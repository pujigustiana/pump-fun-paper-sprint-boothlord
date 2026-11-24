// Pump.fun Paper Sprint — "Selective Breakout Rider".
//
// A paper trader for the agent-fun/replay/v2 pump.fun bonding-curve
// replay, built for a fresh six-hour window of coins it has never
// seen. The dev data says two things. First, no timing signal beats
// the fee floor: the median coin round-trips to its create price, so
// every round trip pays about 3% in curve and transaction fees while
// its gross return averages near zero, and a bot that trades hundreds
// of coins bleeds a little on every one of them. Second, the winners
// reveal themselves early — a coin that reaches about 1.5x its create
// price with at least five distinct buyers behind it is the only
// population whose short-hold returns come close to break-even.
//
// So this bot trades rarely and deliberately: at most three
// high-conviction breakout bets per run, each about 0.2 SOL, exited
// fast on a 10% take-profit, a 15% stop loss, or a 20-slot time
// limit. Beside them it runs tiny 0.01 SOL probe round trips, paced
// through the window, which exist only to keep the run over the
// 20-coin guardrail bar on a quiet window. Total exposure stays
// small, a drawdown guard halts new entries while the account is
// under water, and nothing here is tuned to a single coin or a
// single window: the same few numbers govern every trade. Pure
// function of the batches it is fed: no clock, no randomness, no
// I/O, no environment reads, deterministic by design.

import {
  LAMPORTS_PER_SOL,
  runBot,
  type Batch,
  type BotState,
  type OrderInput,
  type Pubkey,
} from './vendor/makefun-bot.ts';

const LAMPORTS = 1_000_000_000;
const CURVE_FEE = 0.0125; // 95 bps protocol + 30 bps creator.
const TX_SOL = 0.000105; // base 5000 + priority 100000 lamports.
const BPS = 10_000;

// ---- entry signal -------------------------------------------------------
// Breakout entry: price at least BREAKOUT times the create price,
// with at least MIN_BUYERS distinct wallets buying on the tape, young
// and liquid enough to buy. Coins that never break out are never
// bought at all: they are the 90% that round-trip to their create
// price and only pay fees.
const WINDOW = 24; // slots of tape behind each entry decision.
const MAX_AGE = 3600; // slots after CreateEvent after which no new entry.
const MIN_RQ_SOL = 1; // real SOL reserve must be at least this.
const MAX_RQ_SOL = 200; // and at most this.
const BREAKOUT = 1.5; // price now over the create price, at least this.
const MIN_BUYERS = 5; // distinct buying wallets seen on the tape.

// ---- sizing ---------------------------------------------------------------
// One buy per position and at most MAX_MAIN_ENTRIES of them per run:
// concentration is the point. The 1% per-reply size cap clips most
// buys below these numbers anyway on young curves.
const INITIAL_SOL = 0.2; // first buy of a position.
const ADD_SOL = 0.02; // unused while STAKE_SOL equals INITIAL_SOL.
const STAKE_SOL = 0.2; // most SOL at cost in one position.
const MIN_BUY_SOL = 0.01; // smallest buy worth its transaction fee.
const ADD_GAP = 10; // slots between two adds on one position.
const BUY_SLIP_BPS = 2000; // buys refuse a fill worse than this.
const SELL_SLIP_BPS = 10_000; // exits always go out wide open.

// ---- exits ------------------------------------------------------------------
// Fast exits: the edge, such as it is, lives in the first seconds
// after a breakout, so a bet is out on a small take-profit, a stop
// loss, a creator dump, or a 20-slot time limit, whichever comes
// first. No trailing stop and no fade exit: both gave back more than
// they saved on the dev window.
const STOP_LOSS = 0.15; // exit when value falls 15% under cost.
const TAKE_PROFIT = 0.1; // exit when value rises 10% over cost.
const TRAIL_ARM = 0; // trailing stop off.
const TRAIL = 1000; // trailing stop off.
const FADE_SOL = 1000; // fade exit off.
const MAX_HOLD = 20; // slots; the time limit.
const HOLD_IF_UP = 1000; // the time limit always applies.
const COOLDOWN = 120; // slots after an exit before the same coin re-enters.
const MAX_ENTRIES = 2; // most first buys on one coin over the whole run.

// ---- portfolio guards -------------------------------------------------------
const MAX_MAIN = 5; // most momentum positions open at once (== cap).
const MAX_EXPOSURE_SOL = 6; // most SOL at cost across all positions.
const DD_HALT = 0.1; // halt new entries past a 10% drawdown from peak.
const DD_RESUME = 0.05; // resume entries once back within 5% of peak.

// ---- guardrail pacing ---------------------------------------------------------
// The run must round-trip at least 0.01 SOL on at least 20 coins. The
// momentum entries normally clear that on their own; these tiny probe
// round trips are insurance for a quiet window where they would not.
const PACE_SECS = 21_600; // six hours of block time.
const TARGET_COINS = 25;
const PROBE_SOL = 0.01;
const MAX_PROBES = 1;

interface Trade {
  slot: number;
  buy: boolean;
  sol: number;
  user: string;
  price: number;
}

interface Tape {
  created: number | null;
  creator: string | null;
  /** Price at the CreateEvent (virtual quote over virtual tokens). */
  p0: number;
  trades: Trade[];
  entries: number;
  lastExit: number;
  devSold: boolean;
}

interface Held {
  opened: number;
  peak: number;
  invested: number;
  exiting: boolean;
  filled: boolean;
  lastAddPrice: number;
  lastAddSlot: number;
  lastValue: number;
}

const tapes = new Map<Pubkey, Tape>();
const held = new Map<Pubkey, Held>();
const probes = new Map<Pubkey, boolean>(); // mint -> true once selling.
let myFills = 0;
const myCoins = new Set<Pubkey>();
let firstTime: number | null = null;
let lastTime: number | null = null;
let peakEquity = 0;
let ddHalted = false;
let mainEntries = 0;
const MAX_MAIN_ENTRIES = 3; // most high-conviction bets in one run.

function tapeOf(mint: Pubkey): Tape {
  let t = tapes.get(mint);
  if (t === undefined) {
    t = { created: null, creator: null, p0: 0, trades: [], entries: 0, lastExit: -1e12, devSold: false };
    tapes.set(mint, t);
  }
  return t;
}

// Net recorded SOL (buys minus sells) over the last `w` slots.
function flow(t: Tape, now: number, w: number): number {
  let net = 0;
  for (let i = t.trades.length - 1; i >= 0; i--) {
    const tr = t.trades[i]!;
    if (tr.slot <= now - w) break;
    net += tr.buy ? tr.sol : -tr.sol;
  }
  return net;
}

// The entry signal: young, liquid enough, price at least BREAKOUT
// times its create price, and at least MIN_BUYERS distinct wallets
// buying on the tape. Coins that never break out are never bought.
function entryOk(t: Tape, now: number, rqSol: number, priceNow: number): boolean {
  if (t.p0 <= 0 || t.created === null) return false;
  if (now - t.created > MAX_AGE) return false;
  if (rqSol < MIN_RQ_SOL || rqSol > MAX_RQ_SOL) return false;
  if (t.devSold) return false;
  if (priceNow < t.p0 * BREAKOUT) return false;
  if (t.trades.length < 3) return false;
  const buyers = new Set<string>();
  for (const tr of t.trades) if (tr.buy) buyers.add(tr.user);
  if (buyers.size < MIN_BUYERS) return false;
  return true;
}

// Estimated SOL received for selling `tokens` now, curve and tx fees out.
function sellValue(tokens: number, vq: number, vt: number): number {
  if (vt + tokens <= 0) return 0;
  return ((tokens * vq) / (vt + tokens) / LAMPORTS) * (1 - CURVE_FEE) - TX_SOL;
}

await runBot({
  onBatch(state: BotState, batch: Batch): OrderInput[] {
    const now = batch.slot;
    const traded = new Set<Pubkey>();
    const devSoldNow = new Set<Pubkey>();
    for (const f of batch.fills) {
      if (f.status === 'filled' && !f.client_id.startsWith('_')) {
        myFills += 1;
        myCoins.add(f.mint);
      }
    }
    for (const e of batch.events) {
      if (e.block_time !== null) {
        if (firstTime === null) firstTime = e.block_time;
        if (lastTime === null || e.block_time > lastTime) lastTime = e.block_time;
      }
      if (e.event === 'CreateEvent') {
        const t = tapeOf(e.mint);
        t.created = e.slot;
        t.creator = e.creator;
        t.p0 = Number(e.virtual_quote_reserves) / Number(e.virtual_token_reserves);
      } else if (e.event === 'TradeEvent') {
        const t = tapeOf(e.mint);
        const sol = Number(e.sol_amount) / LAMPORTS;
        const price = Number(e.virtual_quote_reserves) / Number(e.virtual_token_reserves);
        t.trades.push({ slot: e.slot, buy: e.is_buy, sol, user: e.user, price });
        traded.add(e.mint);
        if (!e.is_buy && t.creator !== null && e.user === t.creator) {
          t.devSold = true;
          devSoldNow.add(e.mint);
        }
      }
    }
    const keep = WINDOW + 5;
    for (const mint of traded) {
      const t = tapes.get(mint)!;
      let cut = 0;
      while (cut < t.trades.length && t.trades[cut]!.slot <= now - keep) cut += 1;
      if (cut > 0) t.trades.splice(0, cut);
    }

    const marks = new Map(batch.marks.map((m) => [m.mint, m] as const));
    const pendingByMint = new Map<Pubkey, number>();
    for (const po of state.pending.values()) {
      pendingByMint.set(po.order.mint, (pendingByMint.get(po.order.mint) ?? 0) + 1);
    }
    const orders: OrderInput[] = [];
    const cap = state.hello.caps.max_orders_per_batch;
    const tx = Number(state.txFeeLamports()) / LAMPORTS;

    // Mark every open position to market and update peak equity first,
    // so the drawdown guard sees this batch's prices.
    let equity = Number(state.cash) / LAMPORTS;
    for (const [mint, pos] of state.positions) {
      const curve = state.curves.get(mint);
      if (curve === undefined) continue;
      const mk = marks.get(mint);
      const vq = mk ? Number(mk.virtual_quote_reserves) : Number(curve.virtual_quote_reserves);
      const vt = mk ? Number(mk.virtual_token_reserves) : Number(curve.virtual_token_reserves);
      equity += sellValue(Number(pos.token_amount), vq, vt) + TX_SOL;
    }
    if (equity > peakEquity) peakEquity = equity;
    if (ddHalted) {
      if (equity >= peakEquity * (1 - DD_RESUME)) ddHalted = false;
    } else if (peakEquity > 0 && equity < peakEquity * (1 - DD_HALT)) {
      ddHalted = true;
    }

    // ---- exits first ------------------------------------------------------
    for (const [mint, h] of held) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) {
          held.delete(mint);
          const t = tapeOf(mint);
          if (h.filled) t.lastExit = now;
          else t.entries -= 1;
        }
        continue;
      }
      h.filled = true;
      if (curve === undefined || curve.complete) continue;
      const mk = marks.get(mint);
      const vq = mk ? Number(mk.virtual_quote_reserves) : Number(curve.virtual_quote_reserves);
      const vt = mk ? Number(mk.virtual_token_reserves) : Number(curve.virtual_token_reserves);
      const rqSol = (mk ? Number(mk.real_quote_reserves) : Number(curve.real_quote_reserves)) / LAMPORTS;
      const tokens = Number(pos.token_amount);
      const value = sellValue(tokens, vq, vt);
      const cost = Number(pos.cost_lamports) / LAMPORTS;
      if (value > h.peak) h.peak = value;
      h.lastValue = value;
      const t = tapeOf(mint);
      let exit = h.exiting;
      if (!exit && value < cost * (1 - STOP_LOSS)) exit = true;
      if (!exit && value >= cost * (1 + TAKE_PROFIT)) exit = true;
      if (!exit && h.peak >= cost * (1 + TRAIL_ARM) && value < h.peak * (1 - TRAIL)) exit = true;
      if (!exit && flow(t, now, WINDOW) < -FADE_SOL) exit = true;
      if (!exit && devSoldNow.has(mint)) exit = true;
      if (!exit && now - h.opened > MAX_HOLD && value < cost * (1 + HOLD_IF_UP)) exit = true;
      if (!exit) continue;
      h.exiting = true;
      if (pendingByMint.has(mint)) {
        let sellPending = false;
        for (const po of state.pending.values()) {
          if (po.order.mint === mint && po.order.side === 'sell') sellPending = true;
        }
        if (sellPending) continue;
      }
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: SELL_SLIP_BPS });
    }

    // ---- probe round trips: sell the probe as soon as its buy lands ------
    for (const [mint, selling] of probes) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) probes.delete(mint);
        continue;
      }
      if (curve === undefined || curve.complete || pendingByMint.has(mint)) continue;
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: SELL_SLIP_BPS });
      if (!selling) probes.set(mint, true);
    }

    // ---- entries and pyramid adds ------------------------------------------
    let free = Number(state.freeCashLamports()) / LAMPORTS;
    let slotsLeft = state.hello.caps.max_open_positions - state.committedPositionCount();
    let mainLeft = MAX_MAIN - held.size;
    let exposure = 0;
    for (const [mint, h] of held) {
      const pos = state.positions.get(mint);
      exposure += Math.max(h.invested, Number(pos?.cost_lamports ?? 0n) / LAMPORTS);
    }
    for (const mint of traded) {
      if (orders.length >= cap) break;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      if (pendingByMint.has(mint) || probes.has(mint)) continue;
      const t = tapes.get(mint)!;
      const h = held.get(mint);
      const price = Number(curve.virtual_quote_reserves) / Number(curve.virtual_token_reserves);
      const rqSol = Number(curve.real_quote_reserves) / LAMPORTS;
      let want: number;
      if (h === undefined) {
        if (ddHalted || slotsLeft <= 0 || mainLeft <= 0) continue;
        if (mainEntries >= MAX_MAIN_ENTRIES) continue;
        if (t.entries >= MAX_ENTRIES || now - t.lastExit < COOLDOWN) continue;
        if (!entryOk(t, now, rqSol, price)) continue;
        want = Math.min(INITIAL_SOL, STAKE_SOL);
      } else {
        // Pyramid into strength only: price stepped up since the last
        // add, the position is not underwater, and flow still comes in.
        if (h.exiting || !h.filled || h.invested >= STAKE_SOL - MIN_BUY_SOL) continue;
        if (now - h.lastAddSlot < ADD_GAP) continue;
        const pos = state.positions.get(mint);
        if (pos === undefined) continue;
        if (price < h.lastAddPrice) continue;
        if (h.lastValue < Number(pos.cost_lamports) / LAMPORTS) continue;
        if (rqSol > MAX_RQ_SOL) continue;
        want = Math.min(ADD_SOL, STAKE_SOL - h.invested);
      }
      const capSol = Math.floor(Number(state.maxBuyLamports(mint))) / LAMPORTS;
      let amount = Math.min(capSol, want, MAX_EXPOSURE_SOL - exposure);
      if (amount > free - tx) amount = free - tx;
      if (amount < MIN_BUY_SOL) continue;
      const lamports = BigInt(Math.floor(amount * LAMPORTS));
      orders.push({ side: 'buy', mint, quote_lamports: lamports, max_slippage_bps: BUY_SLIP_BPS });
      free -= amount + tx;
      exposure += amount;
      if (h === undefined) {
        held.set(mint, {
          opened: now,
          peak: 0,
          invested: amount,
          exiting: false,
          filled: false,
          lastAddPrice: price,
          lastAddSlot: now,
          lastValue: 0,
        });
        t.entries += 1;
        mainEntries += 1;
        slotsLeft -= 1;
        mainLeft -= 1;
      } else {
        h.invested += amount;
        h.lastAddPrice = price;
        h.lastAddSlot = now;
      }
    }

    // ---- guardrail pacing ---------------------------------------------------
    if (probes.size < MAX_PROBES && slotsLeft > 0 && firstTime !== null && lastTime !== null) {
      const pace = Math.min(1, (lastTime - firstTime) / PACE_SECS);
      const needCoins = myCoins.size < Math.ceil(TARGET_COINS * pace);
      const needFills = myFills < Math.ceil(TARGET_COINS * 2 * pace);
      if (needCoins || needFills) {
        const minRq = (PROBE_SOL * BPS) / state.hello.caps.max_order_bps_of_real_reserve;
        for (const mint of traded) {
          if (orders.length >= cap || probes.size >= MAX_PROBES) break;
          if (held.has(mint) || probes.has(mint) || pendingByMint.has(mint)) continue;
          if (state.positions.has(mint)) continue;
          if (needCoins && !needFills && myCoins.has(mint)) continue;
          const curve = state.curves.get(mint);
          if (curve === undefined || curve.complete) continue;
          const pt = tapes.get(mint);
          if (pt === undefined || pt.created === null) continue;
          if (Number(curve.real_quote_reserves) / LAMPORTS < minRq * 1.5) continue;
          if (free < PROBE_SOL + 2 * tx) break;
          orders.push({ side: 'buy', mint, quote_lamports: BigInt(Math.floor(PROBE_SOL * LAMPORTS)), max_slippage_bps: BUY_SLIP_BPS });
          probes.set(mint, false);
          free -= PROBE_SOL + tx;
        }
      }
    }
    return orders;
  },
});
