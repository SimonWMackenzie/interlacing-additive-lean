import EthInapproximability.ParameterizedNP.TruthTableExponent

/-!
# Parameterized NP route: the approximation allowance `alpha` (`eq:alpha-definition`)

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`ETH-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`, line 135),
"Pointwise-maximal plateau-safe integral allowance for the fixed midpoint
decoder, binder order, and subexponential contradiction", recorded there as
human **proved** / Lean **pending**.  This module lands the *allowance itself*
-- the plateau search `p`, the function `alpha`, its growth, the gap fit
`eq:alpha-gap-fit`, and the frozen pointwise-maximality calculation -- and
nothing downstream of it.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

## Provenance

* **Autoformalization anchors (proof source).**  All in
  `sections/14-final-consequence.tex`, subsection *Binder order and the
  approximation function* (line 2264).
  * Frozen lines 2293--2295: "The resulting sequence `T_n` is nondecreasing and
    tends to infinity, although it may have finite plateaux.  Set
    `alpha(0)=0`.  For every `T >= 1`, define".
  * `eq:alpha-definition` (label line 2301, display lines 2296--2302):
    `p(T) = min{n >= 1 : T_n >= T}`,
    `alpha(T) = max{0, floor((L(p(T))-1)/2)}`.
  * Frozen line 2303: "The subtraction and floor in this display are taken in
    the integers."  Frozen lines 2304--2309 give the equivalent form
    `alpha(T) = Nat.div (Nat.sub (L(p(T)), 1), 2)` with truncated subtraction;
    that is the spelling landed here, and `integerDisplay_agrees` proves the
    two frozen displays are the same number.
  * Frozen lines 2310--2311: "Because `T_n >= (n+2)^2`, the search for `p(T)`
    stops by `ceil(sqrt T)`."
  * Frozen lines 2311--2313: "The functions `p, L`, and `alpha` are total,
    computable, and nondecreasing; since `L(n) -> infinity`, also
    `alpha(T) -> infinity`."
  * Frozen lines 2315--2317: "At an attained length `T_n`, the value `p(T_n)`
    is the first index of its plateau.  Hence `p(T_n) <= n`,
    `L(p(T_n)) <= L(n)`".
  * `eq:alpha-gap-fit` (label line 2320, display lines 2318--2321):
    `2 alpha(T_n) < L(n)` for all `n` with `L(n) >= 1`, proved at frozen lines
    2322--2330.
  * Frozen lines 2331--2335, the exactness half: "For every integer `r >= 1`,
    this choice is also exact: if a nonnegative integer `A` satisfies
    `2A < r`, then `2A <= r-1`, and hence `A <= floor((r-1)/2)`."
  * Frozen lines 2336--2340, the scope sentence bounding what maximality
    means (see GAP-EXPOSED 5).
  * `eq:L-clock` (`sections/12-iteration-specification.tex`, label line 486)
    fixes `L(n) = max({0} union {k : V_k <= n})`, already transcribed as the
    banked `PaddingAndClock.slowIndex`.
  * `eq:common-size` (`sections/12-iteration-specification.tex`, label line
    628) fixes `T_n`, already transcribed as the banked
    `PaddingAndClock.tCommon`.
  * `conv:finite-slots` (`sections/02-mechanical-contract.tex`) fixes the
    zero-based reading of every finite index set; no finite carrier is
    introduced or re-indexed in this module.

* **Banked endpoints, all grep-verified present in
  `src/EthInapproximability/ParameterizedNP/` before use.**
  *Actually consumed:*
  * from `TruthTableExponent.lean` (tranche `cc-t1v`): **`truthTable_ge`**
    (`T_n >= (n+2)^2`, the frozen termination input at line 2310),
    **`truthTable_monotone`** (the frozen "nondecreasing" of line 2293) and
    **`truthTable_unbounded`** (the frozen "tends to infinity" of line 2293),
    which together make the search set of `p` nonempty at every `T`;
  * from `PaddingAndClock.lean` (tranche `cc-t1t-r1`): **`slowIndex`**
    (the frozen `L`), **`slowIndex_le_and_spec`** (used only for
    `L(0) = 0`), **`slowDiagonal_monotone_unbounded`** (the frozen "`L` is
    nondecreasing" and "for every fixed `K`, all `n >= V_K` satisfy
    `K <= L(n)`"), **`SlowClockGateSet`**, **`witnessClock`**,
    **`witnessClock_gates`** and **`witnessClock_reaches_positive_index`**
    (Part 5's non-vacuity only), and the definition **`tCommon`**.

  *Verified present but deliberately **not** consumed:* `commonSquare_ge`
  (`S_n >= n+2`) and `truthTableExponent_unbounded`.  The frozen justification
  of the search bound at line 2310 is stated from `T_n >= (n+2)^2`, not from
  the side length, and the frozen unboundedness of `alpha` runs through
  `L(n) -> infinity`, not through the exponent; routing either through the
  side length would be a fabricated dependence rather than a trace.

* **Imports.**  `EthInapproximability.ParameterizedNP.TruthTableExponent` and,
  through it, `CommonPadding`, `PaddingAndClock`, `SizePropagation`,
  `IterationAssembly` and `EthInapproximability.Prelude`, hence
  `LegacyNPCC.Core` (project-axiom-free) and `LegacyNPCC.Bridge`.
  `LegacyNPCC.Stage12` is **not** imported, so the cited AGHP balanced-family
  axiom stays outside this module's closure and no ledger note for it is
  needed.  No new import is added.

* **Proof status.**  Every declaration below is **new**.  Nothing is
  inherited, nothing is ported, and nothing is transcribed from
  `C:/lean/npc-cc/EthProof`, which traced the older fixed-width manuscript and
  is not a trace or style source here.

## What this module lands

1. **The plateau search `p`** (frozen line 2297).  `alphaSearch_exists` is the
   frozen search set at a guard `n >= 1`, proved nonempty from the banked
   `truthTable_unbounded` -- *never* from a new assumption.  `pIndex` is its
   minimum, and `pIndex_pos`, `pIndex_spec`, `pIndex_le_of` are its three
   defining properties.
2. **The frozen termination bound** (frozen lines 2310--2311), twice:
   `pIndex_le_of_square` in the general form the frozen sentence actually
   argues (`T <= (n+2)^2` at any legal `n` already stops the search), and
   `pIndex_le_sqrt` at the frozen witness.
3. **The allowance `alpha`** (frozen display 2296--2302, in the frozen
   natural-number spelling of lines 2304--2309), as `alphaAllowance`, with
   the frozen `alpha(0) = 0` branch (`alpha_zero`) separated from the
   `T >= 1` clause (`alpha_eq`), and `integerDisplay_agrees` reconciling the
   integer-floor display of line 2300 with the `Nat.div`/`Nat.sub` display of
   lines 2306--2307.
4. **`p` and `alpha` are nondecreasing** (frozen line 2311), as
   `pIndex_monotone` and `alpha_monotone`.
5. **`alpha` is unbounded** (frozen lines 2312--2313), as `alpha_unbounded`,
   in the finite existential form -- the limit form is GAP-EXPOSED 3.
6. **The plateau facts** (frozen lines 2315--2316): `pIndex_of_attained`
   (`p(T_n) <= n`) and `pIndex_plateau_first` ("the first index of its
   plateau").
7. **`eq:alpha-gap-fit`** (frozen display 2318--2321) as `alphaGapFit`,
   proved by the frozen two-case argument of lines 2322--2330.
8. **Frozen pointwise exactness** (lines 2331--2335) as
   `allowance_pointwise_maximal`, with its converse `allowance_plateau_safe`
   (lines 2325--2329) and the combined `allowance_exactness`.
9. **Non-vacuity** (Part 5).  Every hypothesis bundle below is inhabited at a
   legal gate-satisfying clock -- `PaddingAndClock.witnessClock`, whose four
   frozen gates are banked as `witnessClock_gates` -- and `alphaGapFit_fires`
   exhibits the conclusion of the module's one conditional deliverable at
   those legal values.

## Reader counterparts

The reader counterparts are in
`routes/parameterized-np/reader-facing/sections/06-eth.tex`.  **That file was
opened first-hand this tranche and the cited display read to confirm it states
the same fact.**

This tranche's reader anchor is `eq:paper-alpha` (label line 358, display
lines 353--359) and *nothing else*.  It is **split by clause, and no clause is
assigned twice**:

* the clause `p(T) = min{n >= 1 : T_n >= T}` (display line 354) to `pIndex`;
* the clause `alpha(T) = max{0, floor((L(p(T))-1)/2)}` (display lines
  356--357) to `alphaAllowance`.

**No already-assigned reader line is re-claimed.**  In particular
`CLOCK-001` already owns lines 281, 283, 284, 288, 298--302, 304, 317, 318,
319, 322, 325--329, 330, 332--333, 333--334, `eq:paper-padding-invariance`
(label 338), line 340 (both clauses), `eq:paper-table-subexponential` (label
344, both clauses), line 351 (both clauses) and line 360; none of those is
touched here.

**Deliberately not claimed by this tranche** (available to a later one, and
recorded so that the correspondence is visible rather than hidden): reader
lines 360--363 ("Both `p` and `L` are nondecreasing, so `alpha` is total,
computable, and nondecreasing.  Since `p(T) -> infinity` and
`L(n) -> infinity`, it is also unbounded") and `eq:paper-alpha-fits-gap`
(label line 370, display lines 368--371), whose autoformalization
counterparts *are* landed here as `pIndex_monotone`, `alpha_monotone`,
`alpha_unbounded` and `alphaGapFit`.  This tranche's reader-anchor
instruction restricts the claim to `eq:paper-alpha`, so these items remain
formally unassigned; they are not being claimed silently and they are not
being denied.

**Claiming no reader item** (autoformalization-only content, or content the
reader states only inside an item claimed elsewhere): `alphaSearch_exists`,
`pIndex_pos`, `pIndex_spec`, `pIndex_le_of`, `pIndex_le_of_square`,
`pIndex_le_sqrt`, `pIndex_of_attained`, `pIndex_plateau_first`,
`pIndex_at_first_length`, `pIndex_interior`, `truthTable_mono`, `alpha_zero`,
`alpha_eq`, `integerDisplay_agrees`, `allowance_plateau_safe`,
`allowance_pointwise_maximal`, `allowance_exactness`, and every declaration of
Parts 5 and 6.

## Mechanical-contract compliance (`M1`--`M10`, frozen Section 2)

* `M2`/`M4`: **this module introduces no structure at all**, so no constructor
  can carry a conclusion.  Its conditional deliverables (`alpha_monotone`,
  `alpha_unbounded`, `alphaGapFit`) take the frozen clock gates as the
  **explicit binder** `hg : SlowClockGateSet V nstep` -- the banked frozen
  bundle, not a new one -- plus, for `alphaGapFit`, the frozen side condition
  `1 <= L(n)` as a second explicit binder.  Neither binder restates a derived
  telescope: `SlowClockGateSet` is the frozen `V_k` gate list of
  `13-iteration-assembly.tex:653,672--676`, and `1 <= L(n)` is the frozen
  guard printed in the text at line 2317.
* `M7`: no carrier is introduced here.  The nonemptiness fact that this module
  *does* need -- that the frozen search set `{n >= 1 : T_n >= T}` is inhabited
  -- is proved (`alphaSearch_exists`) from the banked `truthTable_unbounded`
  and is never posited.
* `M9`: no ceiling is introduced.  The frozen `ceil(sqrt T)` of line 2310 is a
  *bound on the search*, not a definitional rounding, and it is landed as an
  inequality (`pIndex_le_sqrt`); the only rounding in the definition is the
  frozen truncated `Nat.sub`/`Nat.div` pair of lines 2306--2307, spelled
  exactly.
* **Binder order** (`M3`, and frozen lines 2266--2291).  The frozen text fixes
  B1--B6 and says "Only after B1--B6 are fixed are the functions `L, g, e,
  T_n` [...] instantiated".  Here the clock `V` is the *first* binder of every
  declaration and `p`, `alpha` are functions of it; nothing in this module is
  defined before the datum it depends on, and no statement quantifies over `T`
  before `V`.  B1--B6 themselves are not modelled (GAP-EXPOSED 1).
* Zero-based slots (`conv:finite-slots`) are untouched: no finite index type
  occurs in this module.
* Both interlace widths `q` and `Q` are untouched: the allowance is defined
  strictly after the last level and after final padding, so no interlace
  appears here and none is renamed or re-derived.
* Selector costs and the midpoint decoder are untouched (GAP-EXPOSED 1).

## GAP-EXPOSED (what this module deliberately does not claim)

1. **The binder-order data B1--B6 and the whole machine layer are out of
   scope, explicitly.**  Nothing here models `M_*`, `delta_ETH`,
   `epsilon_*`, the S1--S2 package, `thm:eff-ledger`, `A_cert`, `A_raw`,
   `thm:effective-materialization`, the midpoint decoder,
   `PolyApprox_M(alpha)`, `lem:literal-final-runtime`, `thm:effective-main`
   or `thm:main`.  `alpha` is landed as a function of the clock `V` alone,
   which is exactly what the frozen text instantiates *after* B1--B6.
2. **Computability is not claimed.**  Frozen line 2311 says `p, L, alpha` are
   "total, computable, and nondecreasing".  *Totality* is the Lean typing
   `alphaAllowance V : ℕ → ℕ` (a total function by construction, its search
   discharged by `alphaSearch_exists`), and *nondecreasing* is landed.
   *Computable* is *not*: this module is `noncomputable`, because the banked
   `tCommon` is, and no machine model or complexity claim about `p` or `alpha`
   is made anywhere below.
3. **Every limit form is GAP-EXPOSED.**  `alpha(T) -> infinity`,
   `p(T) -> infinity` and `L(n) -> infinity` as statements about a filter do
   not appear.  What is landed is the finite existential form
   (`alpha_unbounded`), exactly as the banked `truthTable_unbounded` and
   `slowDiagonal_monotone_unbounded` are.  No `Filter.Tendsto` and no
   asymptotic order relation occurs in this module.
4. **The clock is still a parameter.**  `L` is the banked `slowIndex` of an
   arbitrary `V`, and the frozen tie of `V_k` to the compiler's running time
   `tau_k` is not modelled (this is `PaddingAndClock`'s GAP-EXPOSED 2,
   inherited unchanged).  Hence `alpha_monotone`, `alpha_unbounded` and
   `alphaGapFit` are conditional on `SlowClockGateSet`, which Part 5 inhabits.
5. **Maximality is claimed exactly at the frozen certification datum.**
   `allowance_pointwise_maximal` is frozen lines 2331--2335 verbatim: among
   nonnegative integers `A` whose plateau safety is certified by
   `2A < r` with `r = L(p(T_n))`, the frozen value is largest.  Frozen lines
   2336--2340 restrict this to "a maximal rounding under that fixed contract,
   not a claim of any named lower asymptotic rate for `L`", and **nothing
   below claims more**: there is no statement about allowances certified by
   other means, none about the unbounded tail as a limit, and none about the
   growth rate of `L`.
6. **Nothing is claimed about the promise case or the contradiction.**  The
   `2 alpha(T_n) < L(n)` fit is landed as an arithmetic fact about the two
   frozen functions; its use against `eq:k-level-gap` at frozen lines
   2637--2650 is `ETH-001`'s remaining content and is untouched.
7. **No route completion is claimed.**  The headline theorem of the route is
   not in Lean.

## Reading notes

* **N1 (why the guard `n >= 1` is definitional, not cosmetic).**  Frozen line
  2297 writes `min{n >= 1 : T_n >= T}`.  Dropping the guard changes the
  function: at `T = 0` the unguarded minimum is `0`, and
  `unguardedSearch_violates_the_frozen_lower_index` records that difference in
  the kernel.  The guard is also what makes "`p(T_n)` is the first index of
  its plateau" a statement about a positive index.
* **N2 (why `alpha(0)` needs its own branch).**  Frozen line 2294 *sets*
  `alpha(0) = 0` and only then defines the display "for every `T >= 1`", so
  the branch is frozen and is transcribed as an `if`.  It is not redundant
  bookkeeping: the general formula at `T = 0` would read `(L(p(0)) - 1)/2`,
  and the definition would then depend on `L(1)` rather than on the frozen
  stipulation.
* **N3 (`floor` over the integers versus `Nat.div` over the naturals).**  The
  frozen display at line 2300 takes the subtraction and the floor in `ℤ` and
  then caps at `0`; lines 2304--2309 give the `ℕ` spelling with truncated
  subtraction.  `integerDisplay_agrees` proves these are equal at every `r`,
  including the `r = 0` corner where the `ℤ` reading passes through a negative
  quotient.  The `ℕ` spelling is landed because frozen line 510 of the same
  section types the consumer's allowance as a function `ℕ -> ℕ`.
* **N4 (the "first index of the plateau" is minimality, not a new fact).**
  Frozen line 2315 names it; in Lean it is `Nat.find`'s minimality applied to
  the attained value, which is why `pIndex_of_attained` and
  `pIndex_plateau_first` have one-line proofs and introduce no hypothesis.

## Candidate encodings and ranking (NOVEL-concept protocol)

Two encodings of the plateau search were written and run against the same
aux-lemma battery before landing.

* **Candidate A (landed).**  `p(T) = Nat.find` of the **guarded** predicate
  `fun n => 1 <= n ∧ T <= T_n`, nonemptiness from the banked
  `truthTable_unbounded` pushed up to a positive index; `alpha` valued in `ℕ`
  with the frozen `alpha(0) = 0` branch.
* **Candidate B (rejected).**  `p(T) = Nat.find (truthTable_unbounded V T)`,
  i.e. the **unguarded** minimum `min{n : T_n >= T}`, reusing the banked
  existential directly with no extra work.

Ranking.  Battery (the five general lemmas marked **Aux 1**--**Aux 5**
below): A proved 5/5.  B proved 4/5 and is **disqualified on Aux 2**: the
frozen lower guard `p(T) >= 1` of line 2297 is *false* for B, and
`unguardedSearch_violates_the_frozen_lower_index` proves in the kernel that
B's search returns `0` at `T = 0` while A's returns a positive index.  That is
not a cosmetic difference: `p(T_n) <= n` and "the first index of its plateau"
(frozen line 2315) are statements about the guarded minimum, and every
downstream use of `L(p(T))` reads `L` at an index the frozen text guarantees
to be at least `1`.  Faithfulness: A transcribes line 2297 symbol for symbol,
including the guard; B silently changes the definition.  Length: B is shorter
by one lemma (`alphaSearch_exists`) and loses a frozen hypothesis, which is
the wrong trade.  Candidate A wins on all three axes and is landed, and B's
only genuine content -- that the banked existential is what makes the search
terminate -- survives inside `alphaSearch_exists`, which consumes exactly that
banked statement.

## Statement poles

* `alphaSearch_exists` and `alpha_unbounded` are the module's two existential
  deliverables.
  * For `alphaSearch_exists` the trivial witness `n = 0` fails outright:
    `zeroIndexIsNotAWitness` shows the frozen guard `1 <= n` rejects it at
    every `T` and every clock, so the existential is genuinely a search over
    positive indices and not a restatement of `truthTable_unbounded`.
  * For `alpha_unbounded` no *fixed* threshold `T` works:
    `unboundedness_has_no_uniform_threshold` exhibits, for every `T`, a bound
    `B` that `alpha(T)` fails.  The existential is therefore genuinely over
    `T`, which is what "`alpha(T) -> infinity`" means at frozen line 2313.
* `alphaGapFit` is the module's conditional deliverable, and its pole is
  vacuity on two counts.  Its hypothesis bundle is inhabited
  (`alphaGapFit_fires` supplies a legal gate-satisfying clock *and* a source
  size at which the frozen guard `1 <= L(n)` holds, and states the conclusion
  there), and its conclusion is not `0 < L(n)` in disguise: the frozen strict
  inequality is exact by `allowance_pointwise_maximal`, so no larger allowance
  satisfies it.
* `allowance_pointwise_maximal` is an upper bound on an arbitrary `A`, so it
  has no trivial witness at all; `allowance_exactness` records that it is an
  equivalence and therefore cannot be weakened without becoming false.
-/

namespace EthInapproximability.ParameterizedNP.AlphaAllowance

open EthInapproximability.ParameterizedNP.PaddingAndClock
open EthInapproximability.ParameterizedNP.TruthTableExponent

/-! ## Part 1: the frozen search set and its minimum (`eq:alpha-definition`) -/

/-- **Aux 1 (the truth-table length is monotone as a function, not merely
step-by-step).**

The banked `truthTable_monotone` is the unit step of frozen line 2293, "the
resulting sequence `T_n` is nondecreasing"; the search of line 2297 needs it at
arbitrary gaps.  General in the clock and both indices.  Claims no reader item
-- the reader's line 351 is `truthTable_monotone`'s item and is not
re-claimed. -/
theorem truthTable_mono (V : ℕ → ℕ) : Monotone (tCommon V) :=
  monotone_nat_of_le_succ (truthTable_monotone V)

/-- **Aux 2 (the frozen search set is inhabited at a positive index).**

Frozen line 2297: `p(T) = min{n >= 1 : T_n >= T}`.  The minimum exists because
the banked `truthTable_unbounded` -- frozen line 2293's "tends to infinity",
landed in tranche `cc-t1v` -- supplies *some* index at which the length passes
`T`, and Aux 1 pushes that index up past the frozen guard `n >= 1`.  This is
the only nonemptiness fact the module needs, and it is **proved, never
posited** (`M7`).

Statement pole: the trivial witness `n = 0` is rejected by the frozen guard at
every `T` and every clock, which is `zeroIndexIsNotAWitness`.  General in the
clock and the threshold. -/
theorem alphaSearch_exists (V : ℕ → ℕ) (T : ℕ) : ∃ n, 1 ≤ n ∧ T ≤ tCommon V n := by
  obtain ⟨n, hn⟩ := truthTable_unbounded V T
  exact ⟨max n 1, le_max_right _ _, hn.trans (truthTable_mono V (le_max_left _ _))⟩

/-- **`p(T) = min{n >= 1 : T_n >= T}`** -- `eq:alpha-definition`
(`14-final-consequence.tex`, label line 2301, display line 2297).

`Nat.find` on the guarded predicate is exactly the frozen minimum: `pIndex_pos`
and `pIndex_spec` are its membership in the frozen search set, and
`pIndex_le_of` is its minimality.  Dropping the guard would change the function
(reading note N1), which `unguardedSearch_violates_the_frozen_lower_index`
records in the kernel.

`noncomputable` because the banked `tCommon` is; no computability claim is made
about `p` (GAP-EXPOSED 2).

Reader counterpart: the `p(T) = min{n >= 1 : T_n >= T}` clause of
`eq:paper-alpha` (`06-eth.tex`, label line 358, display line 354).  The
`alpha` clause of the same display is `alphaAllowance`'s item and is not
re-claimed. -/
noncomputable def pIndex (V : ℕ → ℕ) (T : ℕ) : ℕ := Nat.find (alphaSearch_exists V T)

/-- The frozen lower guard `p(T) >= 1` of line 2297.  General in the clock and
the threshold.  Claims no reader item. -/
theorem pIndex_pos (V : ℕ → ℕ) (T : ℕ) : 1 ≤ pIndex V T :=
  (Nat.find_spec (alphaSearch_exists V T)).1

/-- The frozen membership `T_{p(T)} >= T` of line 2297.  General in the clock
and the threshold.  Claims no reader item. -/
theorem pIndex_spec (V : ℕ → ℕ) (T : ℕ) : T ≤ tCommon V (pIndex V T) :=
  (Nat.find_spec (alphaSearch_exists V T)).2

/-- The frozen minimality of line 2297: every legal index of the search set
bounds `p(T)`.  General in the clock, the threshold and the competitor index.
Claims no reader item. -/
theorem pIndex_le_of (V : ℕ → ℕ) {T n : ℕ} (hn : 1 ≤ n) (h : T ≤ tCommon V n) :
    pIndex V T ≤ n :=
  Nat.find_le ⟨hn, h⟩

/-- **Aux 3 (`p` is nondecreasing)** -- the first half of frozen line 2311,
"The functions `p, L`, and `alpha` are [...] nondecreasing".

A larger threshold has a smaller search set, so its minimum is at least as
large.  General in the clock.  Claims no reader item: the reader states this at
line 360--361, which this tranche does not claim (see "Reader counterparts"). -/
theorem pIndex_monotone (V : ℕ → ℕ) : Monotone (pIndex V) := by
  intro T T' h
  exact pIndex_le_of V (pIndex_pos V T') (h.trans (pIndex_spec V T'))

/-! ## Part 2: the frozen termination bound (lines 2310--2311) -/

/-- **The frozen search bound, in the general form the frozen sentence argues.**

Frozen lines 2310--2311: "Because `T_n >= (n+2)^2`, the search for `p(T)` stops
by `ceil(sqrt T)`."  The reason is exactly this: any legal index whose square
bound already covers `T` stops the search, through the banked
`truthTable_ge`.  General in the clock, the threshold and the index.  Claims no
reader item -- the reader's line 360 is `truthTable_ge`'s item. -/
theorem pIndex_le_of_square (V : ℕ → ℕ) {T n : ℕ} (hn : 1 ≤ n) (h : T ≤ (n + 2) ^ 2) :
    pIndex V T ≤ n :=
  pIndex_le_of V hn (h.trans (truthTable_ge V n))

/-- **The frozen search bound at the frozen witness** (lines 2310--2311).

`Nat.sqrt T <= ceil(sqrt T)`, so this is the frozen bound in the integer-floor
spelling, tightened only by the frozen guard `n >= 1` that forces the `max`.
General in the clock and the threshold.  Claims no reader item. -/
theorem pIndex_le_sqrt (V : ℕ → ℕ) (T : ℕ) : pIndex V T ≤ max (Nat.sqrt T) 1 := by
  have hle : Nat.sqrt T ≤ max (Nat.sqrt T) 1 := le_max_left _ _
  have hone : 1 ≤ max (Nat.sqrt T) 1 := le_max_right _ _
  have h2 : T < (Nat.sqrt T + 1) * (Nat.sqrt T + 1) := Nat.lt_succ_sqrt T
  have h3 : (Nat.sqrt T + 1) * (Nat.sqrt T + 1)
      ≤ (max (Nat.sqrt T) 1 + 2) * (max (Nat.sqrt T) 1 + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  refine pIndex_le_of_square V hone ?_
  have h4 : T ≤ (max (Nat.sqrt T) 1 + 2) * (max (Nat.sqrt T) 1 + 2) := by omega
  simpa [pow_two] using h4

/-! ## Part 3: plateaux (frozen lines 2315--2316) -/

/-- **`p(T_n) <= n`** -- frozen line 2316, at an attained length.

General in the clock and the source size.  Claims no reader item: the reader
states it at line 366, which this tranche does not claim. -/
theorem pIndex_of_attained (V : ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n) :
    pIndex V (tCommon V n) ≤ n :=
  pIndex_le_of V hn (le_refl _)

/-- **"`p(T_n)` is the first index of its plateau"** -- frozen line 2315.

If any legal index `m` carries the same length, the search stops at or before
it; on a plateau `m <= n` that is the frozen "first index" statement.  This is
minimality read on a plateau and introduces no new hypothesis (reading note
N4); the frozen `m <= n` is not needed for the bound and is therefore not
restated as a binder.  General in the clock and both indices.  Claims no reader
item. -/
theorem pIndex_plateau_first (V : ℕ → ℕ) {m n : ℕ} (hm : 1 ≤ m)
    (h : tCommon V n = tCommon V m) : pIndex V (tCommon V n) ≤ m :=
  pIndex_le_of V hm (le_of_eq h)

/-- The search is attained at the frozen first legal index when the threshold
is already met there.  General in the clock.  Claims no reader item. -/
theorem pIndex_at_first_length (V : ℕ → ℕ) : pIndex V (tCommon V 1) = 1 := by
  have h1 := pIndex_pos V (tCommon V 1)
  have h2 := pIndex_of_attained V (n := 1) (le_refl 1)
  omega

/-- **Interior-threshold witness: the frozen minimum is not always the guard.**

At a threshold one above an attained length the search cannot stop at the first
legal index, so `p` genuinely ranges beyond `1` and `pIndex_at_first_length` is
not the whole story.  Together with `pIndex_at_first_length` this shows both
regimes of the frozen search are live.  General in the clock.  Claims no reader
item. -/
theorem pIndex_interior (V : ℕ → ℕ) : 1 < pIndex V (tCommon V 1 + 1) := by
  have h1 := pIndex_pos V (tCommon V 1 + 1)
  have h2 := pIndex_spec V (tCommon V 1 + 1)
  by_contra hcon
  have heq : pIndex V (tCommon V 1 + 1) = 1 := by omega
  rw [heq] at h2
  omega

/-! ## Part 4: the allowance itself (`eq:alpha-definition`) -/

/-- **`alpha`, the approximation allowance** -- `eq:alpha-definition`
(`14-final-consequence.tex`, label line 2301, display lines 2296--2302), in the
frozen natural-number spelling of lines 2304--2309,
`alpha(T) = Nat.div (Nat.sub (L(p(T)), 1), 2)`.

The `T = 0` branch is the frozen stipulation of line 2294, "Set
`alpha(0) = 0`", which precedes the display and is not derivable from it
(reading note N2).  `L` is the banked `PaddingAndClock.slowIndex` of
`eq:L-clock`.  `integerDisplay_agrees` proves this `ℕ` spelling equals the
integer-floor display of line 2300 at every value, including `r = 0`.

Totality is the typing `ℕ → ℕ`; computability is **not** claimed
(GAP-EXPOSED 2), and the definition is `noncomputable` because the banked
`tCommon` inside `pIndex` is.

Reader counterpart: the `alpha(T) = max{0, floor((L(p(T))-1)/2)}` clause of
`eq:paper-alpha` (`06-eth.tex`, label line 358, display lines 356--357).  The
`p` clause of the same display is `pIndex`'s item and is not re-claimed. -/
noncomputable def alphaAllowance (V : ℕ → ℕ) (T : ℕ) : ℕ :=
  if T = 0 then 0 else (slowIndex V (pIndex V T) - 1) / 2

/-- Frozen line 2294, "Set `alpha(0) = 0`".  General in the clock.  Claims no
reader item -- the reader's `alpha(0) = 0` is inside `eq:paper-alpha`'s
`alpha` clause, already assigned to `alphaAllowance`. -/
theorem alpha_zero (V : ℕ → ℕ) : alphaAllowance V 0 = 0 := by
  simp [alphaAllowance]

/-- The frozen display on its stated range, "for every `T >= 1`" (line 2295).
General in the clock and the threshold.  Claims no reader item. -/
theorem alpha_eq (V : ℕ → ℕ) {T : ℕ} (hT : 1 ≤ T) :
    alphaAllowance V T = (slowIndex V (pIndex V T) - 1) / 2 := by
  simp only [alphaAllowance, if_neg (show T ≠ 0 by omega)]

/-- **Aux 4 (the two frozen displays are the same number).**

Frozen line 2300 writes `max{0, floor((L(p(T))-1)/2)}` with "the subtraction
and floor in this display [...] taken in the integers" (line 2303); frozen
lines 2304--2309 give `Nat.div (Nat.sub (L(p(T)), 1), 2)` with truncated
subtraction.  This is that reconciliation, stated for an arbitrary `r` and in
particular at the corner `r = 0`, where the integer reading passes through a
negative quotient before the `max` caps it.

General in `r`; no clock, no threshold, no hypothesis.  Claims no reader item.
The `ℕ` spelling is the landed one because frozen line 510 of the same section
types the consumer's allowance as `ℕ -> ℕ` (reading note N3). -/
theorem integerDisplay_agrees (r : ℕ) :
    ((r - 1) / 2 : ℕ) = (max 0 (((r : ℤ) - 1) / 2)).toNat := by
  cases r with
  | zero => decide
  | succ m =>
    have h1 : ((m + 1 : ℕ) : ℤ) - 1 = ((m : ℕ) : ℤ) := by push_cast; ring
    rw [h1, max_eq_right (show (0 : ℤ) ≤ (m : ℤ) / 2 by omega)]
    omega

/-! ## Part 5: growth, the gap fit, and frozen exactness -/

/-- **Aux 5 (the frozen rounding is plateau-safe)** -- frozen lines 2325--2329,
`2 floor((r-1)/2) <= r-1 < r`.

General in `r`; the frozen guard `r >= 1` is the one printed at line 2331.
Claims no reader item. -/
theorem allowance_plateau_safe {r : ℕ} (hr : 1 ≤ r) : 2 * ((r - 1) / 2) < r := by
  omega

/-- **Frozen pointwise exactness** -- lines 2331--2335: "if a nonnegative
integer `A` satisfies `2A < r`, then `2A <= r-1`, and hence
`A <= floor((r-1)/2)`."

The frozen guard `r >= 1` is implied by `2A < r` and is therefore not restated
as a hypothesis.  This is an upper bound on an arbitrary `A`, so it has no
trivial witness.  General in `A` and `r`.  Claims no reader item. -/
theorem allowance_pointwise_maximal {A r : ℕ} (h : 2 * A < r) : A ≤ (r - 1) / 2 := by
  omega

/-- The two frozen directions together: at the frozen certification datum `r`,
`floor((r-1)/2)` is exactly the largest plateau-safe allowance.  This is what
frozen line 2336 calls pointwise maximality, and GAP-EXPOSED 5 bounds what it
means.  General in `A` and `r`.  Claims no reader item. -/
theorem allowance_exactness {A r : ℕ} (hr : 1 ≤ r) : A ≤ (r - 1) / 2 ↔ 2 * A < r := by
  omega

/-- **`alpha` is nondecreasing** -- frozen line 2311.

Both frozen inputs are nondecreasing: `p` by `pIndex_monotone`, and `L` by the
banked `slowDiagonal_monotone_unbounded`, whose frozen clock gates enter as the
explicit binder `hg`.  The `T = 0` case is the frozen stipulation of line 2294.
General in the clock, the cutoff function and both thresholds.  Claims no
reader item (see "Reader counterparts"). -/
theorem alpha_monotone {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep) :
    Monotone (alphaAllowance V) := by
  intro T T' h
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [alpha_zero]
  · have hT' : 1 ≤ T' := by omega
    rw [alpha_eq V hT, alpha_eq V hT']
    have hp : pIndex V T ≤ pIndex V T' := pIndex_monotone V h
    have hL : slowIndex V (pIndex V T) ≤ slowIndex V (pIndex V T') :=
      (slowDiagonal_monotone_unbounded hg).1 _ _ hp
    omega

/-- **`alpha` is unbounded** -- frozen lines 2312--2313, "since
`L(n) -> infinity`, also `alpha(T) -> infinity`", in the finite existential
form (GAP-EXPOSED 3).

The frozen input is the banked `slowDiagonal_monotone_unbounded`, whose second
conjunct is the frozen finite form "for every fixed `K`, all `n >= V_K` satisfy
`K <= L(n)`".  Taking a threshold one above an attained length forces the
frozen search past that index, and the frozen rounding then keeps half of
`K = 2B+1`.

Statement pole: no *fixed* `T` works;
`unboundedness_has_no_uniform_threshold` exhibits, for every `T`, a bound the
value at `T` fails.  General in the clock, the cutoff function and the
bound. -/
theorem alpha_unbounded {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep) (B : ℕ) :
    ∃ T, B ≤ alphaAllowance V T := by
  obtain ⟨m, hm⟩ : ∃ m, m = V (2 * B + 1) := ⟨_, rfl⟩
  have hLm : 2 * B + 1 ≤ slowIndex V m := by
    subst hm
    exact (slowDiagonal_monotone_unbounded hg).2 _ _ (le_refl _)
  refine ⟨tCommon V m + 1, ?_⟩
  rw [alpha_eq V (by omega)]
  have h3 := pIndex_spec V (tCommon V m + 1)
  have hpm : m ≤ pIndex V (tCommon V m + 1) := by
    by_contra hcon
    have h1 : pIndex V (tCommon V m + 1) ≤ m := by omega
    have h2 := truthTable_mono V h1
    omega
  have hL : slowIndex V m ≤ slowIndex V (pIndex V (tCommon V m + 1)) :=
    (slowDiagonal_monotone_unbounded hg).1 _ _ hpm
  omega

/-- **`eq:alpha-gap-fit`** -- `14-final-consequence.tex`, label line 2320,
display lines 2318--2321: `2 alpha(T_n) < L(n)` for every `n` with `L(n) >= 1`.

The proof is the frozen two-case argument of lines 2322--2330 with
`r = L(p(T_n))`: the frozen `p(T_n) <= n` of line 2316 is `pIndex_of_attained`,
`L(p(T_n)) <= L(n)` is the banked monotonicity, and the `r = 0` and `r >= 1`
cases are the frozen truncated arithmetic.  The frozen side condition
`L(n) >= 1` of line 2317 is an explicit binder, and it already forces `n >= 1`
because the banked `slowIndex_le_and_spec` gives `L(0) = 0`.

Non-vacuity: `alphaGapFit_fires` inhabits the whole bundle at a legal
gate-satisfying clock and a source size where the guard holds, and states the
conclusion there.  General in the clock, the cutoff function and the source
size.  Claims no reader item (see "Reader counterparts"). -/
theorem alphaGapFit {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep) (n : ℕ)
    (hn : 1 ≤ slowIndex V n) :
    2 * alphaAllowance V (tCommon V n) < slowIndex V n := by
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · have := (slowIndex_le_and_spec V 0).1
      omega
    · exact hpos
  have hsq : 4 ≤ (n + 2) ^ 2 := by
    have h2 : (2 : ℕ) ≤ n + 2 := by omega
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left h2 2
  have hT : 1 ≤ tCommon V n := by
    have := truthTable_ge V n
    omega
  rw [alpha_eq V hT]
  have hp : pIndex V (tCommon V n) ≤ n := pIndex_of_attained V hn1
  have hL : slowIndex V (pIndex V (tCommon V n)) ≤ slowIndex V n :=
    (slowDiagonal_monotone_unbounded hg).1 _ _ hp
  omega

/-! ## Part 6: non-vacuity, hypothesis consistency, and statement poles -/

/-- **Non-vacuity of `alpha_unbounded` at legal parameter values** (LANE-GATE 3).

`PaddingAndClock.witnessClock` is the banked nondegenerate inhabitant of the
four frozen clock gates, so the hypothesis bundle of `alpha_unbounded` is
consistent, and the conclusion it yields there is not the trivial `0 <= _`:
some allowance value is at least `1`.  General in the cutoff function. -/
theorem alpha_hypotheses_consistent (nstep : ℕ → ℕ) :
    ∃ T, 1 ≤ alphaAllowance (witnessClock nstep) T :=
  alpha_unbounded (witnessClock_gates nstep) 1

/-- **Non-vacuity of `alphaGapFit` at legal parameter values** (LANE-GATE 3).

Both binders are inhabited *simultaneously*: `witnessClock_gates` supplies the
frozen clock gates, and the banked `witnessClock_reaches_positive_index`
supplies a source size at which the frozen guard `1 <= L(n)` genuinely holds.
The statement is the conclusion of `alphaGapFit` at those values, so the pair
of hypotheses is consistent and the deliverable is not vacuous.  General in the
cutoff function. -/
theorem alphaGapFit_fires (nstep : ℕ → ℕ) :
    2 * alphaAllowance (witnessClock nstep)
        (tCommon (witnessClock nstep) (witnessClock nstep 1))
      < slowIndex (witnessClock nstep) (witnessClock nstep 1) :=
  alphaGapFit (witnessClock_gates nstep) _ (witnessClock_reaches_positive_index nstep)

/-- **Statement pole: the frozen guard rejects the trivial index.**

`alphaSearch_exists` would be a restatement of the banked `truthTable_unbounded`
if `n = 0` were allowed; frozen line 2297 writes `n >= 1`, and this records
that the guard really excludes the trivial candidate, at every clock and every
threshold. -/
theorem zeroIndexIsNotAWitness (V : ℕ → ℕ) (T : ℕ) :
    ¬ (1 ≤ 0 ∧ T ≤ tCommon V 0) := by
  rintro ⟨h, -⟩
  omega

/-- **Candidate B refuted in the kernel: the unguarded search is a different
function.**

The rejected encoding takes the minimum of `{n : T_n >= T}`, reusing the banked
`truthTable_unbounded` directly.  At `T = 0` that minimum is `0`, while the
frozen `p` of line 2297 is at least `1` -- so the unguarded spelling violates
the frozen lower index and cannot be the frozen `p` (reading note N1).  General
in the clock. -/
theorem unguardedSearch_violates_the_frozen_lower_index (V : ℕ → ℕ) :
    Nat.find (truthTable_unbounded V 0) = 0 ∧ 1 ≤ pIndex V 0 :=
  ⟨(Nat.find_eq_zero _).2 (Nat.zero_le _), pIndex_pos V 0⟩

/-- **Statement pole: no fixed threshold witnesses unboundedness.**

`alpha_unbounded` is an existential over the threshold, and it has to be: for
every fixed `T` there is a bound the value at `T` fails.  Without this the
existential could be satisfied by a constant allowance.  General in the clock
and the threshold. -/
theorem unboundedness_has_no_uniform_threshold (V : ℕ → ℕ) (T : ℕ) :
    ∃ B, ¬ (B ≤ alphaAllowance V T) :=
  ⟨alphaAllowance V T + 1, by omega⟩

/-- **Statement pole: the frozen strict inequality is not a triviality.**

`alphaGapFit` reads `2 alpha(T_n) < L(n)`.  If the frozen rounding were
slack, the same inequality would hold for a strictly larger allowance; frozen
lines 2331--2335 say it does not, and here that is recorded at a concrete legal
value: with `r = 3` the frozen allowance is `1`, the allowance `2` fails the
plateau-safety test, and `1` is the exact maximum. -/
theorem frozenRounding_is_tight_at_a_legal_value :
    (3 - 1) / 2 = 1 ∧ 2 * 1 < 3 ∧ ¬ (2 * 2 < 3) := by
  refine ⟨by norm_num, by norm_num, by omega⟩

end EthInapproximability.ParameterizedNP.AlphaAllowance
