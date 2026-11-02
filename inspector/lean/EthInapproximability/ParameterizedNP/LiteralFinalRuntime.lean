import EthInapproximability.ParameterizedNP.AlphaAllowance

/-!
# Parameterized NP route: the literal tail-runtime witnesses
(`lem:literal-final-runtime`)

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`ETH-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`, line 135),
whose Lean cell already carries tranche `cc-t1w` (`AlphaAllowance.lean`) and
whose GAP-EXPOSED list names `lem:literal-final-runtime` as the row's open Lean
content.  This module lands *that lemma's literal cost accounting* -- the
displayed code-length and envelope functions, the two machine-composition
envelopes, the list-codec and streaming charges, the polynomial majorant, the
two cutoffs, and the final tail bound -- and nothing downstream of it.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

## Repair round `cc-t1x-r1`

The first round of this tranche was parked at the statement gate with three
confirmed defects.  All three are statement defects that a green build cannot
see, and all three are repaired here; the rest of the module is restored
unchanged.

1. **The M2 call trace and the M5 primitive-site list are now separate.**
   `eq:machine-composition-upper` sums over the **full ordered call trace**
   (frozen lines 229--238 and 255--264), whereas the frozen `h_br` of lines
   2392--2395 counts the M5 *primitive* call sites only.  At the frozen branch
   controller the trace also contains the four major calls `A_gap`,
   `A_realize`, `A_materialize` and `A_app` (frozen lines 2381--2384), so the
   trace has `h_br + 4` entries.  Round 1 bound both roles to one Lean `h`,
   which lands `16 C_K (h_br+9)(Cbar+1)3^{rbar}` at `h := h_br + 4` and drops
   the four major calls at `h := h_br` -- in neither reading is the frozen
   `C_br = 16 C_K (h_br+5)(Cbar+1)3^{rbar}` of lines 2407--2409 obtained.
   `controllerCompositionEnvelope` and `literalValidBranchBound` now index the
   trace by `Finset.range (h_br + 4)` with an explicit four-element `major`
   subset carrying the frozen major-call bounds of lines 2414--2415, and the
   complementary `h_br` primitive sites carrying `primitiveCallEnvelope`.
2. **The top controller now takes the frozen substitution's own input list.**
   Frozen S1 (`thm:encoded-source-package`, S1, lines 1267--1272) bounds
   `A_spar^{eps_*}`'s step count **and** its exact `List(CNF3)`-encoded output
   length by `2^{eps n}P_eps(H)`, the second frozen summand of
   `eq:literal-top-controller-bound`; round 1 instead priced the S1 call by a
   `(H+1)^{r_top}`-shaped charge with a coefficient `Cs1` documented as an
   entry of `Cbar_top`.  It is not one: `Cbar_top = max(1, C_list,
   max_{rho in R_top} C_rho)` (frozen lines 2532--2534) ranges over `C_list`
   and the M5 primitive sites, and `A_spar^{eps_*}` is a major subcall.  That
   false frozen-fact claim is deleted rather than re-worded.  The `C_K` factor
   of `eq:machine-composition-upper`, absent from round 1's `htime`, is
   restored, and the `t` copied branch inputs are summed **once** against the
   S1 output length (the frozen list-length inequality of line 2495), because
   bounding each payload separately by the whole output would square the frozen
   `2^{eps_* n}P_*(H)` term.
3. **`B_gap` is a polynomial evaluation.**  Frozen lines 2361--2362 read
   `B_gap(n) = Q_*(n + B_Phi(n) + 1)` with `Q_eps` a coefficientwise
   nonnegative integer polynomial (frozen lines 1246--1247); round 1 degraded
   it to the scalar product `Q * (n + B_Phi + 1)`.  `gapCodeBound` is now
   `polyEval q dQ (n + bPhi + 1)`, the same evaluation already used for `P_*`,
   and moves to Part 4 for that reason.

Consequences for Part 7: the four witnesses whose binder lists are the repaired
binder lists -- `controllerCompositionEnvelope_fires`,
`literalValidBranchBound_fires`, `literalFinalRuntime_hypotheses_consistent`
and `literalFinalRuntime_fires` -- are re-instantiated at the new lists.  Every
other declaration of the module is restored byte for byte, except the docstring
of `frozenSixteenDominates`, whose sentence "the exact consequence used below"
became false once the repaired derivation carried `C_K` explicitly and is
restated honestly there.

## Repair round `cc-t1x-r2`

`cc-t1x-r1` cleared every declaration except `topControllerEnvelope` and the
`literalFinalRuntime` that composes it.  The one confirmed defect there is
repaired now, and nothing else in the module changes.

* **The `h_top` primitive call sites carry the full M2 triple.**
  `eq:machine-composition-upper` (frozen display lines 255--264) sums
  `|x_j| + |y_j| + s_j` over **every** site `j < h` of the ordered call trace,
  and the frozen `R_top` of lines 2523--2526 is a list of call sites of that
  trace.  Round r1's `htime` charged those sites only `sum_{j<h_top} prim j`,
  i.e. their transition counts, dropping `sum_{j<h_top}(|x_j| + |y_j|)`.  That
  is not instantiable at the composite the lemma names, and it cannot be
  patched by inflating `prim j`, because `primitiveCallEnvelope`'s frozen
  right-hand side `2 Cbar 3^{rbar}(H+1)^{rbar+1}` bounds `s_j` alone and is
  strictly exceeded by the triple.  `topControllerEnvelope` and
  `literalFinalRuntime` now take `primIn`/`primOut` alongside `prim`, with the
  two extra explicit binders `primIn j <= H + 1` and `primOut j <= H + 1`
  (the top envelope of frozen lines 2523--2526), and `htime` sums
  `(primIn j + primOut j + prim j)` -- the same shape
  `controllerCompositionEnvelope` already carries on the branch trace.
* **The frozen constants are unchanged.**  `controllerConstant` and
  `controllerExponent` are untouched.  The new `2 h_top (H+1)^{r_top}` leg is
  absorbed by the `16 h_top 3^{rbar_top}` block of
  `C_top = 16 C_{K_top}(h_top+5)(Cbar_top+1)3^{rbar_top}`, which round r1's
  proof left entirely unused (it appeared only as `0 <= ...`).  The coefficient
  step `hcA` therefore closes at `4 + Cbar + 2 h_top + 2 h_top Cbar 3^{rbar}`
  against the same frozen right-hand side; `hcB` and `hcD` are unaffected.
* **The witnesses are re-instantiated at legal nonzero values.**
  `literalFinalRuntime_hypotheses_consistent` and `literalFinalRuntime_fires`
  now carry `primIn = primOut = 3` at `H = 2` (so both legs are live at their
  ceiling, not satisfied by zero slack) and the re-tightened running time
  `103`.  Every other r1 liveness feature is kept.

The remaining changes of this round are record-only: the supplementary display
*line numbers* in the docstrings of Parts 1, 3 and 5 drifted by one to three
lines against the frozen file (the stable LaTeX labels were and are exact), and
the shortlist filed by the r1 verify seat is corrected here -- `w(t)` at frozen
line 28, `d(t)` at 32, the codec-width display at 27--33,
`def:ordered-3cnf-codec` at 15, `U_br` at 2404--2406, `r_br` at 2407 and
`r_top` at 2535, the list-length inequality uniformly at 2495, and
`eq:literal-final-cutoff` at 2441--2449 with `n_L` at 2442 and `n_tail` at
2443--2447.

## Provenance

* **Autoformalization anchors (proof source).**  `lem:literal-final-runtime`,
  `sections/14-final-consequence.tex`, label line 2343, environment lines
  2342--2573.  Every display in that environment is transcribed here:
  * `def:ordered-3cnf-codec` (label line 15, codec-width display at frozen
    lines 27--33) fixes `w(t) = ceil(log_2(t+1))`,
    `nu(t) = 1^{w(t)} 0 bin_{w(t)}(t)` and `d(t) = ceil(log_2 max{2,t})`;
  * `eq:reference-3cnf-length` (label line 49, display lines 46--50):
    `|enc^ref_3CNF(Phi)| = 2w(n)+1+2w(m)+1+3m(1+d(n))`;
  * `eq:branch-code-bound` (label line 2357, display lines 2353--2357);
  * `eq:graph-code-bound` (label line 2360, displays lines 2358--2360);
  * `B_gap` and `B_app` (frozen lines 2361 and 2370, unlabelled displays inside
    the same `align`), with `Q_*` and `P_*` supplied as *coefficientwise
    nonnegative integer polynomials* by `thm:encoded-source-package` (label
    line 1199, polynomial datum at frozen lines 1246--1247, gap-call charge in
    S2 at lines 1277--1280);
  * `thm:encoded-source-package`, **S1** (frozen lines 1252--1272): the branch
    list with `t <= 2^{eps n}` and `m(Phi_j) <= C_eps n`, and the step-count
    **and** output-length bound `2^{eps n}P_eps(H)`;
  * `eq:literal-mat-envelope` (label line 2368, display lines 2362--2368);
  * `eq:machine-composition-upper` (label line 263, display lines 255--264),
    whose index `j < h` ranges over the full ordered call trace built at frozen
    lines 225--238;
  * the frozen branch-controller call skeleton, frozen lines 2380--2400: the
    four major calls `A_gap`, `A_realize`, `A_materialize`, `A_app`, and the
    finite M5 primitive-site list `R_br` with `h_br = |R_br|`;
  * `eq:primitive-machine-bound` (label line 404, display lines 399--405);
  * `eq:literal-branch-runtime` (label line 2412, display lines 2400--2412),
    with the frozen maxima of lines 2393--2399;
  * `eq:literal-valid-branch-bound` (label line 2427, display lines 2421--2427),
    with its two frozen side conditions at lines 2420--2424;
  * `eq:literal-list-codec` (label line 298, display lines 295--299);
  * the frozen list-length inequality of line 2495,
    `|y| >= 2 sum_{j<t} |x_j| + 2t`;
  * `eq:literal-list-streaming-constant` (label line 2491, display lines
    2488--2491);
  * `eq:literal-list-streaming-bound` (label line 2501, display lines
    2496--2502);
  * the polynomial majorant paragraph, frozen lines 2450--2463
    (`P_*(X) = sum a_j X^j`, `a_P = 1 + sum a_j`, `r_P = max{1,d_P}`, and
    `P_*(H) <= a_P (H+1)^{r_P}`);
  * the frozen `C_top`/`r_top` table, lines 2528--2539;
  * `eq:literal-top-controller-bound` (label line 2555, display lines
    2549--2555);
  * `eq:literal-final-cutoff` (label line 2448, display lines 2441--2449);
  * `eq:literal-final-eth-witnesses` (label line 2562, display lines
    2559--2562);
  * `eq:literal-final-tail-bound` (label line 2571, display lines 2566--2571).
  * `conv:finite-slots` (`sections/02-mechanical-contract.tex`) is untouched:
    no finite index set is introduced or re-indexed anywhere below.

* **Banked endpoints, all grep-verified present in
  `src/EthInapproximability/ParameterizedNP/` before use.**
  *Actually consumed:*
  * from `PaddingAndClock.lean` (tranche `cc-t1t-r1`): **`slowIndex`** (the
    frozen `L`), **`SlowClockGateSet`** (the frozen clock gates, used as an
    explicit binder and never restated), **`slowDiagonal_monotone_unbounded`**
    (whose second conjunct is what makes the frozen `n_L` set nonempty),
    **`witnessClock`**, **`witnessClock_gates`** and
    **`slowIndex_zero_is_attained`** (Part 7's non-vacuity and poles only), and
    the definitions **`tCommon`** (the frozen `T_n`) and **`gMaj`** (the frozen
    `g`), both consumed by `frozenBranchInputEnvelope`;
  * from `AlphaAllowance.lean` (tranche `cc-t1w`): **`alphaAllowance`** (the
    frozen `alpha`) and **`alphaGapFit`** (`eq:alpha-gap-fit`), consumed by
    `tailAllowanceGapFit`, which is the sole reason `n_L` appears inside the
    frozen `n_tail` set at all;
  * from `TruthTableExponent.lean` (tranche `cc-t1v`):
    **`floorAndCeilingDisagreeInGeneral`**, reused (never re-proved) as the
    `M9` pole `floorWidthIsNotTheFrozenWidth`.

  *Verified present but deliberately **not** consumed:*
  `PaddingAndClock.witnessClock_reaches_positive_index` (the positive-index
  guard this module needs comes from the frozen `n_tail` constraint itself,
  through `slowIndexCutoff_spec`, not from a hand-picked source size),
  `PaddingAndClock.gMaj_spec`, `TruthTableExponent.truthTable_ge`,
  `truthTable_monotone`, `truthTable_unbounded`, `commonSquare_ge`,
  `truthTableExponent_sublinear`, and every declaration of `CommonPadding.lean`
  (which is in the import chain through `PaddingAndClock`, but the tail
  accounting runs after final padding and states nothing about the padded
  matrix).  None of the frozen displays in `lem:literal-final-runtime` argues
  from a growth property of `T_n` or `g`: they enter the accounting **only** as
  summands of `U_br` and as the bases of `(T_n+1)^{h_stream}`,
  `(T_n+1)^{r_app}` and `2^{d_mat(g(n)+1)}`.  Consuming a growth lemma here
  would be importing an argument the frozen lemma does not make.  The one
  growth input the frozen lemma *does* use --
  `eq:literal-branch-subexponential` -- is GAP-EXPOSED 3 below.

* **Nature of the proofs.**  New, and literal: every proof below is
  natural-number arithmetic on the frozen displays.  No proof is inherited, and
  the only external adapters are Mathlib's `Nat.clog`, `Nat.pow_le_pow_left`,
  `Nat.pow_le_pow_right`, `Nat.one_le_pow`, `Nat.find` and `Finset.sum_le_sum`.
  `LegacyNPCC.Stage12` is **not** imported, so the cited AGHP axiom stays
  outside this module's closure; no import is added beyond
  `EthInapproximability.ParameterizedNP.AlphaAllowance`.

## What is landed, part by part

1. **The frozen codec widths and code-length envelopes** (frozen lines 27--33,
   46--50, 2353--2371): `codeWidth` (`w`), `indexWidth` (`d`), `headerLength`
   (`|nu(t)|`), `refCodeLength` (`eq:reference-3cnf-length`), `branchCodeBound`
   (`B_Phi`), `graphCodeBound` (`B_G`), `matEnvelope`
   (`B_mat`), `appBound` (`B_app`) and `branchInputEnvelope` (`U_br`), with the
   frozen substitutions `refCodeLength_le_branchCodeBound` (frozen line 2372,
   "S1 and `eq:reference-3cnf-length` give ...") proved rather than posited.
   `gapCodeBound` (`B_gap`) belongs to this display too but is landed in Part 4,
   after `polyEval`, because the frozen `Q_*` is a polynomial.
2. **The two machine envelopes**: `primitiveCallEnvelope` is frozen lines
   2416--2419 applied to `eq:primitive-machine-bound`, and
   `controllerCompositionEnvelope` is the substitution of that into
   `eq:machine-composition-upper` announced at frozen lines 2420--2427,
   landing exactly `C_br U_br^{r_br}` with the frozen constants
   `controllerConstant`/`controllerExponent`.  Its index set is the **M2 call
   trace** `Finset.range (h_br + 4)`, with the four frozen major call sites
   isolated as an explicit four-element `major` subset and the remaining `h_br`
   sites carrying the primitive envelope: the frozen `h_br` is `|R_br|`, not the
   trace length, and the frozen `C_br` is `(h_br + 5)`-shaped precisely because
   the trace is four longer (repair 1 above).  `literalValidBranchBound` is
   `eq:literal-valid-branch-bound` with **both** frozen side conditions kept as
   binders.
3. **The list codec and its streaming charge**: `listCodecLength` is the frozen
   inequality of line 2495 proved from `eq:literal-list-codec`, `listConstant`
   is `eq:literal-list-streaming-constant`, and `listStreamingBound` is
   `eq:literal-list-streaming-bound`.
4. **The polynomial majorant** (frozen lines 2450--2463): `polyEval`,
   `polyMajorant`, `polyExponent`, and `polyMajorant_bound`, together with
   `gapCodeBound`, the frozen `B_gap(n) = Q_*(n + B_Phi(n) + 1)` evaluated with
   the same `polyEval`.
5. **The two cutoffs** (`eq:literal-final-cutoff`): `leastIndexWith` is the
   frozen "least element of a nonempty set of naturals";
   `positiveIndexTailExists` proves the `n_L` set nonempty **from the banked
   `slowDiagonal_monotone_unbounded`** rather than assuming it, and
   `slowIndexCutoff` is `n_L`; `TailCutoffSet`/`tailCutoff` are the frozen
   `n_tail` set and its least element, whose nonemptiness is the named
   hypothesis discussed in GAP-EXPOSED 3, together with the four guard
   consequences of frozen lines 2444--2445.
6. **The top controller and the final witnesses**: `topControllerEnvelope` is
   `eq:literal-top-controller-bound` derived from the frozen substitution's own
   input list -- the `C_K` head of `eq:machine-composition-upper`, the frozen S1
   step **and** output bounds, the one-time list charge, the once-counted
   copied branch inputs with their outputs and runtimes, and the `R_top`
   primitive sites, whose input, output **and** transition count are all
   priced at the top envelope `H + 1` as `eq:machine-composition-upper`
   demands (repair 2 above and the `cc-t1x-r2` repair);
   `satExponent`/`satConstant` are `eq:literal-final-eth-witnesses`; and
   `literalFinalTailBound`, with the capstone `literalFinalRuntime`, is
   `eq:literal-final-tail-bound`.
7. **`tailAllowanceGapFit`**: on the frozen tail the banked `eq:alpha-gap-fit`
   fires, which is precisely why `n_L` is one of the three lower constraints in
   the frozen `n_tail` set.  This is the fit, **not** the promise-case
   contradiction (GAP-EXPOSED 6).
8. **Non-vacuity, hypothesis consistency, and statement poles** (Part 7).

## Reader counterparts

The reader artifact is
`routes/parameterized-np/reader-facing/sections/06-eth.tex`.  **That file was
opened first-hand this tranche and every cited item was read to confirm what it
states.**

**No declaration below claims a reader item.**  The reader states this lemma's
content only as big-`O` prose inside the proof of `prop:paper-eth-consequence`
(reader lines 442--464: "There are at most `2^{eps n}` branches", "The graph
reduction is polynomial per branch", and the two unlabelled displays
`T_n^{O(1)} = 2^{o(n)}` and `2^{3 eps n}|Phi|^{O(1)}`).  Those are prose and
unlabelled asymptotic displays, not statements, and the reader's exponent
`3 eps` is a different accounting from the frozen autoformalization's
`2 eps_*` -- the frozen paper is the proof source, and citing the reader's
coarser count as the counterpart of `eq:literal-final-tail-bound` would be a
mis-assignment.  So this tranche claims **no** reader item for its own
declarations, and records that fact rather than hiding it.

**Reader items assigned by this tranche to already-landed `cc-t1w`
declarations** (previously recorded as deliberately unassigned in the `ETH-001`
ledger cell, now taken, split by clause, none assigned twice, and none
re-claimed from any other row):

* reader lines 360--363, the sentences "Both `p` and `L` are nondecreasing, so
  `alpha` is total, computable, and nondecreasing.  Since `p(T) -> infinity`
  and `L(n) -> infinity`, it is also unbounded", split by clause --
  the `p` nondecreasing clause to `AlphaAllowance.pIndex_monotone`, the `alpha`
  nondecreasing clause to `AlphaAllowance.alpha_monotone`, and the unbounded
  clause to `AlphaAllowance.alpha_unbounded`.  The *computable* clause is
  **not** claimed (GAP-EXPOSED 2), and the `L` nondecreasing clause stays with
  `CLOCK-001`'s `slowDiagonal_monotone_unbounded`, which already owns reader
  lines 332--333.  Line 360 also opens with the *earlier* sentence "The search
  for `p(T)` terminates because `T_n >= (n+2)^2`", which stays with tranche
  `cc-t1v`'s `TruthTableExponent.truthTable_ge`: the two sentences share a
  source line but are different items, and nothing is assigned twice;
* `eq:paper-alpha-fits-gap` (label line 370, display lines 368--371) to
  `AlphaAllowance.alphaGapFit`.

**`eq:paper-g-little-o` (label line 312) stays unclaimed.**  It states
`g(n) = o(n)`.  No little-`o`, `Filter.Tendsto`, or asymptotic order relation
is landed in this module or in any banked module (`CommonPadding.lean` records
the same disposition for `log_2 T_n = o(n)`), and this tranche does not change
that: the frozen `eq:literal-branch-subexponential` that would consume it is
GAP-EXPOSED 3.  Recording it as unclaimed is the accurate disposition, not an
omission.

## Mechanical-contract compliance (`M1`--`M10`, frozen Section 2)

* `M2`/`M4`: **this module introduces no structure at all**, so no constructor
  can carry a conclusion.  `TailCutoffSet` is a two-clause `Prop`-valued
  abbreviation of the frozen set-builder of `eq:literal-final-cutoff`, not a
  bundle: both clauses are printed in the frozen display, and neither restates
  a derived telescope.  Every conditional deliverable takes explicit binders --
  the frozen clock gates as the banked `SlowClockGateSet`, the frozen side
  conditions of `eq:literal-valid-branch-bound` as `hn`/`hvalid`, and every
  machine-cost input as its own named inequality.
* `M3` (binder order): the frozen text fixes B1--B6 first and only then
  instantiates `L, g, e, T_n`; here the clock `V` is the first binder of every
  declaration that mentions `L`, `g` or `T_n`, and no statement quantifies over
  a cost before the datum it prices.  B1--B6 themselves are not modelled
  (GAP-EXPOSED 1).
* `M7` (nonemptiness facts are proved, never posited): the frozen `n_L` set is
  proved nonempty in `positiveIndexTailExists` from the banked
  `slowDiagonal_monotone_unbounded`.  The frozen `n_tail` set is **not**
  provable here and is therefore an explicit hypothesis -- and
  `tailCutoffSet_can_be_empty` proves in the kernel that it genuinely can be
  empty, so this is a real assumption and not a disguised triviality.
* `M9` (ceilings are preserved): the frozen `w(t) = ceil(log_2(t+1))` and
  `d(t) = ceil(log_2 max{2,t})` are landed as `Nat.clog 2 (t+1)` and
  `Nat.clog 2 (max 2 t)` -- ceiling logarithms, matching the banked
  `Nat.clog 2 (n+2)` spelling of `eCommon`.  No ceiling is replaced by a floor,
  and `J_G(n) = ceil(n lambda_n^{c_*})` is left as an explicit binder rather
  than encoded, because `lambda_n = log_2(n+2)` is a real logarithm and the
  machine layer that produces `J_G` is unlanded (GAP-EXPOSED 4).
* Selector costs, both interlace widths `q` and `Q`, and every finite carrier
  are untouched: the tail accounting runs strictly after the last level and
  after final padding, so no interlace, carrier, or slot occurs below.  The
  frozen `Q_*` of `B_gap` is the *source package's* polynomial datum of B3, not
  an interlace width, and is carried as an opaque binder.

## GAP-EXPOSED (what this module deliberately does not claim)

1. **The machine layer is not modelled, by design.**  Nothing here defines
   `mathfrak M`, `time_M`, `Comp_M`, `enc_3CNF`, `enc_G`, `A_spar`, `A_gap`,
   `A_realize`, `A_materialize`, `A_app`, `A_br`, `A_SAT`, `A_bf`, an M2
   certificate, an M5 primitive, `PolyApprox_M(alpha)`, `EncodedETH`, or
   `CitedETH`.  Every machine quantity is a natural number supplied by an
   explicit binder, and every machine fact is a named hypothesis inequality.
   `MATERIALIZE-001` is therefore **GAP-EXPOSED** here in exactly the frozen
   place: `eq:materializer-exact-runtime` enters only through the binder
   pattern of `matEnvelope`, and `thm:effective-materialization` itself is not
   formalized.
2. **Computability, totality of the controllers, and the M2 certificates are
   not claimed.**  Frozen lines 2510--2519 argue that `A_SAT` is total from the
   totality of every named submachine; that argument is about machines and is
   not transcribed.  What is landed is the arithmetic that the frozen text
   performs *given* the charge bounds.
3. **`eq:literal-branch-subexponential` is not landed, and neither is any limit
   form.**  Frozen lines 2432--2438 conclude `R_br(n) = 2^{o(n)}` from
   `g(n) = o(n)`, `T_n = 2^{o(n)}` and `L(n) <= n`.  No `Filter.Tendsto`, no
   `o`/`O` relation, and no `Real` asymptotic appears anywhere below.  The
   consequence the frozen text draws from it -- that the `n_tail` set of
   `eq:literal-final-cutoff` is nonempty -- is therefore a **named hypothesis**
   (`tailCutoff`'s existence argument), and `tailCutoffSet_can_be_empty` shows
   that hypothesis is not free.  The companion `n_L` set is *not* hypothesized:
   it is proved from banked material.
4. **`epsilon_*` is not modelled.**  The frozen branch-count and tail envelopes
   `2^{eps_* n}` and `2^{2 eps_* n}` are carried as an abstract natural-number
   envelope `e` with `1 <= e`, so `eq:literal-final-tail-bound` is landed as
   `K_SAT * e^2 * (H+1)^{r_SAT}`.  The frozen exponent doubling is preserved
   *as a square*, which is the point of candidate ranking below.  Likewise
   `J_G(n) = ceil(n lambda_n^{c_*})`, `delta_ETH`, and the rational arithmetic
   `eps_* = delta_ETH/8` are not encoded.
5. **`thm:effective-main` and `thm:main` are untouched.**  Frozen lines
   2575--2600 and the promise-case contradiction of lines 2637--2650 are
   `ETH-001`'s remaining open content and nothing below states, implies, or
   approaches them.
6. **`tailAllowanceGapFit` is the fit, not the contradiction.**  It says only
   that on the frozen tail the guard `1 <= L(n)` of `eq:alpha-gap-fit` holds,
   so the banked `alphaGapFit` applies.  It makes no claim about `YES`/`NO`
   cases, about `2z` versus `2Y_k+k`, or about any approximation algorithm.
7. **The uniform `A_bf` bound of frozen lines 2606--2613 is not landed.**  It
   is stated from S3, which is machine content.
8. **No route completion is claimed.**  The headline theorem of the route is
   not in Lean.

## Reading notes

* **N1 (why `U_br` carries its leading `1`).**  Frozen lines 2404--2406 write
  `U_br(n) = 1 + n + B_Phi(n) + ...`.  The `1` is not cosmetic: every envelope
  step below divides by nothing but does raise `U_br` to a positive power, and
  `1 <= U_br` is what makes `U <= U^{r+1}` available.  `one_le_branchInputEnvelope`
  records this, and the two envelope theorems take `1 <= U` as a binder so that
  they remain general (they are true of any positive envelope, not only of the
  frozen sum).
* **N2 (why `C_br` and `C_top` are one Lean constant).**  Frozen lines
  2407--2409 and 2536--2538 print *the same literal expression*
  `16 C_K (h+5) (Cbar+1) 3^{rbar}` at two different controller tables, and
  likewise `r_br = rbar_br + 1` and `r_top = rbar_top + 1`.  They are landed as
  one `controllerConstant`/`controllerExponent` applied at two argument tuples;
  this is transcription, not identification, and no property of one is
  transferred to the other.  In both tuples the `h` slot is the **primitive**
  call-site count (`h_br = |R_br|`, `h_top = |R_top|`), never a call-trace
  length; see N6.
* **N3 (why `2 Cbar 3^{rbar} U^{rbar+1}` and not the frozen bound verbatim).**
  Frozen lines 2418--2421 say that on a primitive call
  `eq:primitive-machine-bound` "is at most `2 Cbar_br 3^{rbar_br}
  U_br^{rbar_br+1}`".  `primitiveCallEnvelope` proves exactly that implication
  from `eq:primitive-machine-bound`'s literal left-hand side, so the frozen
  sentence is a theorem here rather than a definition.
* **N4 (why the top-controller derivation needs the `+5`).**
  Frozen line 2570 says the factor 16 "deliberately dominates the four major
  call sites, the controller input and output terms, and the finite
  primitive-call list".  In `topControllerEnvelope` the coefficient step `hcA`
  is exactly that dominance in expanded form: `C_top` contains the summand
  `80 Cbar_top 3^{rbar_top}`, which absorbs both the controller's own input and
  output terms and the `+1` of `eq:literal-list-streaming-bound`, the summand
  `16 h_top Cbar_top 3^{rbar_top}`, which absorbs the transition counts of the
  primitive-call list, and the summand `16 h_top 3^{rbar_top}`, which absorbs
  those sites' own input and output lengths -- the leg the `cc-t1x-r2` repair
  restored, and the one block round 1 left unused.  The `C_K` factor cancels on
  both sides, so, unlike round 1, no
  `1 <= C_K` binder is needed; `frozenSixteenDominates` records the frozen
  sentence itself as a standalone kernel fact.
* **N5 (why `r_P = max{1, d_P}` and not `d_P`).**  Frozen line 2461 prints the
  guard.  Without it a constant polynomial (`d_P = 0`) would give `r_P = 0` and
  the majorant step `H^j <= (H+1)^{r_P}` would still hold, but `r_SAT` could
  then be `0` and `(H+1)^{r_SAT} = 1`, which is not what the frozen final
  display prices; `polyExponent_is_positive` records the guard in the kernel.
* **N6 (why the call trace is `h_br + 4` and not `h_br`).**  The two frozen
  numbers have different definitions: `h` in `eq:machine-composition-upper` is
  the length of the ordered call trace whose blocks make up the token set of
  frozen lines 225--238, while `h_br` at line 2395 is `|R_br|`, the finite list
  of **M5 primitive** call sites.  Frozen lines 2381--2384 name the four major
  calls of the branch controller, so the trace is `h_br + 4` long, and the
  frozen `(h_br + 5)` of `C_br` is what a trace of that length costs.  The same
  reading applies at the top table: `R_top` is defined at frozen lines
  2523--2526 as the primitive sites "outside both the already charged branch
  controller and the separately charged one-pass streaming layer", so those
  layers appear in `topControllerEnvelope` as their own summands and not as
  entries of `h_top`.
* **N7 (why the copied branch inputs are summed once).**  The frozen top bound
  carries one factor `2^{eps_* n}P_*(H)`, not its square.  The `t` copied
  payloads are disjoint substrings of the single S1 output `y`
  (`eq:literal-list-codec`, and the frozen inequality
  `|y| >= 2 sum_{j<t}|x_j| + 2t` of line 2495, landed as `listCodecLength`), so
  the M2 sum of the copied inputs is bounded **in total** by `|y|`.  Bounding
  each payload separately by `|y|` and then summing `t <= 2^{eps_* n}` of them
  would multiply the frozen term by a further branch envelope -- an over-strong
  hypothesis that typechecks perfectly.  `hbrInSum` is therefore stated on the
  sum, not pointwise.

## Candidate encodings and ranking (NOVEL-concept protocol)

The genuinely novel design decision in this module is how to encode the frozen
branch-count envelope `2^{eps_* n}` and its square `2^{2 eps_* n}`, since
`eps_*` is a positive **rational** and the frozen paper never gives it a
natural-number spelling.  Two encodings were written and run against the same
aux-lemma battery before landing.

* **Candidate A (landed).**  Carry the envelope abstractly: a natural number
  `e` with the single frozen property `1 <= e` (true of `2^{eps_* n}` for every
  positive rational `eps_*` and every `n`), with `e^2` for `2^{2 eps_* n}`.
  Every downstream inequality is then proved for *every* such envelope.
* **Candidate B (rejected).**  Spell the envelope in `Nat` as
  `2 ^ (epsNum * n / epsDen)` with truncated division, so that `eps_*` is
  literally present as a pair of naturals.

Ranking.  Battery (the general lemmas marked **Aux 1**--**Aux 9** below):
A proved 9/9.  B proved 8/9 and is **disqualified on Aux 9** (the squaring
law).  The frozen final display is `2^{2 eps_* n}`, and under B that is
`2 ^ (2 * epsNum * n / epsDen)`, whereas the product of two branch envelopes is
`2 ^ (epsNum * n / epsDen) * 2 ^ (epsNum * n / epsDen)`.  Truncated division
makes these *different numbers*:
`truncatedEpsilonExponent_is_not_the_frozen_square` records in the kernel that
at `eps_* = 1/2` and `n = 1` the product is `1` while the frozen display is
`2`.  Landing B would therefore have silently **strengthened** the frozen tail
bound by a factor of two -- an over-strong conclusion that typechecks perfectly
(LANE-GATE 4b) -- while also fixing an interface (a rational `eps_*` in `Nat`
form) that the unlanded machine layer has not chosen.  Faithfulness: A states
exactly what the frozen displays use about the envelope and nothing more;
B states more than the paper and gets it wrong.  Length: B is longer, because
every step needs a division side condition.  Candidate A wins on all three
axes.

## Statement poles

* `positiveIndexTailExists` is an existential deliverable, and the trivial
  witness fails it: `zeroThresholdIsNotATailWitness` shows that `N = 0` is
  rejected at the banked witness clock, because `L(0) = 0` there (banked
  `slowIndex_zero_is_attained`).  So the existential really is a search for a
  positive threshold beyond which the clock index is positive.
* The `n_tail` existential is **not** landed as a theorem precisely because it
  has no trivial witness *and* no proof from banked material:
  `tailCutoffSet_can_be_empty` exhibits legal `R_br` and `E` for which the
  frozen set is empty.  That is the pole that forces GAP-EXPOSED 3.
* `literalFinalTailBound` is a universally quantified upper bound, so it has no
  trivial witness; its pole is degeneracy of the *constant*.
  `satConstant_factor_is_needed` exhibits legal values at which the frozen
  `K_SAT = C_top (a_P + 2)` holds but `C_top` alone fails, so the frozen
  `a_P + 2` is not slack, and `frozenSquare_is_needed` exhibits legal values at
  which the frozen `e^2` holds but a single `e` fails, so the frozen exponent
  doubling is not slack either.
* `primitiveCallEnvelope` and `controllerCompositionEnvelope` are conditional
  deliverables whose whole binder lists are inhabited at nondegenerate values
  by `primitiveCallEnvelope_fires` and `controllerCompositionEnvelope_fires`
  (positive call counts, positive costs, and a genuinely nonempty sum -- with
  **both** halves of the trace split nonempty: four major sites and two
  primitive sites), and the headline binder list is inhabited simultaneously by
  `literalFinalRuntime_hypotheses_consistent`, which is the kernel form of the
  "attempt to derive `False` from the full hypothesis bundle" check: a
  simultaneous witness is a proof that no contradiction is derivable.  In that
  witness the branch-input sum is `10` against the frozen ceiling `12`, so the
  once-counted list constraint of N7 is live and not satisfied by slack.
* The three repairs of round `cc-t1x-r1` each carry their own pole, so the
  defect they fix is checkable rather than merely described:
  `traceLengthIsNotThePrimitiveSiteCount` (the two readings of `h` give
  different frozen constants), `perBranchPayloadBoundIsNotTheFrozenListBound`
  (a pointwise payload bound does not give the frozen sum bound), and
  `scalarGapBoundIsNotTheFrozenPolynomial` (the frozen `Q_*` takes values no
  scalar multiple of its argument takes).
-/

namespace EthInapproximability.ParameterizedNP.LiteralFinalRuntime

open EthInapproximability.ParameterizedNP.PaddingAndClock
open EthInapproximability.ParameterizedNP.AlphaAllowance

/-! ## Part 1: the frozen codec widths and literal code-length envelopes -/

/-- The frozen unary/binary header width `w(t) = ceil(log_2(t+1))`
(`def:ordered-3cnf-codec`, frozen line 28). -/
def codeWidth (t : ℕ) : ℕ := Nat.clog 2 (t + 1)

/-- The frozen variable-index width `d(t) = ceil(log_2 max{2,t})`
(`def:ordered-3cnf-codec`, frozen line 32). -/
def indexWidth (t : ℕ) : ℕ := Nat.clog 2 (max 2 t)

/-- The literal length of the frozen self-delimiting header
`nu(t) = 1^{w(t)} 0 bin_{w(t)}(t)` (frozen line 30): `w(t)` ones, one zero, and
`w(t)` payload bits. -/
def headerLength (t : ℕ) : ℕ := 2 * codeWidth t + 1

/-- `eq:reference-3cnf-length` (frozen display lines 46--50): the exact length
of the reference 3-CNF encoding of a record with `n` variables and `m`
clauses. -/
def refCodeLength (n m : ℕ) : ℕ :=
  2 * codeWidth n + 1 + 2 * codeWidth m + 1 + 3 * m * (1 + indexWidth n)

/-- `eq:branch-code-bound` (frozen display lines 2353--2357):
`B_Phi(n) = 2w(n)+1+2w(C_* n)+1+3 C_* n (1+d(n))`. -/
def branchCodeBound (C n : ℕ) : ℕ :=
  2 * codeWidth n + 1 + 2 * codeWidth (C * n) + 1 + 3 * (C * n) * (1 + indexWidth n)

/-- `eq:graph-code-bound` (frozen display line 2360):
`B_G(n) = 4w(J_G(n)) + 2 + 2 J_G(n) d(J_G(n))`, at the supplied value
`J = J_G(n)` (GAP-EXPOSED 4). -/
def graphCodeBound (J : ℕ) : ℕ := 4 * codeWidth J + 2 + 2 * J * indexWidth J

-- The frozen gap-call envelope `B_gap(n) = Q_*(n + B_Phi(n) + 1)` (frozen lines
-- 2361--2362) is landed in Part 4 as `gapCodeBound`, immediately after
-- `polyEval`: the frozen `Q_*` is a coefficientwise nonnegative integer
-- polynomial (`thm:encoded-source-package`, frozen lines 1246--1247), so its
-- value at `n + B_Phi(n) + 1` is a polynomial evaluation and not a product by a
-- scalar.  Nothing in Part 1 depends on it: `branchInputEnvelope` takes the
-- value of `B_gap` as an opaque summand.

/-- `eq:literal-mat-envelope` (frozen display lines 2362--2368):
`B_mat(n) = C_mat((n+1)(n+B_G(n)+1)^{r_mat} + (n+1)2^{d_mat(g(n)+1)}
            + (T_n+1)^{h_stream})`. -/
def matEnvelope (Cmat rmat dmat hstream n bG gn Tn : ℕ) : ℕ :=
  Cmat * ((n + 1) * (n + bG + 1) ^ rmat
        + (n + 1) * 2 ^ (dmat * (gn + 1))
        + (Tn + 1) ^ hstream)

/-- The frozen approximation-call envelope (frozen line 2370):
`B_app(n) = K_app (T_n+1)^{r_app}`. -/
def appBound (Kapp rapp Tn : ℕ) : ℕ := Kapp * (Tn + 1) ^ rapp

/-- `eq:literal-branch-runtime`, first line (frozen lines 2404--2406):
`U_br(n) = 1 + n + B_Phi(n) + B_G(n) + g(n) + T_n + B_gap(n) + B_mat(n)
           + B_app(n)`. -/
def branchInputEnvelope (n bPhi bG gn Tn bgap bmat bapp : ℕ) : ℕ :=
  1 + n + bPhi + bG + gn + Tn + bgap + bmat + bapp

/-- **Aux 1 (the frozen `B_Phi` is the frozen exact length at the frozen clause
bound).**

Frozen line 2372: "Indeed, S1 and `eq:reference-3cnf-length` give
`|enc_3CNF(Phi_j)| <= B_Phi(n)`."  The frozen substitution is `m := C_* n`, and
the resulting inequality is *proved* here from monotonicity of the ceiling
logarithm rather than posited.  General in the clause count, the source
constant and the variable count. -/
theorem refCodeLength_le_branchCodeBound {C n m : ℕ} (hm : m ≤ C * n) :
    refCodeLength n m ≤ branchCodeBound C n := by
  have hw : codeWidth m ≤ codeWidth (C * n) :=
    Nat.clog_mono_right 2 (by omega)
  have hmul : 3 * m * (1 + indexWidth n) ≤ 3 * (C * n) * (1 + indexWidth n) :=
    Nat.mul_le_mul (Nat.mul_le_mul le_rfl hm) le_rfl
  simp only [refCodeLength, branchCodeBound]
  omega

/-- **Aux 2 (the frozen envelope is positive).**

Frozen lines 2404--2406 write the leading `1` of `U_br` explicitly; reading note N1
explains why it is load-bearing.  General in all eight summands. -/
theorem one_le_branchInputEnvelope (n bPhi bG gn Tn bgap bmat bapp : ℕ) :
    1 ≤ branchInputEnvelope n bPhi bG gn Tn bgap bmat bapp := by
  simp only [branchInputEnvelope]
  omega

/-- The frozen branch envelope at the banked clock data: `g` is the banked
`PaddingAndClock.gMaj` and `T_n` is the banked `PaddingAndClock.tCommon`, so
this is `U_br` with its two clock-dependent summands taken from the landed
definitions rather than re-introduced.  General in the clock and in every
machine-supplied summand. -/
noncomputable def frozenBranchInputEnvelope (V : ℕ → ℕ) (n bPhi bG bgap bmat bapp : ℕ) : ℕ :=
  branchInputEnvelope n bPhi bG (gMaj V n) (tCommon V n) bgap bmat bapp

/-! ## Part 2: the two frozen machine envelopes -/

/-- `r_br = rbar_br + 1` and `r_top = rbar_top + 1` (frozen lines 2407 and
2535); see reading note N2. -/
def controllerExponent (rbar : ℕ) : ℕ := rbar + 1

/-- `C_br = 16 C_{K_br}(h_br+5)(Cbar_br+1)3^{rbar_br}` (frozen lines
2407--2409) and, at the top table, `C_top` (frozen lines 2536--2538); see
reading note N2. -/
def controllerConstant (CK h Cbar rbar : ℕ) : ℕ :=
  16 * CK * (h + 5) * (Cbar + 1) * 3 ^ rbar

/-- `R_br(n) = C_br U_br(n)^{r_br}` (frozen line 2411). -/
def controllerRuntime (CK h Cbar rbar U : ℕ) : ℕ :=
  controllerConstant CK h Cbar rbar * U ^ controllerExponent rbar

/-- **Aux 3 (the frozen primitive-call envelope).**

Frozen lines 2418--2421: "For a primitive call, its input, output, and literal
scan or emit budget are at most `U_br`, so `eq:primitive-machine-bound` is at
most `2 Cbar_br 3^{rbar_br} U_br^{rbar_br+1}`."  The left-hand side below is
`eq:primitive-machine-bound` (frozen display lines 399--405) verbatim:
`C_rho (1 + |x| + |out|)^{r_rho} (1 + J_rho(x))`.  General in the primitive's
table entry, the controller maxima, and the envelope. -/
theorem primitiveCallEnvelope {Crho rrho Cbar rbar inLen outLen budget U : ℕ}
    (hC : Crho ≤ Cbar) (hr : rrho ≤ rbar) (hU : 1 ≤ U)
    (hin : inLen ≤ U) (hout : outLen ≤ U) (hbud : budget ≤ U) :
    Crho * (1 + inLen + outLen) ^ rrho * (1 + budget)
      ≤ 2 * Cbar * 3 ^ rbar * U ^ (rbar + 1) := by
  have h1 : 1 + inLen + outLen ≤ 3 * U := by omega
  have h2 : (1 + inLen + outLen) ^ rrho ≤ (3 * U) ^ rrho := Nat.pow_le_pow_left h1 _
  have h3 : (3 * U) ^ rrho ≤ (3 * U) ^ rbar := Nat.pow_le_pow_right (by omega) hr
  have h4 : 1 + budget ≤ 2 * U := by omega
  calc Crho * (1 + inLen + outLen) ^ rrho * (1 + budget)
      ≤ Cbar * (3 * U) ^ rbar * (2 * U) :=
        Nat.mul_le_mul (Nat.mul_le_mul hC (le_trans h2 h3)) h4
    _ = 2 * Cbar * 3 ^ rbar * U ^ (rbar + 1) := by rw [mul_pow]; ring

/-- **Aux 4 (the frozen M2 composition envelope, with the M2 call trace and the
M5 primitive-site list kept apart).**

`eq:machine-composition-upper` (frozen display lines 255--264) prices a
certified composite by
`C_K(1 + |x| + |out| + sum_{j<h}(|x_j| + |y_j| + s_j))`, where the index `j`
ranges over the **full ordered call trace** of the composite (frozen lines
229--238 build the token set as `{star} + [|x|] + [|out|]` disjoint-union the
blocks of *all* `h` subcalls).  The frozen `h_br` of lines 2392--2395 is a
**different** number: it is `|R_br|`, the length of the finite list of M5
*primitive* call sites only.  At the frozen branch controller the trace also
contains the four major calls `A_gap`, `A_realize`, `A_materialize` and `A_app`
(frozen lines 2381--2384), so the trace length is `h_br + 4`.

That separation is what this statement keeps.  The trace is
`Finset.range (h_br + 4)`; `major` is the four-element set of major call sites,
where frozen lines 2414--2415 give input, output **and** transition count at
most `U_br`; on the remaining `h_br` primitive sites frozen lines 2416--2419
give the `primitiveCallEnvelope` bound.  The result is exactly
`C_br U_br^{r_br}` with the frozen
`C_br = 16 C_K (h_br+5)(Cbar_br+1)3^{rbar_br}` -- binding both roles to one
Lean variable would instead land `(h_br+9)` at `h := h_br + 4`, or silently
drop the four major calls at `h := h_br`.  The numerical factor 16 of frozen
lines 2428--2430 is what makes the substitution close.

General in the controller table, the trace, the choice of major sites, and the
envelope. -/
theorem controllerCompositionEnvelope {CK hbr Cbar rbar U inLen outLen : ℕ}
    {x y s : ℕ → ℕ} (major : Finset ℕ)
    (hmajor : major ⊆ Finset.range (hbr + 4)) (hcard : major.card = 4)
    (hU : 1 ≤ U) (hin : inLen ≤ U) (hout : outLen ≤ U)
    (hx : ∀ j ∈ Finset.range (hbr + 4), x j ≤ U)
    (hy : ∀ j ∈ Finset.range (hbr + 4), y j ≤ U)
    (hsmajor : ∀ j ∈ major, s j ≤ U)
    (hsprim : ∀ j ∈ Finset.range (hbr + 4) \ major,
      s j ≤ 2 * Cbar * 3 ^ rbar * U ^ (rbar + 1)) :
    CK * (1 + inLen + outLen + ∑ j ∈ Finset.range (hbr + 4), (x j + y j + s j))
      ≤ controllerRuntime CK hbr Cbar rbar U := by
  have hP : 1 ≤ 3 ^ rbar := Nat.one_le_pow _ _ (by norm_num)
  have hW1 : 1 ≤ U ^ (rbar + 1) := Nat.one_le_pow _ _ (by omega)
  have hUW : U ≤ U ^ (rbar + 1) := by
    calc U = U ^ 1 := (pow_one U).symm
      _ ≤ U ^ (rbar + 1) := Nat.pow_le_pow_right hU (by omega)
  have hcards : (Finset.range (hbr + 4) \ major).card = hbr := by
    rw [Finset.card_sdiff_of_subset hmajor, Finset.card_range, hcard]
    omega
  have hsplit : (∑ j ∈ Finset.range (hbr + 4) \ major, (x j + y j + s j))
        + ∑ j ∈ major, (x j + y j + s j)
      = ∑ j ∈ Finset.range (hbr + 4), (x j + y j + s j) :=
    Finset.sum_sdiff hmajor
  have hmajsum : ∑ j ∈ major, (x j + y j + s j) ≤ 12 * U := by
    calc ∑ j ∈ major, (x j + y j + s j) ≤ ∑ _j ∈ major, (3 * U) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          have h1 := hx j (hmajor hj)
          have h2 := hy j (hmajor hj)
          have h3 := hsmajor j hj
          omega
      _ = major.card * (3 * U) := by simp [Finset.sum_const, mul_comm]
      _ = 12 * U := by rw [hcard]; ring
  have hprimsum : ∑ j ∈ Finset.range (hbr + 4) \ major, (x j + y j + s j)
      ≤ hbr * (2 * U + 2 * Cbar * 3 ^ rbar * U ^ (rbar + 1)) := by
    calc ∑ j ∈ Finset.range (hbr + 4) \ major, (x j + y j + s j)
        ≤ ∑ _j ∈ Finset.range (hbr + 4) \ major,
            (2 * U + 2 * Cbar * 3 ^ rbar * U ^ (rbar + 1)) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          have hjmem : j ∈ Finset.range (hbr + 4) := (Finset.mem_sdiff.mp hj).1
          calc x j + y j + s j
              ≤ U + U + 2 * Cbar * 3 ^ rbar * U ^ (rbar + 1) :=
                Nat.add_le_add (Nat.add_le_add (hx j hjmem) (hy j hjmem)) (hsprim j hj)
            _ = 2 * U + 2 * Cbar * 3 ^ rbar * U ^ (rbar + 1) := by ring
      _ = (Finset.range (hbr + 4) \ major).card
            * (2 * U + 2 * Cbar * 3 ^ rbar * U ^ (rbar + 1)) := by
          simp [Finset.sum_const, mul_comm]
      _ = hbr * (2 * U + 2 * Cbar * 3 ^ rbar * U ^ (rbar + 1)) := by rw [hcards]
  have hsum : ∑ j ∈ Finset.range (hbr + 4), (x j + y j + s j)
      ≤ 12 * U + hbr * (2 * U + 2 * Cbar * 3 ^ rbar * U ^ (rbar + 1)) := by
    omega
  have hstep : 15 + 2 * hbr + 2 * hbr * Cbar * 3 ^ rbar
      ≤ 16 * (hbr + 5) * (Cbar + 1) * 3 ^ rbar := by
    have e1 : 16 * (hbr + 5) * (Cbar + 1) * 3 ^ rbar
        = 16 * hbr * Cbar * 3 ^ rbar + 16 * hbr * 3 ^ rbar
          + 80 * Cbar * 3 ^ rbar + 80 * 3 ^ rbar := by ring
    have b1 : (15 : ℕ) ≤ 80 * 3 ^ rbar := by
      calc (15 : ℕ) ≤ 80 * 1 := by norm_num
        _ ≤ 80 * 3 ^ rbar := Nat.mul_le_mul le_rfl hP
    have b2 : 2 * hbr ≤ 16 * hbr * 3 ^ rbar := by
      calc 2 * hbr ≤ 16 * hbr * 1 := by omega
        _ ≤ 16 * hbr * 3 ^ rbar := Nat.mul_le_mul le_rfl hP
    have b3 : 2 * hbr * Cbar * 3 ^ rbar ≤ 16 * hbr * Cbar * 3 ^ rbar :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) le_rfl
    have b4 : 0 ≤ 80 * Cbar * 3 ^ rbar := Nat.zero_le _
    rw [e1]
    omega
  calc CK * (1 + inLen + outLen + ∑ j ∈ Finset.range (hbr + 4), (x j + y j + s j))
      ≤ CK * (1 + U + U
          + (12 * U + hbr * (2 * U + 2 * Cbar * 3 ^ rbar * U ^ (rbar + 1)))) :=
        Nat.mul_le_mul le_rfl
          (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add le_rfl hin) hout) hsum)
    _ ≤ CK * (U ^ (rbar + 1) + U ^ (rbar + 1) + U ^ (rbar + 1)
          + (12 * U ^ (rbar + 1)
            + hbr * (2 * U ^ (rbar + 1) + 2 * Cbar * 3 ^ rbar * U ^ (rbar + 1)))) := by
        refine Nat.mul_le_mul le_rfl ?_
        refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hW1 hUW) hUW) ?_
        refine Nat.add_le_add (Nat.mul_le_mul le_rfl hUW) ?_
        exact Nat.mul_le_mul le_rfl
          (Nat.add_le_add (Nat.mul_le_mul le_rfl hUW) le_rfl)
    _ = CK * U ^ (rbar + 1) * (15 + 2 * hbr + 2 * hbr * Cbar * 3 ^ rbar) := by ring
    _ ≤ CK * U ^ (rbar + 1) * (16 * (hbr + 5) * (Cbar + 1) * 3 ^ rbar) :=
        Nat.mul_le_mul le_rfl hstep
    _ = controllerRuntime CK hbr Cbar rbar U := by
        simp only [controllerRuntime, controllerConstant, controllerExponent]
        ring

/-- `eq:literal-valid-branch-bound` (frozen display lines 2421--2427).

The frozen statement is conditional on **both** side conditions printed at
frozen lines 2420--2424: `n >= max{n_eps_*, n_mat}`, and the branch lying in the
exact S1 list, so that the resulting graph satisfies
`SourceOut_{P_eps_*}(n,G)`.  Both are kept as binders here, and both are used:
the machine layer supplies the M2 charge bound and the envelope bounds only
under those conditions, which is why `hM2` is stated as an implication from
them.  `SourceOut` is an opaque `Prop` binder because the guarded-source
predicate is not formalized (GAP-EXPOSED 1).

The M2 call trace and the M5 primitive-site list are kept apart exactly as in
`controllerCompositionEnvelope`: the trace has length `h_br + 4`, and the four
frozen major calls of lines 2381--2384 are the set `major`.

General in the controller table, the trace, the choice of major sites, the
envelope, and both side conditions. -/
theorem literalValidBranchBound
    {SourceOut : Prop} {nEps nMat n CK hbr Cbar rbar U inLen outLen time : ℕ}
    {x y s : ℕ → ℕ} (major : Finset ℕ)
    (hmajor : major ⊆ Finset.range (hbr + 4)) (hcard : major.card = 4)
    (hn : max nEps nMat ≤ n) (hvalid : SourceOut)
    (hM2 : max nEps nMat ≤ n → SourceOut →
      time ≤ CK * (1 + inLen + outLen
        + ∑ j ∈ Finset.range (hbr + 4), (x j + y j + s j)))
    (hU : 1 ≤ U) (hin : inLen ≤ U) (hout : outLen ≤ U)
    (hx : ∀ j ∈ Finset.range (hbr + 4), x j ≤ U)
    (hy : ∀ j ∈ Finset.range (hbr + 4), y j ≤ U)
    (hsmajor : ∀ j ∈ major, s j ≤ U)
    (hsprim : ∀ j ∈ Finset.range (hbr + 4) \ major,
      s j ≤ 2 * Cbar * 3 ^ rbar * U ^ (rbar + 1)) :
    time ≤ controllerRuntime CK hbr Cbar rbar U :=
  le_trans (hM2 hn hvalid)
    (controllerCompositionEnvelope major hmajor hcard hU hin hout hx hy hsmajor hsprim)

/-! ## Part 3: the frozen list codec and its one-pass streaming charge -/

/-- `eq:literal-list-streaming-constant` (frozen display lines 2488--2491):
`C_list = 20(C_move + C_mark + C_copy + 1)`. -/
def listConstant (Cmove Cmark Ccopy : ℕ) : ℕ := 20 * (Cmove + Cmark + Ccopy + 1)

/-- **Aux 5 (the frozen list-length inequality).**

`eq:literal-list-codec` (frozen display lines 295--299) makes the encoded list
literally `nu(t)` followed by `esc(x_j)11` for each `j < t`, so its length is
`|nu(t)| + sum_{j<t}(2|x_j| + 2)`.  Frozen line 2495 uses only the consequence
`|y| >= 2 sum_{j<t}|x_j| + 2t`, which is what is proved here.  General in the
branch count and the payload lengths. -/
theorem listCodecLength (t : ℕ) (x : ℕ → ℕ) :
    2 * (∑ j ∈ Finset.range t, x j) + 2 * t
      ≤ headerLength t + ∑ j ∈ Finset.range t, (2 * x j + 2) := by
  have hsplit : ∑ j ∈ Finset.range t, (2 * x j + 2)
      = 2 * (∑ j ∈ Finset.range t, x j) + 2 * t := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_range, mul_comm]
  omega

/-- `eq:literal-list-streaming-bound` (frozen display lines 2496--2502): all
list traversal, validation, branch copying and scratch clearing outside the
branch calls take at most `C_list(|y|+1)`, and on the S1 producer output
`|y| <= 2^{eps_* n} P_*(H)`.  General in the three literal transition-count
maxima, the encoded length, the branch envelope and the polynomial value. -/
theorem listStreamingBound {Cmove Cmark Ccopy yLen e P : ℕ} (hy : yLen ≤ e * P) :
    listConstant Cmove Cmark Ccopy * (yLen + 1)
      ≤ listConstant Cmove Cmark Ccopy * (e * P + 1) :=
  Nat.mul_le_mul le_rfl (by omega)

/-! ## Part 4: the frozen polynomial majorant (frozen lines 2450--2463) -/

/-- The frozen fixed nonnegative integer polynomial
`P_*(X) = sum_{j<=d_P} a_j X^j` (frozen lines 2452--2454), evaluated at `H`. -/
def polyEval (a : ℕ → ℕ) (dP H : ℕ) : ℕ := ∑ j ∈ Finset.range (dP + 1), a j * H ^ j

/-- The frozen gap-call envelope (frozen lines 2361--2362):
`B_gap(n) = Q_*(n + B_Phi(n) + 1)`.

`Q_*` is the source package's polynomial datum: `thm:encoded-source-package`
(frozen lines 1246--1247) supplies `P_epsilon` and `Q_epsilon` as
*coefficientwise nonnegative integer polynomials*, and S2 (frozen lines
1277--1280) charges the gap machine `Q_epsilon(n + |enc_3CNF(Phi_j)| + 1)`
steps.  So `B_gap` is a polynomial **evaluation**, landed with the same
`polyEval` used for `P_*`, and the coefficient sequence `q` with degree bound
`dQ` is carried as an opaque binder (GAP-EXPOSED 1: the machine that realizes
`Q_*` is not modelled). -/
def gapCodeBound (q : ℕ → ℕ) (dQ n bPhi : ℕ) : ℕ := polyEval q dQ (n + bPhi + 1)

/-- The frozen coefficient majorant `a_P = 1 + sum_{j<=d_P} a_j`
(frozen line 2459). -/
def polyMajorant (a : ℕ → ℕ) (dP : ℕ) : ℕ := 1 + ∑ j ∈ Finset.range (dP + 1), a j

/-- The frozen exponent `r_P = max{1, d_P}` (frozen line 2460); see reading
note N5. -/
def polyExponent (dP : ℕ) : ℕ := max 1 dP

/-- **Aux 6 (the frozen polynomial majorant).**

Frozen line 2463: "Then `P_*(H) <= a_P (H+1)^{r_P}` for every `H >= 0`."
General in the coefficient sequence, the degree and the argument. -/
theorem polyMajorant_bound (a : ℕ → ℕ) (dP H : ℕ) :
    polyEval a dP H ≤ polyMajorant a dP * (H + 1) ^ polyExponent dP := by
  have hterm : ∀ j ∈ Finset.range (dP + 1),
      a j * H ^ j ≤ a j * (H + 1) ^ polyExponent dP := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have hj' : j ≤ polyExponent dP := by
      simp only [polyExponent]
      omega
    have h1 : H ^ j ≤ (H + 1) ^ j := Nat.pow_le_pow_left (by omega) j
    have h2 : (H + 1) ^ j ≤ (H + 1) ^ polyExponent dP :=
      Nat.pow_le_pow_right (by omega) hj'
    exact Nat.mul_le_mul le_rfl (le_trans h1 h2)
  calc polyEval a dP H
      ≤ ∑ j ∈ Finset.range (dP + 1), a j * (H + 1) ^ polyExponent dP :=
        Finset.sum_le_sum hterm
    _ = (∑ j ∈ Finset.range (dP + 1), a j) * (H + 1) ^ polyExponent dP := by
        rw [← Finset.sum_mul]
    _ ≤ polyMajorant a dP * (H + 1) ^ polyExponent dP := by
        refine Nat.mul_le_mul ?_ le_rfl
        simp only [polyMajorant]
        omega

/-- **Aux 7 (the frozen `max{1, d_P}` guard is a positivity guard).**

Reading note N5: the guard is what stops a constant polynomial from collapsing
the frozen final exponent.  General in the degree. -/
theorem polyExponent_is_positive (dP : ℕ) : 1 ≤ polyExponent dP := by
  simp only [polyExponent]
  omega

/-! ## Part 5: the two frozen cutoffs (`eq:literal-final-cutoff`) -/

/-- The frozen "least element of a nonempty set of naturals", used twice in
`eq:literal-final-cutoff` (frozen display lines 2441--2449, introduced at
frozen lines 2439--2440): "Consequently the
following two sets are nonempty, so their least elements are defined."  The
frozen sets are not decidable predicates, so the classical decidability
instance is supplied explicitly. -/
noncomputable def leastIndexWith (p : ℕ → Prop) (h : ∃ N, p N) : ℕ :=
  @Nat.find p (Classical.decPred p) h

theorem leastIndexWith_spec (p : ℕ → Prop) (h : ∃ N, p N) : p (leastIndexWith p h) :=
  @Nat.find_spec p (Classical.decPred p) h

theorem leastIndexWith_min (p : ℕ → Prop) (h : ∃ N, p N) {N : ℕ} (hN : p N) :
    leastIndexWith p h ≤ N :=
  @Nat.find_min' p (Classical.decPred p) h N hN

/-- **Aux 8 (the frozen `n_L` set is nonempty, from banked material).**

`eq:literal-final-cutoff`, first line (frozen line 2442):
`n_L = min{N >= 1 : for every n >= N, L(n) >= 1}`.  The frozen text obtains
nonemptiness from `L(n) -> infinity`; here it is obtained from the banked
finite form `slowDiagonal_monotone_unbounded`, whose second conjunct says every
`n >= V_K` has `K <= L(n)`.  Taking `K = 1` gives the threshold
`max(1, V_1)`.  This set is therefore **not** hypothesized.  General in the
clock and the cutoff function. -/
theorem positiveIndexTailExists {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep) :
    ∃ N, 1 ≤ N ∧ ∀ n, N ≤ n → 1 ≤ slowIndex V n := by
  refine ⟨max 1 (V 1), le_max_left _ _, ?_⟩
  intro n hn
  exact (slowDiagonal_monotone_unbounded hg).2 1 n (le_trans (le_max_right 1 (V 1)) hn)

/-- The frozen `n_L` of `eq:literal-final-cutoff`. -/
noncomputable def slowIndexCutoff {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep) : ℕ :=
  leastIndexWith (fun N => 1 ≤ N ∧ ∀ n, N ≤ n → 1 ≤ slowIndex V n)
    (positiveIndexTailExists hg)

/-- The two defining properties of the frozen `n_L`. -/
theorem slowIndexCutoff_spec {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep) :
    1 ≤ slowIndexCutoff hg ∧ ∀ n, slowIndexCutoff hg ≤ n → 1 ≤ slowIndex V n :=
  leastIndexWith_spec _ (positiveIndexTailExists hg)

/-- Minimality of the frozen `n_L`. -/
theorem slowIndexCutoff_min {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep)
    {N : ℕ} (hN : 1 ≤ N ∧ ∀ n, N ≤ n → 1 ≤ slowIndex V n) :
    slowIndexCutoff hg ≤ N :=
  leastIndexWith_min _ (positiveIndexTailExists hg) hN

/-- `eq:literal-final-cutoff`, second line (frozen lines 2443--2447): the
frozen `n_tail` set,
`{N >= max{n_eps_*, n_mat, n_L} : for every n >= N, R_br(n) <= 2^{eps_* n}}`.

Both clauses are printed in the frozen display; neither restates the other, and
neither is a derived telescope. -/
def TailCutoffSet (nEps nMat nL : ℕ) (Rbr E : ℕ → ℕ) (N : ℕ) : Prop :=
  max (max nEps nMat) nL ≤ N ∧ ∀ n, N ≤ n → Rbr n ≤ E n

/-- The frozen `n_tail`.  Its defining set's nonemptiness is the named
hypothesis `h`, because the frozen justification is
`eq:literal-branch-subexponential`, which is GAP-EXPOSED 3;
`tailCutoffSet_can_be_empty` shows the hypothesis is not free. -/
noncomputable def tailCutoff (nEps nMat nL : ℕ) (Rbr E : ℕ → ℕ)
    (h : ∃ N, TailCutoffSet nEps nMat nL Rbr E N) : ℕ :=
  leastIndexWith _ h

theorem tailCutoff_spec (nEps nMat nL : ℕ) (Rbr E : ℕ → ℕ)
    (h : ∃ N, TailCutoffSet nEps nMat nL Rbr E N) :
    TailCutoffSet nEps nMat nL Rbr E (tailCutoff nEps nMat nL Rbr E h) :=
  leastIndexWith_spec _ h

theorem tailCutoff_min (nEps nMat nL : ℕ) (Rbr E : ℕ → ℕ)
    (h : ∃ N, TailCutoffSet nEps nMat nL Rbr E N) {N : ℕ}
    (hN : TailCutoffSet nEps nMat nL Rbr E N) :
    tailCutoff nEps nMat nL Rbr E h ≤ N :=
  leastIndexWith_min _ h hN

/-- The four guard consequences of frozen lines 2444--2445: because the frozen
`n_tail` set is constrained to lie above `max{n_eps_*, n_mat, n_L}`, every
`n >= n_tail` already satisfies the three earlier cutoffs, and the tail
inequality holds there.  They are therefore **not** re-hypothesized at any use
site. -/
theorem tailCutoff_guards (nEps nMat nL : ℕ) (Rbr E : ℕ → ℕ)
    (h : ∃ N, TailCutoffSet nEps nMat nL Rbr E N) {n : ℕ}
    (hn : tailCutoff nEps nMat nL Rbr E h ≤ n) :
    nEps ≤ n ∧ nMat ≤ n ∧ nL ≤ n ∧ Rbr n ≤ E n := by
  obtain ⟨hge, htail⟩ := tailCutoff_spec nEps nMat nL Rbr E h
  refine ⟨?_, ?_, ?_, htail n hn⟩
  · exact le_trans (le_trans (le_trans (le_max_left nEps nMat) (le_max_left _ nL)) hge) hn
  · exact le_trans (le_trans (le_trans (le_max_right nEps nMat) (le_max_left _ nL)) hge) hn
  · exact le_trans (le_trans (le_max_right _ nL) hge) hn

/-- **The frozen allowance gap fits on the whole tail.**

This is the sole reason `n_L` is one of the three lower constraints of the
frozen `n_tail` set: past `n_L` the guard `1 <= L(n)` of `eq:alpha-gap-fit`
holds, so the banked `AlphaAllowance.alphaGapFit` applies at every tail index.
It is the *fit*, not the promise-case contradiction (GAP-EXPOSED 6).  General
in the clock, the cutoff function, and all four cutoffs. -/
theorem tailAllowanceGapFit {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep)
    {nEps nMat : ℕ} {Rbr E : ℕ → ℕ}
    (h : ∃ N, TailCutoffSet nEps nMat (slowIndexCutoff hg) Rbr E N) {n : ℕ}
    (hn : tailCutoff nEps nMat (slowIndexCutoff hg) Rbr E h ≤ n) :
    2 * alphaAllowance V (tCommon V n) < slowIndex V n := by
  obtain ⟨-, -, hnL, -⟩ := tailCutoff_guards nEps nMat (slowIndexCutoff hg) Rbr E h hn
  exact alphaGapFit hg n ((slowIndexCutoff_spec hg).2 n hnL)

/-! ## Part 6: the top controller and the frozen final witnesses -/

/-- `r_SAT = max{r_P, r_top}` (frozen line 2560). -/
def satExponent (dP rtop : ℕ) : ℕ := max (polyExponent dP) rtop

/-- `K_SAT = C_top(a_P + 2)` (frozen line 2561). -/
def satConstant (Ctop aP : ℕ) : ℕ := Ctop * (aP + 2)

/-- **The frozen factor 16 dominates the fibre constant.**

Frozen lines 2428--2430 and 2568--2570: the numerical factor 16 "deliberately
dominates the four major call sites, the controller input and output terms, and
the finite primitive-call list".  This records that frozen sentence in the one
form it is used in: `C_top` is at least twice the fibre maximum `Cbar_top`.
Reading note N4: after the `cc-t1x-r1` repair the top-controller derivation
carries the `C_K` factor of `eq:machine-composition-upper` explicitly, so it
consumes the dominance in the *expanded* coefficient form inside
`topControllerEnvelope`'s `hcA` (where the `80 Cbar_top 3^{rbar_top}` summand of
`C_top` absorbs the `+1` of `eq:literal-list-streaming-bound`) rather than
through this lemma.  The lemma is therefore a standalone kernel record of the
frozen sentence, not a step of that proof.  General in the controller table. -/
theorem frozenSixteenDominates {CK h Cbar rbar : ℕ} (hCK : 1 ≤ CK) :
    2 * Cbar ≤ controllerConstant CK h Cbar rbar := by
  have hP : 1 ≤ 3 ^ rbar := Nat.one_le_pow _ _ (by norm_num)
  simp only [controllerConstant]
  calc 2 * Cbar ≤ 16 * 1 * 5 * (Cbar + 1) * 1 := by omega
    _ ≤ 16 * CK * (h + 5) * (Cbar + 1) * 3 ^ rbar :=
        Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hCK) (by omega)) le_rfl) hP

theorem one_le_controllerConstant {CK h Cbar rbar : ℕ} (hCK : 1 ≤ CK) :
    1 ≤ controllerConstant CK h Cbar rbar := by
  have := frozenSixteenDominates (CK := CK) (h := h) (Cbar := Cbar) (rbar := rbar) hCK
  have hP : 1 ≤ 3 ^ rbar := Nat.one_le_pow _ _ (by norm_num)
  simp only [controllerConstant] at *
  calc (1 : ℕ) ≤ 16 * 1 * 5 * (0 + 1) * 1 := by norm_num
    _ ≤ 16 * CK * (h + 5) * (Cbar + 1) * 3 ^ rbar :=
        Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hCK) (by omega)) (by omega)) hP

/-- `eq:literal-top-controller-bound` (frozen display lines 2549--2555).

The frozen derivation at lines 2541--2548 is "the same substitution used for
`eq:literal-branch-runtime`, now using the S1 time and output bounds, the
one-time list charge `eq:literal-list-streaming-bound`, and the M2 sum of the
`t` copied branch inputs and branch runtimes".  So the binder list below is the
input list of *that* substitution, term by term:

* the outer `C_K` factor of `eq:machine-composition-upper` is present
  (`htime`), together with its `1 + |x| + |out|` head, where `|x| = H` is the
  encoded formula and `outLen` is the composite's own output;
* the `A_spar^{eps_*}` call is priced by the **frozen S1 bound**
  (`thm:encoded-source-package`, S1, frozen lines 1267--1272): its step count
  **and** its exact `List(CNF3)`-encoded output length are *both* at most
  `2^{eps_* n} P_*(H)`, which is the second frozen summand of the conclusion.
  There is no `Cbar_top`-entry hypothesis for it, because
  `Cbar_top = max(1, C_list, max_{rho in R_top} C_rho)` (frozen lines
  2532--2534) ranges over `C_list` and the **M5 primitive** sites, and
  `A_spar^{eps_*}` is a major subcall, not one of those entries: the parked
  reading that `Cs1 <= Cbar_top` is a frozen fact was wrong and is not restated
  here;
* `hClist` *is* a frozen fact, `C_list` being a printed entry of that maximum,
  and `hlist` is `eq:literal-list-streaming-bound`;
* the `t` branch calls contribute their copied inputs, their outputs and their
  runtimes.  The copied inputs are summed **once** (`hbrInSum`), because the
  payloads are disjoint substrings of the S1 output: that is exactly the frozen
  list-length inequality of line 2495 recorded in `listCodecLength`.  Bounding
  each payload separately by the whole output would square the frozen
  `2^{eps_* n}P_*(H)` term.  Branch outputs are bounded by branch transition
  counts (frozen line 2415, "an output has at most one bit per transition");
* the M5 primitive sites of `R_top` are call sites of the same M2 trace, so
  `eq:machine-composition-upper` charges each of them the **full triple**
  `|x_j| + |y_j| + s_j` (frozen display lines 255--264, sum term over every
  `j < h`).  Their input and output lengths are at the top controller's own
  envelope `H + 1` (`hprimIn`, `hprimOut`; frozen lines 2523--2526 place
  `R_top` outside both the separately charged branch controller and the
  separately charged streaming layer), and their transition counts are priced
  by `primitiveCallEnvelope` at that same envelope (`hprim`).  Together they
  give the frozen `(H+1)^{r_top}` summand.  Charging only `s_j` here -- as the
  parked `cc-t1x-r1` round did -- drops `sum_{j<h_top}(|x_j| + |y_j|)` from the
  frozen display and makes the lemma uninstantiable at the composite it names;
  inflating `prim j` to the whole triple instead would make the
  `primitiveCallEnvelope` bound false, so the three legs are three binders
  (repair `cc-t1x-r2`).  This is exactly the shape
  `controllerCompositionEnvelope` already carries on its own trace.

General in the controller table, the primitive-site count, the branch count,
the branch bound, the encoded input length and the polynomial value. -/
theorem topControllerEnvelope
    {CK htop Cbar rbar Clist H e P t Rbr outLen s1In s1Out s1Cost listCost time : ℕ}
    {brIn brOut br primIn primOut prim : ℕ → ℕ}
    (hClist : Clist ≤ Cbar)
    (hout : outLen ≤ H + 1) (hs1in : s1In ≤ H + 1)
    (hs1out : s1Out ≤ e * P) (hs1time : s1Cost ≤ e * P)
    (hlist : listCost ≤ Clist * (e * P + 1))
    (hbrInSum : ∑ j ∈ Finset.range t, brIn j ≤ e * P)
    (hbrOut : ∀ j ∈ Finset.range t, brOut j ≤ br j)
    (ht : t ≤ e) (hbr : ∀ j ∈ Finset.range t, br j ≤ Rbr)
    (hprimIn : ∀ j ∈ Finset.range htop, primIn j ≤ H + 1)
    (hprimOut : ∀ j ∈ Finset.range htop, primOut j ≤ H + 1)
    (hprim : ∀ j ∈ Finset.range htop,
      prim j ≤ 2 * Cbar * 3 ^ rbar * (H + 1) ^ controllerExponent rbar)
    (htime : time ≤ CK * (1 + H + outLen + (s1In + s1Out + s1Cost) + listCost
        + ∑ j ∈ Finset.range t, (brIn j + brOut j + br j)
        + ∑ j ∈ Finset.range htop, (primIn j + primOut j + prim j))) :
    time ≤ controllerConstant CK htop Cbar rbar
             * ((H + 1) ^ controllerExponent rbar + e * P + e * Rbr) := by
  have hPw : 1 ≤ 3 ^ rbar := Nat.one_le_pow _ _ (by norm_num)
  have hA1 : 1 ≤ (H + 1) ^ controllerExponent rbar := Nat.one_le_pow _ _ (by omega)
  have hHA : H + 1 ≤ (H + 1) ^ controllerExponent rbar := by
    calc H + 1 = (H + 1) ^ 1 := (pow_one _).symm
      _ ≤ (H + 1) ^ controllerExponent rbar :=
        Nat.pow_le_pow_right (by omega) (by simp [controllerExponent])
  have hHA' : H ≤ (H + 1) ^ controllerExponent rbar := by omega
  have hOutA : outLen ≤ (H + 1) ^ controllerExponent rbar := le_trans hout hHA
  have hS1inA : s1In ≤ (H + 1) ^ controllerExponent rbar := le_trans hs1in hHA
  have hlist' : listCost
      ≤ Cbar * (e * P) + Cbar * (H + 1) ^ controllerExponent rbar := by
    calc listCost ≤ Clist * (e * P + 1) := hlist
      _ ≤ Cbar * (e * P + 1) := Nat.mul_le_mul hClist le_rfl
      _ = Cbar * (e * P) + Cbar * 1 := by ring
      _ ≤ Cbar * (e * P) + Cbar * (H + 1) ^ controllerExponent rbar :=
        Nat.add_le_add le_rfl (Nat.mul_le_mul le_rfl hA1)
  have hbrsum : ∑ j ∈ Finset.range t, (brIn j + brOut j + br j)
      ≤ e * P + 2 * (e * Rbr) := by
    have hdist : ∑ j ∈ Finset.range t, (brIn j + brOut j + br j)
        = (∑ j ∈ Finset.range t, brIn j)
          + ∑ j ∈ Finset.range t, (brOut j + br j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hrest : ∑ j ∈ Finset.range t, (brOut j + br j) ≤ 2 * (e * Rbr) := by
      calc ∑ j ∈ Finset.range t, (brOut j + br j)
          ≤ ∑ _j ∈ Finset.range t, (2 * Rbr) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            have h1 := hbrOut j hj
            have h2 := hbr j hj
            omega
        _ = t * (2 * Rbr) := by simp [Finset.sum_const, Finset.card_range, mul_comm]
        _ ≤ e * (2 * Rbr) := Nat.mul_le_mul ht le_rfl
        _ = 2 * (e * Rbr) := by ring
    omega
  have hprimsum : ∑ j ∈ Finset.range htop, (primIn j + primOut j + prim j)
      ≤ 2 * htop * (H + 1) ^ controllerExponent rbar
        + 2 * htop * Cbar * 3 ^ rbar * (H + 1) ^ controllerExponent rbar := by
    calc ∑ j ∈ Finset.range htop, (primIn j + primOut j + prim j)
        ≤ ∑ _j ∈ Finset.range htop,
            ((H + 1) ^ controllerExponent rbar + (H + 1) ^ controllerExponent rbar
              + 2 * Cbar * 3 ^ rbar * (H + 1) ^ controllerExponent rbar) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact Nat.add_le_add
            (Nat.add_le_add (le_trans (hprimIn j hj) hHA) (le_trans (hprimOut j hj) hHA))
            (hprim j hj)
      _ = htop * ((H + 1) ^ controllerExponent rbar + (H + 1) ^ controllerExponent rbar
              + 2 * Cbar * 3 ^ rbar * (H + 1) ^ controllerExponent rbar) := by
          simp [Finset.sum_const, Finset.card_range, mul_comm]
      _ = 2 * htop * (H + 1) ^ controllerExponent rbar
            + 2 * htop * Cbar * 3 ^ rbar * (H + 1) ^ controllerExponent rbar := by ring
  have hcA : 4 + Cbar + 2 * htop + 2 * htop * Cbar * 3 ^ rbar
      ≤ 16 * (htop + 5) * (Cbar + 1) * 3 ^ rbar := by
    have e1 : 16 * (htop + 5) * (Cbar + 1) * 3 ^ rbar
        = 16 * htop * Cbar * 3 ^ rbar + 16 * htop * 3 ^ rbar
          + 80 * Cbar * 3 ^ rbar + 80 * 3 ^ rbar := by ring
    have b1 : (4 : ℕ) ≤ 80 * 3 ^ rbar := by
      calc (4 : ℕ) ≤ 80 * 1 := by norm_num
        _ ≤ 80 * 3 ^ rbar := Nat.mul_le_mul le_rfl hPw
    have b2 : Cbar ≤ 80 * Cbar * 3 ^ rbar := by
      calc Cbar = 1 * Cbar * 1 := by ring
        _ ≤ 80 * Cbar * 3 ^ rbar :=
          Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) le_rfl) hPw
    have b3 : 2 * htop * Cbar * 3 ^ rbar ≤ 16 * htop * Cbar * 3 ^ rbar :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) le_rfl
    have b4 : 2 * htop ≤ 16 * htop * 3 ^ rbar := by
      calc 2 * htop ≤ 16 * htop * 1 := by omega
        _ ≤ 16 * htop * 3 ^ rbar := Nat.mul_le_mul le_rfl hPw
    rw [e1]
    omega
  have hcB : 3 + Cbar ≤ 16 * (htop + 5) * (Cbar + 1) * 3 ^ rbar :=
    le_trans (by omega) hcA
  have hcD : 2 ≤ 16 * (htop + 5) * (Cbar + 1) * 3 ^ rbar :=
    le_trans (by omega) hcA
  have hbig : 1 + H + outLen + (s1In + s1Out + s1Cost) + listCost
        + (∑ j ∈ Finset.range t, (brIn j + brOut j + br j))
        + ∑ j ∈ Finset.range htop, (primIn j + primOut j + prim j)
      ≤ (4 + Cbar + 2 * htop + 2 * htop * Cbar * 3 ^ rbar)
          * (H + 1) ^ controllerExponent rbar
        + (3 + Cbar) * (e * P) + 2 * (e * Rbr) := by
    calc 1 + H + outLen + (s1In + s1Out + s1Cost) + listCost
          + (∑ j ∈ Finset.range t, (brIn j + brOut j + br j))
          + ∑ j ∈ Finset.range htop, (primIn j + primOut j + prim j)
        ≤ (H + 1) ^ controllerExponent rbar + (H + 1) ^ controllerExponent rbar
            + (H + 1) ^ controllerExponent rbar
            + ((H + 1) ^ controllerExponent rbar + e * P + e * P)
            + (Cbar * (e * P) + Cbar * (H + 1) ^ controllerExponent rbar)
            + (e * P + 2 * (e * Rbr))
            + (2 * htop * (H + 1) ^ controllerExponent rbar
              + 2 * htop * Cbar * 3 ^ rbar * (H + 1) ^ controllerExponent rbar) :=
          Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add
                  (Nat.add_le_add (Nat.add_le_add hA1 hHA') hOutA)
                  (Nat.add_le_add (Nat.add_le_add hS1inA hs1out) hs1time))
                hlist')
              hbrsum)
            hprimsum
      _ = (4 + Cbar + 2 * htop + 2 * htop * Cbar * 3 ^ rbar)
            * (H + 1) ^ controllerExponent rbar
            + (3 + Cbar) * (e * P) + 2 * (e * Rbr) := by ring
  calc time ≤ CK * (1 + H + outLen + (s1In + s1Out + s1Cost) + listCost
          + (∑ j ∈ Finset.range t, (brIn j + brOut j + br j))
          + ∑ j ∈ Finset.range htop, (primIn j + primOut j + prim j)) := htime
    _ ≤ CK * ((4 + Cbar + 2 * htop + 2 * htop * Cbar * 3 ^ rbar)
            * (H + 1) ^ controllerExponent rbar
          + (3 + Cbar) * (e * P) + 2 * (e * Rbr)) :=
        Nat.mul_le_mul le_rfl hbig
    _ ≤ CK * ((16 * (htop + 5) * (Cbar + 1) * 3 ^ rbar)
            * (H + 1) ^ controllerExponent rbar
          + (16 * (htop + 5) * (Cbar + 1) * 3 ^ rbar) * (e * P)
          + (16 * (htop + 5) * (Cbar + 1) * 3 ^ rbar) * (e * Rbr)) :=
        Nat.mul_le_mul le_rfl
          (Nat.add_le_add
            (Nat.add_le_add (Nat.mul_le_mul hcA le_rfl) (Nat.mul_le_mul hcB le_rfl))
            (Nat.mul_le_mul hcD le_rfl))
    _ = controllerConstant CK htop Cbar rbar
          * ((H + 1) ^ controllerExponent rbar + e * P + e * Rbr) := by
        simp only [controllerConstant]
        ring

/-- **Aux 9 (the frozen envelope doubling is exactly the square of the branch
envelope).**

`eq:literal-final-tail-bound` prices the tail at `2^{2 eps_* n}`, and the frozen
derivation gets it as one envelope factor from the branch count times one from
the `n_tail` cutoff of `eq:literal-final-cutoff`.  Any admissible encoding of
the envelope must therefore satisfy the squaring law: the product of two branch
envelopes **is** the frozen doubled envelope, and the doubled envelope
dominates the single one.  Candidate A satisfies both clauses at every legal
value; the rejected candidate fails the first, as
`truncatedEpsilonExponent_is_not_the_frozen_square` records.  General in the
envelope. -/
theorem envelopeSquaringLaw {e : ℕ} (he : 1 ≤ e) : e * e = e ^ 2 ∧ e ≤ e ^ 2 := by
  refine ⟨by ring, ?_⟩
  calc e = e * 1 := by ring
    _ ≤ e * e := Nat.mul_le_mul le_rfl he
    _ = e ^ 2 := by ring

/-- `eq:literal-final-tail-bound` (frozen display lines 2566--2571).

Frozen line 2564: "For every `n >= n_tail`, `eq:literal-final-cutoff` and
`eq:literal-top-controller-bound` give the exact tail bound
`time <= K_SAT 2^{2 eps_* n}(H+1)^{r_SAT}`."  The two frozen inputs are `hTop`
(`eq:literal-top-controller-bound`) and `hCut` (`R_br(n) <= 2^{eps_* n}`, the
tail clause of the frozen `n_tail` set).  The frozen exponent doubling is
literal: one factor `e` comes from the branch count and one from `hCut`, and
they are kept as the square `e^2` (GAP-EXPOSED 4, candidate ranking).

General in the controller constant, the top exponent, the polynomial, the
encoded input length, the envelope and the branch bound. -/
theorem literalFinalTailBound {Ctop rtop dP H time e Rbr : ℕ} {a : ℕ → ℕ}
    (hE : 1 ≤ e) (hCut : Rbr ≤ e)
    (hTop : time ≤ Ctop * ((H + 1) ^ rtop + e * polyEval a dP H + e * Rbr)) :
    time ≤ satConstant Ctop (polyMajorant a dP) * e ^ 2
             * (H + 1) ^ satExponent dP rtop := by
  have hA1 : 1 ≤ (H + 1) ^ satExponent dP rtop := Nat.one_le_pow _ _ (by omega)
  have he2 : 1 ≤ e ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hee : e ≤ e ^ 2 := (envelopeSquaringLaw hE).2
  have h1 : (H + 1) ^ rtop ≤ e ^ 2 * (H + 1) ^ satExponent dP rtop := by
    have hle : (H + 1) ^ rtop ≤ (H + 1) ^ satExponent dP rtop :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    calc (H + 1) ^ rtop ≤ (H + 1) ^ satExponent dP rtop := hle
      _ = 1 * (H + 1) ^ satExponent dP rtop := by ring
      _ ≤ e ^ 2 * (H + 1) ^ satExponent dP rtop := Nat.mul_le_mul he2 le_rfl
  have h2 : e * polyEval a dP H
      ≤ polyMajorant a dP * (e ^ 2 * (H + 1) ^ satExponent dP rtop) := by
    have hpe : (H + 1) ^ polyExponent dP ≤ (H + 1) ^ satExponent dP rtop :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    calc e * polyEval a dP H
        ≤ e * (polyMajorant a dP * (H + 1) ^ polyExponent dP) :=
          Nat.mul_le_mul le_rfl (polyMajorant_bound a dP H)
      _ ≤ e * (polyMajorant a dP * (H + 1) ^ satExponent dP rtop) :=
          Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hpe)
      _ ≤ e ^ 2 * (polyMajorant a dP * (H + 1) ^ satExponent dP rtop) :=
          Nat.mul_le_mul hee le_rfl
      _ = polyMajorant a dP * (e ^ 2 * (H + 1) ^ satExponent dP rtop) := by ring
  have h3 : e * Rbr ≤ e ^ 2 * (H + 1) ^ satExponent dP rtop := by
    calc e * Rbr ≤ e * e := Nat.mul_le_mul le_rfl hCut
      _ = e ^ 2 * 1 := by ring
      _ ≤ e ^ 2 * (H + 1) ^ satExponent dP rtop := Nat.mul_le_mul le_rfl hA1
  calc time ≤ Ctop * ((H + 1) ^ rtop + e * polyEval a dP H + e * Rbr) := hTop
    _ ≤ Ctop * (e ^ 2 * (H + 1) ^ satExponent dP rtop
          + polyMajorant a dP * (e ^ 2 * (H + 1) ^ satExponent dP rtop)
          + e ^ 2 * (H + 1) ^ satExponent dP rtop) :=
        Nat.mul_le_mul le_rfl (Nat.add_le_add (Nat.add_le_add h1 h2) h3)
    _ = satConstant Ctop (polyMajorant a dP) * e ^ 2
          * (H + 1) ^ satExponent dP rtop := by
        simp only [satConstant]
        ring

/-- **The frozen tail accounting, end to end.**

Composing `topControllerEnvelope` with `literalFinalTailBound` at the frozen
top-controller table gives `eq:literal-final-tail-bound` with the frozen
witnesses of `eq:literal-final-eth-witnesses`: the constant is
`K_SAT = C_top(a_P+2)` with `C_top = 16 C_{K_top}(h_top+5)(Cbar_top+1)3^{rbar_top}`,
the exponent is `r_SAT = max{r_P, r_top}` with `r_top = rbar_top + 1`, and the
envelope factor is the frozen square.

This is the literal cost accounting of `lem:literal-final-runtime` and nothing
more: it is not `thm:effective-main`, and it claims no route completion
(GAP-EXPOSED 5 and 8). -/
theorem literalFinalRuntime
    {CK htop Cbar rbar Clist H e P t Rbr outLen s1In s1Out s1Cost listCost time dP : ℕ}
    {a brIn brOut br primIn primOut prim : ℕ → ℕ}
    (hClist : Clist ≤ Cbar)
    (hE : 1 ≤ e) (hCut : Rbr ≤ e) (hP : P = polyEval a dP H)
    (hout : outLen ≤ H + 1) (hs1in : s1In ≤ H + 1)
    (hs1out : s1Out ≤ e * P) (hs1time : s1Cost ≤ e * P)
    (hlist : listCost ≤ Clist * (e * P + 1))
    (hbrInSum : ∑ j ∈ Finset.range t, brIn j ≤ e * P)
    (hbrOut : ∀ j ∈ Finset.range t, brOut j ≤ br j)
    (ht : t ≤ e) (hbr : ∀ j ∈ Finset.range t, br j ≤ Rbr)
    (hprimIn : ∀ j ∈ Finset.range htop, primIn j ≤ H + 1)
    (hprimOut : ∀ j ∈ Finset.range htop, primOut j ≤ H + 1)
    (hprim : ∀ j ∈ Finset.range htop,
      prim j ≤ 2 * Cbar * 3 ^ rbar * (H + 1) ^ controllerExponent rbar)
    (htime : time ≤ CK * (1 + H + outLen + (s1In + s1Out + s1Cost) + listCost
        + ∑ j ∈ Finset.range t, (brIn j + brOut j + br j)
        + ∑ j ∈ Finset.range htop, (primIn j + primOut j + prim j))) :
    time ≤ satConstant (controllerConstant CK htop Cbar rbar) (polyMajorant a dP) * e ^ 2
             * (H + 1) ^ satExponent dP (controllerExponent rbar) := by
  subst hP
  exact literalFinalTailBound hE hCut
    (topControllerEnvelope hClist hout hs1in hs1out hs1time hlist hbrInSum hbrOut
      ht hbr hprimIn hprimOut hprim htime)

/-! ## Part 7: non-vacuity, hypothesis consistency, and statement poles -/

/-- **Non-vacuity of `primitiveCallEnvelope` at legal parameter values**
(LANE-GATE 3).

Every binder is inhabited simultaneously at nondegenerate values: a primitive
with `C_rho = 2 <= Cbar = 3` and `r_rho = 1 <= rbar = 2`, a positive envelope
`U = 4`, and input, output and scan budget all positive and distinct.  The
conclusion is a genuine inequality between positive numbers, not `0 <= _`. -/
theorem primitiveCallEnvelope_fires :
    2 * (1 + 2 + 3) ^ 1 * (1 + 4) ≤ 2 * 3 * 3 ^ 2 * 4 ^ (2 + 1) :=
  primitiveCallEnvelope (Crho := 2) (rrho := 1) (Cbar := 3) (rbar := 2)
    (inLen := 2) (outLen := 3) (budget := 4) (U := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Non-vacuity of `controllerCompositionEnvelope` at legal parameter values**
(LANE-GATE 3).

The primitive-site list is genuinely nonempty (`h_br = 2`), so the M2 call trace
has the six sites `h_br + 4` and **both** halves of the split are nonempty: four
major sites (`major = {0,1,2,3}`) and two primitive sites.  Every subcall carries
positive input, output and transition counts, and the envelope is positive, so
the sum in the statement is a sum of positive terms rather than an empty sum. -/
theorem controllerCompositionEnvelope_fires :
    2 * (1 + 4 + 4 + ∑ _j ∈ Finset.range 6, (4 + 4 + 5))
      ≤ controllerRuntime 2 2 1 1 5 := by
  refine controllerCompositionEnvelope (CK := 2) (hbr := 2) (Cbar := 1) (rbar := 1)
    (U := 5) (inLen := 4) (outLen := 4) (x := fun _ => 4) (y := fun _ => 4)
    (s := fun _ => 5) (Finset.range 4)
    (Finset.range_subset_range.mpr (by norm_num)) (Finset.card_range 4)
    (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ _ => by norm_num)

/-- **Non-vacuity of `literalValidBranchBound` at legal parameter values**
(LANE-GATE 3).

Both frozen side conditions are inhabited at once -- a source size above both
cutoffs and a true instance of the opaque source predicate -- together with the
whole numeric bundle, so the conditional deliverable is not vacuous. -/
theorem literalValidBranchBound_fires :
    2 * (1 + 4 + 4 + ∑ _j ∈ Finset.range 6, (4 + 4 + 5))
      ≤ controllerRuntime 2 2 1 1 5 := by
  refine literalValidBranchBound (SourceOut := 1 ≤ 2) (nEps := 4) (nMat := 5) (n := 7)
    (CK := 2) (hbr := 2) (Cbar := 1) (rbar := 1) (U := 5) (inLen := 4) (outLen := 4)
    (x := fun _ => 4) (y := fun _ => 4) (s := fun _ => 5) (Finset.range 4)
    (Finset.range_subset_range.mpr (by norm_num)) (Finset.card_range 4)
    (by norm_num) (by norm_num) (fun _ _ => le_rfl) (by norm_num) (by norm_num)
    (by norm_num) (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)

/-- **Non-vacuity of the frozen `n_tail` set at legal parameter values**
(LANE-GATE 3).

The frozen set is inhabited at a nondegenerate pair: a strictly growing branch
runtime `R_br(n) = n` under a strictly growing envelope `E(n) = 2^n`.  Both
sides move with `n`, so this is not the constant-versus-constant degenerate
instance. -/
theorem tailCutoffSet_is_inhabited (nEps nMat nL : ℕ) :
    ∃ N, TailCutoffSet nEps nMat nL (fun n => n) (fun n => 2 ^ n) N := by
  refine ⟨max (max nEps nMat) nL, le_rfl, ?_⟩
  intro n _
  exact le_of_lt (Nat.lt_two_pow_self)

/-- **Statement pole: the frozen `n_tail` set can be empty.**

`eq:literal-branch-subexponential` is the frozen input that makes the set
nonempty, and it is GAP-EXPOSED 3.  This records that the nonemptiness
hypothesis is a real assumption: with `R_br(n) = 2^{2n}` against the envelope
`2^n` -- legal shapes for both -- no threshold works.  Without this pole,
`tailCutoff`'s hypothesis could be mistaken for a formality. -/
theorem tailCutoffSet_can_be_empty :
    ¬ ∃ N, TailCutoffSet 0 0 0 (fun n => 2 ^ (2 * n)) (fun n => 2 ^ n) N := by
  rintro ⟨N, -, h⟩
  have hle := h (N + 1) (by omega)
  have hlt : (2 : ℕ) ^ (N + 1) < 2 ^ (2 * (N + 1)) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  simp only at hle
  omega

/-- **Statement pole: the trivial threshold is not a witness for `n_L`.**

`positiveIndexTailExists` is an existential over thresholds.  At the banked
witness clock the candidate `N = 0` fails, because the banked
`slowIndex_zero_is_attained` gives `L(0) = 0` there.  So the frozen `n_L` is a
genuine search and not a restatement of the banked unboundedness.  General in
the cutoff function. -/
theorem zeroThresholdIsNotATailWitness (nstep : ℕ → ℕ) :
    ¬ (∀ n, 0 ≤ n → 1 ≤ slowIndex (witnessClock nstep) n) := by
  intro h
  have := h 0 (Nat.zero_le 0)
  have hzero := (slowIndex_zero_is_attained nstep).1
  omega

/-- **Non-vacuity of `tailAllowanceGapFit` at legal parameter values**
(LANE-GATE 3).

The full bundle is inhabited at once: the banked `witnessClock_gates` supply
the frozen clock gates, `tailCutoffSet_is_inhabited` supplies a nondegenerate
frozen `n_tail` set, and the conclusion is stated at the cutoff itself.
General in the cutoff function and both machine cutoffs. -/
theorem tailAllowanceGapFit_fires (nstep : ℕ → ℕ) (nEps nMat : ℕ) :
    2 * alphaAllowance (witnessClock nstep)
        (tCommon (witnessClock nstep)
          (tailCutoff nEps nMat (slowIndexCutoff (witnessClock_gates nstep))
            (fun n => n) (fun n => 2 ^ n)
            (tailCutoffSet_is_inhabited nEps nMat
              (slowIndexCutoff (witnessClock_gates nstep)))))
      < slowIndex (witnessClock nstep)
          (tailCutoff nEps nMat (slowIndexCutoff (witnessClock_gates nstep))
            (fun n => n) (fun n => 2 ^ n)
            (tailCutoffSet_is_inhabited nEps nMat
              (slowIndexCutoff (witnessClock_gates nstep)))) :=
  tailAllowanceGapFit (witnessClock_gates nstep) _ le_rfl

/-- **Hypothesis consistency for `literalFinalRuntime`** (the kernel form of the
"attempt to derive `False` from the full hypothesis bundle" check).

Every binder of the headline theorem is discharged simultaneously at legal,
nondegenerate values: a genuinely nonempty branch list (`t = 2`) under a branch
envelope `e = 4` that strictly exceeds it, a positive branch bound
`R_br = 3 <= e`, a nonempty M5 primitive-site list at the top controller
(`h_top = 2`), a degree-one polynomial with positive coefficients, a positive
encoded length `H = 2`, and positive S1 step, S1 output, streaming, branch-input
and primitive charges -- with the copied branch inputs summing to `10`, strictly
inside the frozen `2^{eps_* n}P_*(H) = 12`, so the single-count list constraint
is live rather than degenerate.  After the `cc-t1x-r2` repair the primitive
sites also carry **nonzero** input and output legs (`primIn = primOut = 3`, at
the top envelope `H + 1 = 3`), so the witness certifies the corrected
`eq:machine-composition-upper` telescope rather than the truncated one: the
primitive block now contributes `26` instead of `14` and the running time is
re-tightened to `103`.  The M2 factor `C_K` is a genuine multiplier and is
recorded positive.  A simultaneous witness is a proof that the bundle is
consistent, so the deliverable is not vacuous. -/
theorem literalFinalRuntime_hypotheses_consistent :
    ∃ (CK htop Cbar rbar Clist H e P t Rbr outLen s1In s1Out s1Cost listCost
        time dP : ℕ) (a brIn brOut br primIn primOut prim : ℕ → ℕ),
      Clist ≤ Cbar ∧ 1 ≤ e ∧ Rbr ≤ e ∧ P = polyEval a dP H ∧
      outLen ≤ H + 1 ∧ s1In ≤ H + 1 ∧ s1Out ≤ e * P ∧ s1Cost ≤ e * P ∧
      listCost ≤ Clist * (e * P + 1) ∧
      (∑ j ∈ Finset.range t, brIn j) ≤ e * P ∧
      (∀ j ∈ Finset.range t, brOut j ≤ br j) ∧
      t ≤ e ∧ (∀ j ∈ Finset.range t, br j ≤ Rbr) ∧
      (∀ j ∈ Finset.range htop, primIn j ≤ H + 1) ∧
      (∀ j ∈ Finset.range htop, primOut j ≤ H + 1) ∧
      (∀ j ∈ Finset.range htop,
        prim j ≤ 2 * Cbar * 3 ^ rbar * (H + 1) ^ controllerExponent rbar) ∧
      time ≤ CK * (1 + H + outLen + (s1In + s1Out + s1Cost) + listCost
        + (∑ j ∈ Finset.range t, (brIn j + brOut j + br j))
        + ∑ j ∈ Finset.range htop, (primIn j + primOut j + prim j)) ∧
      1 ≤ CK ∧ 1 ≤ time ∧ (∀ j ∈ Finset.range htop, 1 ≤ primIn j ∧ 1 ≤ primOut j) := by
  refine ⟨1, 2, 2, 1, 2, 2, 4, 3, 2, 3, 3, 3, 10, 12, 26, 103, 1,
    fun _ => 1, fun _ => 5, fun _ => 2, fun _ => 3, fun _ => 3, fun _ => 3,
    fun _ => 7, ?_⟩
  norm_num [polyEval, controllerExponent, Finset.sum_range_succ]

/-- **The frozen conclusion fires at those values.**

The headline theorem applied to the consistent bundle above, so the frozen
final display is exhibited at legal, nondegenerate parameter values rather than
asserted in general only. -/
theorem literalFinalRuntime_fires :
    (103 : ℕ) ≤ satConstant (controllerConstant 1 2 2 1) (polyMajorant (fun _ => 1) 1) * 4 ^ 2
             * (2 + 1) ^ satExponent 1 (controllerExponent 1) := by
  refine literalFinalRuntime (CK := 1) (htop := 2) (Cbar := 2) (rbar := 1)
    (Clist := 2) (H := 2) (e := 4) (P := 3) (t := 2) (Rbr := 3) (outLen := 3)
    (s1In := 3) (s1Out := 10) (s1Cost := 12) (listCost := 26) (time := 103) (dP := 1)
    (a := fun _ => 1) (brIn := fun _ => 5) (brOut := fun _ => 2) (br := fun _ => 3)
    (primIn := fun _ => 3) (primOut := fun _ => 3) (prim := fun _ => 7)
    le_rfl (by norm_num) (by norm_num) ?_ le_rfl le_rfl (by norm_num) (by norm_num)
    (by norm_num) ?_ (fun _ _ => by norm_num) (by norm_num) (fun _ _ => le_rfl)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ _ => by norm_num [controllerExponent]) ?_
  · norm_num [polyEval, Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

/-- **Statement pole: the frozen constant `K_SAT = C_top(a_P+2)` is not slack.**

Dropping the frozen `(a_P + 2)` factor -- i.e. bounding by `C_top e^2
(H+1)^{r_SAT}` alone -- is false at legal values: with `C_top = 1`, the
degree-one all-ones polynomial (`a_P = 3`, `r_P = 1`), `r_top = 1`, `H = 0`,
`e = 1` and `R_br = 1`, the frozen top-controller bound is `3` while the
constant-free bound is `1`.  The frozen `K_SAT` is `5`, which does hold. -/
theorem satConstant_factor_is_needed :
    polyMajorant (fun _ => 1) 1 = 3 ∧
    (1 : ℕ) * ((0 + 1) ^ 1 + 1 * polyEval (fun _ => 1) 1 0 + 1 * 1) = 3 ∧
    ¬ ((3 : ℕ) ≤ 1 * 1 ^ 2 * (0 + 1) ^ satExponent 1 1) ∧
    (3 : ℕ) ≤ satConstant 1 (polyMajorant (fun _ => 1) 1) * 1 ^ 2
        * (0 + 1) ^ satExponent 1 1 := by
  refine ⟨by simp [polyMajorant], ?_, ?_, ?_⟩
  · simp [polyEval, Finset.sum_range_succ]
  · simp [satExponent, polyExponent]
  · simp [satConstant, polyMajorant, satExponent, polyExponent]

/-- **Statement pole: the frozen exponent doubling is not slack.**

`eq:literal-final-tail-bound` reads `K_SAT 2^{2 eps_* n}(H+1)^{r_SAT}`, with one
envelope factor from the branch count and one from the `n_tail` cutoff.  A
single factor is not enough: with `K_SAT`-shaped data `C_top = 1`, the zero
polynomial of degree zero (`a_P = 1`), `r_top = 1`, `H = 0`, `e = 3` and
`R_br = 3`, the frozen top-controller bound is `1 + 0 + 9 = 10`, which exceeds
the single-envelope value `C_top(a_P+2) e (H+1)^{r_SAT} = 9`, while the frozen
square gives `27`. -/
theorem frozenSquare_is_needed :
    (1 : ℕ) * ((0 + 1) ^ 1 + 3 * polyEval (fun _ => 0) 0 0 + 3 * 3) = 10 ∧
    ¬ ((10 : ℕ) ≤ satConstant 1 (polyMajorant (fun _ => 0) 0) * 3
        * (0 + 1) ^ satExponent 0 1) ∧
    (10 : ℕ) ≤ satConstant 1 (polyMajorant (fun _ => 0) 0) * 3 ^ 2
        * (0 + 1) ^ satExponent 0 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [polyEval]
  · simp [satConstant, polyMajorant, satExponent, polyExponent]
  · simp [satConstant, polyMajorant, satExponent, polyExponent]

/-- **Candidate B refuted in the kernel: the truncated rational exponent is not
the frozen square.**

The rejected encoding writes the frozen branch envelope `2^{eps_* n}` as
`2 ^ (epsNum * n / epsDen)` with truncated natural division.  At
`eps_* = 1/2` and `n = 1` the product of two such envelopes is `1`, while the
frozen `2^{2 eps_* n}` is `2`.  Landing B would therefore have replaced the
frozen tail bound by a strictly stronger one -- an over-strong conclusion that
typechecks perfectly.  Candidate A carries the envelope abstractly and keeps
the doubling as a square, so no such collapse is possible. -/
theorem truncatedEpsilonExponent_is_not_the_frozen_square :
    (2 : ℕ) ^ (1 * 1 / 2) * 2 ^ (1 * 1 / 2) = 1 ∧ (2 : ℕ) ^ (2 * 1 * 1 / 2) = 2 := by
  refine ⟨by norm_num, by norm_num⟩

/-- **Statement pole (repair 1): the M2 call trace is not the M5 primitive-site
list.**

Round 1 of this tranche bound both roles to one Lean variable.  The two
readings are *different frozen constants*, and a green build sees neither: at
the smallest legal table (`C_K = 1`, `h_br = 0`, `Cbar_br = 0`,
`rbar_br = 0`) the round-1 reading at the trace length `h_br + 4` prices the
controller at `144` where the frozen `C_br` of lines 2407--2409 prices it at
`80`.  Since the frozen conclusion is an upper bound, the inflated constant
would have been a *weaker* theorem wearing the frozen name; taking instead
`h := h_br` drops the four major calls of lines 2381--2384 from the sum and
gives a bound that is not proved.  Only the split kept by
`controllerCompositionEnvelope` lands the frozen constant. -/
theorem traceLengthIsNotThePrimitiveSiteCount :
    controllerConstant 1 (0 + 4) 0 0 = 144 ∧ controllerConstant 1 0 0 0 = 80 ∧
      controllerConstant 1 (0 + 4) 0 0 ≠ controllerConstant 1 0 0 0 := by
  refine ⟨by norm_num [controllerConstant], by norm_num [controllerConstant],
    by norm_num [controllerConstant]⟩

/-- **Statement pole (repair 2): a per-branch payload bound is not the frozen
list bound.**

Reading note N7.  `topControllerEnvelope` bounds the copied branch inputs by
`hbrInSum`, a bound on their **sum**, because the payloads are disjoint
substrings of one S1 output.  Bounding each payload separately by that same
output length is a strictly different hypothesis: at `t = 2`, `e = 2`, `P = 1`
every payload satisfies the pointwise bound `2 <= e * P` while their sum is `4`,
which exceeds it.  Substituting the pointwise reading would therefore have
carried `t` copies of the frozen `2^{eps_* n}P_*(H)` term into the conclusion,
squaring the frozen envelope exactly where the frozen display carries it
once. -/
theorem perBranchPayloadBoundIsNotTheFrozenListBound :
    (∀ j ∈ Finset.range 2, (fun _ : ℕ => (2 : ℕ)) j ≤ 2 * 1) ∧
      ¬ ((∑ j ∈ Finset.range 2, (fun _ : ℕ => (2 : ℕ)) j) ≤ 2 * 1) := by
  refine ⟨fun _ _ => by norm_num, ?_⟩
  norm_num [Finset.sum_range_succ]

/-- **Statement pole (repair 3): the frozen `Q_*` is not a scalar.**

`B_gap(n) = Q_*(n + B_Phi(n) + 1)` with `Q_*` a coefficientwise nonnegative
integer *polynomial* (frozen lines 1246--1247 and 2361--2362).  Round 1 spelled
this as a product `Q * (n + B_Phi + 1)`, which is the special case of a
monomial with zero constant term.  The general case is not of that form: the
all-ones polynomial of degree one takes the value `4` at the argument `3`, and
no natural number `Q` has `Q * 3 = 4`.  So the scalar spelling is not a
weakening or a strengthening of the frozen datum -- it is a different function
family, and `gapCodeBound` uses `polyEval`. -/
theorem scalarGapBoundIsNotTheFrozenPolynomial :
    polyEval (fun _ => 1) 1 3 = 4 ∧ ¬ ∃ Q : ℕ, Q * 3 = polyEval (fun _ => 1) 1 3 := by
  have h : polyEval (fun _ => 1) 1 3 = 4 := by
    norm_num [polyEval, Finset.sum_range_succ]
  refine ⟨h, ?_⟩
  rintro ⟨Q, hQ⟩
  rw [h] at hQ
  omega

/-- **Statement pole: the frozen ceiling widths are not floor widths.**

`M9` demands that ceilings survive transcription.  `w(t) = ceil(log_2(t+1))` is
landed as `Nat.clog`, and the floor spelling is a *different function*: the
banked `TruthTableExponent.floorAndCeilingDisagreeInGeneral` already records
that at `6` they return `2` and `3`.  That banked statement is **reused, not
re-proved**, and it is exactly the argument of `codeWidth 5`, so the frozen
header length `2w(5)+1` would be understated by two bits under the floor
spelling. -/
theorem floorWidthIsNotTheFrozenWidth :
    codeWidth 5 = Nat.clog 2 6 ∧ headerLength 5 = 2 * Nat.clog 2 6 + 1 ∧
      Nat.log 2 6 ≠ Nat.clog 2 6 :=
  ⟨rfl, rfl,
    EthInapproximability.ParameterizedNP.TruthTableExponent.floorAndCeilingDisagreeInGeneral⟩

end EthInapproximability.ParameterizedNP.LiteralFinalRuntime
