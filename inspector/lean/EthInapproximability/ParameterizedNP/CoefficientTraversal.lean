import EthInapproximability.ParameterizedNP.EnvelopeRealization
import EthInapproximability.ParameterizedNP.DenseStageFourOpening

/-!
# Parameterized NP route: the two-pass coefficient traversal

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger rows: opened under **`PARAM-001`** (the schedule-compiler thread), and
retiring one registered deferral of **`SIZE-001`** / `FIXED-LEVEL-CARRIERS-001`.

`EnvelopeRealization.lean` (tranche 63) built the successor argument but had to
carry the first row of `eq:structural-majorants` as a **named hypothesis**
`hstruct`, recording as its **GAP-EXPOSED 2**:

> `eq:structural-majorants`' first row is the conclusion of the two-pass
> coefficient traversal over the whole Section-6 gate list; that traversal is
> not formalized, so `hstruct` (and its source-width companion) is an explicit
> hypothesis at the frozen display. ... This is a PARK with the dependency
> named: **the second-pass coefficient traversal of `06:1660--1706`**.

This module formalizes that traversal's combination step and **turns `hstruct`
into a theorem**.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

## The frozen chain this module traces

Opened first-hand this tranche, `06-parameter-schedule.tex:1662--1706`:

```
For the first pass, keep the formal integer variable X used in
(eq:exceptional-coefficient-roots).  After its explicit factor-nine
shift absorption, the literal coefficient pass writes every requested
exceptional-set binary length in the form
     (c_0(u) + b_0(u) clog_2(X+2)) L_P^2
with the explicitly computed integers c_0(u), b_0(u), and
(eq:Cexc0-literal-producer) takes their two literal maxima.  Choose
A_wrap > c_seed as the least integer satisfying
     A_wrap >= C_exc^0 + B_exc^0 clog_2(A_wrap+2) + 4
and set C_exc = C_exc^0 + B_exc^0 clog_2(A_wrap+2).
This search terminates and gives A_wrap > C_exc.  Run the same finite
traversal again with this integer substituted for X.  Equation
(eq:Csize-literal-producer), rather than the four-row degree summary,
produces C_size >= 2.  Beyond the constant input cutoffs emitted by that
traversal,
     every new logarithmic side length and auxiliary scale <= W(L) := 2^{C_size L^8},
     ...
```

The four supporting displays are opened at their own anchors, never recalled:

1. `(CoeffRow)` (`06-parameter-schedule.tex:1500--1507`): the pass's output row
   is `(u, C_u, d_u, P_u)` with `P_u : val(u) <= 2^{C_u P^{d_u}}`, and
   "every requested exponential majorant is finally replaced by coefficient
   `max{1, C_u}`" (lines 1511--1512).
2. `06:1631--1637`: "Here `A_pre >= 16`, so `L >= 1`, and every row carries the
   checked absorption `(L+2)^{d_u} <= 3^{d_u} L^{d_u}`.  The later promotion
   from degree `d_u <= 8` to degree eight also uses `L >= 1`.  The seven T3 rows
   instead have checked degree `d_u <= 2` in the driver `A_*`, so they feed
   `2^{C_size A_*^2}` directly and undergo no `L+2`-to-`L` shift."
3. `eq:Csize-literal-producer` (label line 1624, display 1611--1625) -- the
   **banked** `SizePropagation.csizeLiteral`, consumed by pin and not restated.
   `06:1628--1631` is the DEFINED-vs-FREE ruling this module obeys, and the
   sentence spans those four lines: "the registry determines a finite table of
   one checked row `(u, C_u, d_u, P_u)` per expanded successor or tail factor
   root; **no human or formalizer supplies a coefficient**."
4. `06:1555--1565`: the first pass's raw affine row
   `bar c_0(u) + bar b_0(u) clog_2(X+2)` at driver `P = L_P + 2`, the shift rule
   "Since the schedule has `P_0 >= 16`, we have `L_P >= 1`, and therefore
   `(L_P+2)^2 <= 9 L_P^2`", and the coefficient row's explicit
   `c_0(u) = 9 bar c_0(u)`, `b_0(u) = 9 bar b_0(u)`.  The affine form itself is
   the **banked** `IterationAssembly.excAffine`; the two literal maxima are the
   banked `.cexcZero`, `.bexcZero`; the search and `C_exc` are the banked
   `.awrap`, `.cexcOf`, `.coefficientPass_awrap`.  None is restated.

## What lands

* `CoeffRow`, `RowChecked` -- the pass's output row of `(CoeffRow)` as **data
  plus one legality guard** (`d_u <= 8`, the largest entry of the mechanically
  generated degree table, `06:1643--1656` and `06:1704--1706`), with the checked
  derivation `P_u` travelling as an explicit predicate at every use site rather
  than sitting in constructor data.
* `shiftAbsorption`, `degreePromotion` -- the two frozen absorptions of
  `06:1631--1634`, each with its `L >= 1` side condition, each shown to be
  content (`shiftAbsorption_needs_positive_L`, `degreeGuard_is_content`).
* `row_le_structuralW` and **`structuralMajorantRow`** -- the first row of
  `eq:structural-majorants` as a **theorem**: at `L >= 1`, every value of a
  second-pass row list checked at driver `L+2` is at most
  `W(L) = 2^{C_size L^8}` at the recorded `C_size = csizeLiteral`.
* `excRow_shifted`, `excRow_le_cexc`, `firstPass_feeds_secondPass` -- the
  **first** pass: the factor-nine shift, the two literal maxima, and the
  substitution `X := A_wrap` that produces `C_exc` and hands the second pass its
  numeral.  `excRow_le_cexc` is the third row of `eq:structural-majorants`
  (`log_2(...) <= C_exc L_P^2`) at a single requested root.
* `traversalRealization_of_rows`, `srcWidthLogRealization_of_rows`,
  `htraversal_of_state_of_rows`, `hsrclog_of_state_of_rows` -- **all four**
  hypothesis-bearing `EnvelopeRealization` deliverables, **with `hstruct` and
  its source-width companion `hstructSrc` discharged**, i.e.
  `EnvelopeRealization`'s GAP-EXPOSED 2 retired for all four of that module's
  hypothesis-bearing deliverables -- the **combination step**; the traversal's
  row *production* stays open here as GAP-EXPOSED 1.  Both antecedent slots
  of `SuccessorMajorant.successorMajorant` (`htraversal` and `hsrclog`,
  `SuccessorMajorant.lean:656--662`) are therefore fillable from checked rows
  alone, with no structural-majorant hypothesis supplied by hand at any
  consumer.
* `traversalPremises_inhabited` and `bothSlots_premises_inhabited` -- the
  non-vacuity of that claim.  The first exhibits `hmaj` and `hchk` together with
  the structural conclusion; the second exhibits one row list and one output
  record meeting **all three** premises of the two slots at once (`hmaj`,
  `hchk`, and the second slot's membership `hmem`) together with both structural
  conclusions, so "both slots are filled from checked rows alone" is not a
  type-level claim standing on an unexhibited tuple.  Both are labelled
  BEYOND-PAPER (GAP-EXPOSED 2).
* `rowsN`, `colsN`, `paperCarrierSpec`, `paperCarrierSpec_realized` -- the
  **canonical inhabitation of `m_{N,i}`, `n_{N,i}`** registered against
  `SIZE-001`, discharged with the paper's own construction: `N = A^T`
  (`08-dense-stage4.tex:147`) over the protected duplicate, so
  `m_N = |Rows(N)| = |Cols(A)| = 184 M_0 S_0 D_0` and
  `n_N = |Cols(N)| = |Rows(A)| = 2^{22} X_0 T_raw V_raw B_raw`
  (`eq:protected-carrier-cardinalities`, `08:111--122`).  The interim
  `FixedLevelCarriers.fixedLevelCarriers_realized_fires` count-realizing
  stand-in is **superseded**.

## DEFINED-vs-FREE

* **DEFINED, reified and evaluated, never assigned a numeral:** `W(L)` (banked
  `SizePropagation.structuralW`), `C_size` (banked `.csizeLiteral`), the affine
  first-pass row (banked `IterationAssembly.excAffine`), `C_exc^0`, `B_exc^0`
  (banked `.cexcZero`, `.bexcZero`), `A_wrap` (banked `.awrap`), `C_exc` (banked
  `.cexcOf`), `c_seed` and `L_P` (banked `ParameterSchedule.cSeed`, `.LPwidth`
  at `.P0sched`), the shift constants nine and three and the promotion degree
  eight (frozen numerals of `06:1561`, `06:1633`, `06:1694`), the seven protected
  multiplicities and both protected carrier totals (banked
  `DenseStageFourOpening.wBase` .. `.uBlock`, `.card_ProtColsFrozen`,
  `.card_ProtRowsFrozen`), `m_0`, `n_0`, `A_wrap`, `L_P`, `delta_U` inside the
  carrier specification (banked `FixedLevelCarriers.paperSeedSpec`).
* **FREE in the paper itself, therefore binders:** the registry's per-root
  coefficient table `(C_u, d_u)` -- `06:1628--1631` forbids a formalizer to
  supply it, so every theorem below quantifies over all admissible tables rather
  than naming one; the recorded exceptional table `(bar c_0(u), bar b_0(u))`; the
  Section-8 reservoir carriers `V, X, L_2, Y` and the Stage-2 width `q`, which
  the one-level construction fixes from data no Lean module produces yet.
* **The one printed value bound** the frozen second pass computes in full is the
  reduced source-template factor of `06:1590--1597`,
  `q_2(1+eps_2)N_src / (s q_1^{t_2} m_R^{t_2-1}) <= 2 q_2^2/q_1^{t_2} <= 2`;
  `reducedSourceTemplate_checked` states it **at every admissible coefficient
  pair**, which is strictly stronger than inventing one and is the only form
  `06:1628--1631` permits.

## Reader counterparts

The reader artifact of the same frozen release,
`routes/parameterized-np/reader-facing/sections/`, was opened first-hand this
tranche and every candidate read in place.

**No reader item is claimed by any declaration here, and the reason is
recorded.**  A search of all nine reader files for `C_{\mathrm{size}}`,
`A_{\mathrm{wrap}}`, `coefficient`, `traversal` and `majorant` returns **no**
occurrence of the constant `C_size`, of `A_wrap`, of `C_exc`, of the two-pass
structure, of the factor-nine shift, or of the degree table: the reader's only
two sentences touching the pass are `05-iteration.tex:240--246` and
`:248--251`, **both inside `\begin{proof}`**, hence proof prose, which the
reader-counterpart rule forbids citing as a statement -- and `:245--246` is in
any case already `EnvelopeRealization.CutoffEmission.nStep`'s neighbourhood.
Reader appendix C's two non-proof sentences, `C-effectivity-details.tex:82--84`
and `:86--88`, are **already assigned** to `EnvelopeRealization.pCut` and
`.pCut_nonempty`, and re-citing either is the double assignment the rule
forbids; the remaining candidate `:80--82` overlaps line 82 with the first of
them, so it is declined rather than split.  For the Stage-4 counts, the reader's
protected-duplication paragraph `A-stage4-details.tex:180--194` is
the seven multiplicities the banked `DenseStageFourOpening` already transcribes,
and its follow-on sentence `:197` (the exact masses) is already assigned to
`WRAPPER-PROTECTED-EARLY-001`; the reader never prints either protected carrier
total as an equation at all.

Crosswalk: no new row; the assignments and the compiler's remaining Lean-pending
status stay in the existing row **6, "Simultaneous parameters and size"**, of
`READER_CROSSWALK.md`, which is `PARAM-001`'s row.

## Status and dependencies

* Proof status: **new (elementary)** throughout.  Every declaration is a
  transcription of a frozen display, a general property of that transcription,
  or a composition of banked results.  No communication-complexity lemma is
  introduced, adapted or re-proved, and no banked module is edited.
* Consumed by pin, never restated: `SizePropagation.structuralW`,
  `.csizeLiteral`, `.csizeLiteral_spec`; `IterationAssembly.excAffine`,
  `.literalMax`, `.le_literalMax`, `.cexcZero`, `.bexcZero`, `.awrap`,
  `.cexcOf`, `.coefficientPass_awrap`, `.envE`, `.ellN`, `.cexp`;
  `ParameterSchedule.cSeed`, `.LPwidth`, `.P0sched`, `.four_le_LPwidth_sched`;
  `SuccessorMajorant.SuccessorOutputs`, `.LevelState`;
  `EnvelopeRealization.CutoffEmission`, `.absorbedCoeff`, `.dExp`, `.eExp`,
  `.traversalRealization`, `.srcWidthLogRealization`, `.htraversal_of_state`,
  `.hsrclog_of_state`, `.normalizedL`, `.four_le_normalizedL`;
  `FixedLevelCarriers.LevelCarrierSpec`, `.paperSeedSpec`,
  `.fixedLevelCarriers_realized`;
  `DenseStageFourOpening.ProtColsFrozen`, `.ProtRowsFrozen`, `.protectedAFrozen`,
  `.transposeN`, `.card_ProtColsFrozen`, `.card_ProtRowsFrozen`,
  `.protectedAFrozen_carriers_nondegenerate`;
  `BridgeOutputEquality.rowsCard`, `.colsCard`; `OneLevelCompletion.levelOutput`.
* Imports: `EnvelopeRealization` and `DenseStageFourOpening`, hence transitively
  `SuccessorMajorant`, `PilotPCut`, `DominantWidthBound`, `PaddingAndClock`,
  `FixedLevelCarriers`, `SizePropagation`, `IterationAssembly`,
  `ParameterSchedule`, `EntryGates`, `RawStageFour` and
  `EthInapproximability.Prelude`, hence `LegacyNPCC.Core` (project-axiom-free)
  and `LegacyNPCC.Bridge`.  **`LegacyNPCC.Stage12` is not imported**, so no
  declaration reaches the cited AGHP balanced-family axiom and no opt-in ledger
  note is owed; `EXPANDER-001` has no contact with this module.
* External adapters: none.  No new `axiom`, no opaque certificate.
* Axiom surface (Appendix D, and `#print axioms`): at most `propext`,
  `Classical.choice`, `Quot.sound`.

## Faithfulness notes (mechanical rules M1--M10)

* **Both new structures carry data plus at most one legality guard.**
  `CoeffRow` has the three printed components of `(CoeffRow)` and the frozen
  degree guard `d_u <= 8`; `ExcRow` has the requested binary length and the two
  recorded pre-shift integers `bar c_0(u)`, `bar b_0(u)` and **no** guard.
  Neither carries a complexity, robustness or promise field, neither carries the
  desired conclusion `value <= W(L)`, and neither restates a derived telescope:
  the shifted integers `9 bar c_0`, `9 bar b_0` and the recorded maxima are
  `def`s and theorems about the record, not fields.
* **The checked derivation is a predicate, not a field.**  `P_u` of `(CoeffRow)`
  is `RowChecked`, supplied at each use site, exactly as `SizePropagation`
  travels `z_N <= bar z_N` as a named hypothesis rather than as definitional
  content.
* **Both interlace widths stay distinct.**  `q_i` and `Q_i` enter only through
  the banked `FixedLevelCarriers.LevelCarrierSpec.q` and `.Q`; nothing here
  merges them or reads one for the other.
* **Every comparison is transcribed as printed.**  `d_u <= 8`, `C_size >= 2`,
  `(L+2)^{d_u} <= 3^{d_u} L^{d_u}`, `(L_P+2)^2 <= 9 L_P^2`, `A_wrap > C_exc` and
  the structural row `<= W(L)` are all non-strict or strict exactly as at
  `06:1634`, `06:1689`, `06:1633`, `06:1561`, `06:1686` and `06:1693--1694`.
* **Statement poles.**  `shiftAbsorption_needs_positive_L`,
  `degreeGuard_is_content`, `lpShift_needs_positive_LP` and
  `structuralMajorantRow_needs_the_checked_rows` each exhibit a concrete failure
  when one hypothesis is dropped, so none of the four is decoration.
  `paperCarrierSpec_counts_are_not_the_stand_in` separates the paper's counts
  from the interim probe's in the kernel.

## GAP-EXPOSED

1. **The compiler is still not built.**  `thm:eff-ledger`'s existential --
   `K_*`, `c |-> Cert_c`, the byte machine `A_cert`, `SchemaChecked`,
   `NumChecked`, the expression graph, and the two producers' recorded tables --
   has no Lean declaration and none is given.  What lands here is the frozen
   *combination step*: **given** the pass's per-root checked rows at the frozen
   driver, the structural row follows.  Nothing below asserts that any concrete
   compiler emits them, and nothing below is an axiom.  `PARAM-001` stays open.
2. **The registry's coefficient table is not inhabited at the paper's numbers.**
   `06:1628--1631` states that no formalizer supplies a coefficient, so the
   canonical inhabitation of `CoeffRow` at the paper's own `(C_u, d_u)` is
   **registered as deferred** against `PARAM-001`, discharged when the registry
   lands.  The
   in-tranche instances are of two honest kinds and no third:
   `reducedSourceTemplate_checked`, which is the paper's own printed value bound
   at **every** admissible coefficient pair, and the three explicitly
   BEYOND-PAPER audit instances `structuralMajorantRow_hypotheses_consistent`,
   `traversalPremises_inhabited` and `bothSlots_premises_inhabited`, whose
   shared row exercises our encoding at a tightness point the paper never
   prints.  None of the three is a canonical inhabitation, and none substitutes
   for the paper's application point.
3. **Only the `L+2` half of `eq:Csize-literal-producer` is composed, and the
   `rows3` domination clause is not used.**  The seven `T3_B1` rows of
   `06:1601--1606` feed `2^{C_size A_*^2}` at driver `A_*` and undergo no shift
   (`06:1634--1637`); `csizeLiteral`'s `rows3` argument carries them, **but
   nothing here dominates a T3 row through `passCsize`**.  Stated exactly:
   `structuralMajorantRow` ranges over `passValues rows` only, so the only
   clauses of the banked `SizePropagation.csizeLiteral_spec` this module invokes
   are `.1` (the floor `C_size >= 2`, through `two_le_passCsize`) and `.2.1`
   (the `3^{d_u} C_u` domination of the `L+2` table, through
   `passCsize_dominates`); the producer's third clause `.2.2`, which dominates
   the `rows3` entries, is invoked by **no** declaration below, and every
   instance below passes `rows3 = []`.  `tailRow_le_tailMajorant` is the one-row
   form at a universally quantified `Csize` and is never connected to
   `passCsize`; the majorant `2^{C_size A_*^2}` itself is the **third** tail
   error of `eq:four-tail-errors` and is not stated here.  `rows3` is therefore
   a live binder of `passCsize` (it changes the produced `C_size`) but a dead
   *hypothesis* for the T3 majorant, and this entry records that as the residue
   rather than claiming the composition.
4. **The other three rows of `eq:structural-majorants` are not claimed.**
   `b_T >= L^{20}/C_size` and `b_1 >= A_*^6/C_size` (line 1695--1696) and
   `L_theta <= 2^{C_size L_P}` (line 1699) have no declaration here; only the
   first row and, at a single root, the `C_exc L_P^2` row of line 1697--1698.
5. **The level-indexed Stage-4 chain is still absent, in a strictly narrower
   sense than before.**  `paperCarrierSpec` supplies `m_{N,i}`, `n_{N,i}` as the
   `Fintype.card` of the paper's own `N = A^T` carriers, so the counts are no
   longer recorded integers and the NON-FIDELITY stand-in is superseded.  What
   remains open is the *plumbing*: producing level `i`'s Section-8 reservoir data
   `(F, q, V, X, L_2, Y)` from the previous level's output `R_i` is
   `STAGE1-001` .. `WRAP-001`, so the instance is exhibited at one legal choice
   of that data held **level-uniformly**, and the level-indexed variation stays
   with those rows.  No route completion is claimed anywhere in this module.
-/

namespace EthInapproximability.ParameterizedNP.CoefficientTraversal

open EthInapproximability.ParameterizedNP.IterationAssembly
open EthInapproximability.ParameterizedNP.SizePropagation
open EthInapproximability.ParameterizedNP.SuccessorMajorant
open EthInapproximability.ParameterizedNP.EnvelopeRealization

/-! ## Part 1: the pass's output row

`(CoeffRow)`, `06-parameter-schedule.tex:1500--1507`. -/

/-- **The coefficient pass's output row** -- `(CoeffRow)`
(`06-parameter-schedule.tex`, display lines 1501--1507):

```
 (u, C_u, d_u, P_u),   P_u :  val(u) <= 2^{C_u P^{d_u}}
```

Three data components and one legality guard, and nothing else.

* `value` is `val(u)`, the requested root's value;
* `coeff` is `C_u`, and `06:1511--1512` fixes its floor -- "every requested
  exponential majorant is finally replaced by coefficient `max{1, C_u}`" -- which
  is *not* a field here, because the successor combination never uses it (an
  unused hypothesis in constructor data would be over-strong, and the banked
  `csizeLiteral`'s own `{2}` floor already dominates);
* `degree` is `d_u`, guarded by the frozen `d_u <= 8` of `06:1634`, whose value
  is fixed by the mechanically generated degree table of `06:1643--1656` and
  reasserted at `06:1704--1706` ("the exponent eight ... is the largest entry in
  the displayed, mechanically generated degree table").

The derivation tree `P_u` is deliberately **not** a field: it is the predicate
`RowChecked` below, supplied at each use site.  Putting it in the record would
be the conclusion-in-constructor-data defect that rule M4 forbids and would make
the type an assertion rather than a row. -/
structure CoeffRow where
  /-- `val(u)`, the requested root's value. -/
  value : ℕ
  /-- `C_u`, the row's recorded integer coefficient. -/
  coeff : ℕ
  /-- `d_u`, the row's checked degree in the driver. -/
  degree : ℕ
  /-- Legality guard: the frozen `d_u <= 8` of `06:1634`. -/
  degree_le_eight : degree ≤ 8

/-- **`P_u` of `(CoeffRow)`, as a predicate at a driver** --
`06-parameter-schedule.tex:1505`, `val(u) <= 2^{C_u P^{d_u}}`.

`P` is the pass's driver: `L + 2` for the C7 roots and the nine `T1`--`T2`
factors, `A_*` for the seven `T3` factors (`06:1608--1610`). -/
def RowChecked (P : ℕ) (r : CoeffRow) : Prop :=
  r.value ≤ 2 ^ (r.coeff * P ^ r.degree)

/-- **Aux 1 (a checked row stays checked at a larger driver).**  Monotone in the
driver, which is what lets the same registry row be read at `L + 2` after the
`A_pre` normalization moves `L`.  General in the row and both drivers. -/
theorem rowChecked_mono_driver {P P' : ℕ} (r : CoeffRow) (h : P ≤ P')
    (hr : RowChecked P r) : RowChecked P' r := by
  refine le_trans hr (Nat.pow_le_pow_right (by norm_num) ?_)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

/-- **Aux 2 (a checked row stays checked at a larger coefficient).**  Monotone in
`C_u`, which is the direction `06:1511--1512`'s `max{1, C_u}` replacement moves
in, so the frozen final convention cannot invalidate a row.  General. -/
theorem rowChecked_mono_coeff {P C C' d : ℕ} {v : ℕ} (hd : d ≤ 8) (hd' : d ≤ 8)
    (h : C ≤ C')
    (hr : RowChecked P ⟨v, C, d, hd⟩) : RowChecked P ⟨v, C', d, hd'⟩ := by
  refine le_trans hr (Nat.pow_le_pow_right (by norm_num) ?_)
  exact Nat.mul_le_mul_right _ h

/-- **Aux 3 (`06:1590--1597`: the reduced source-template row, at every
admissible coefficient pair).**

The one requested second-pass root whose value bound the frozen source computes
in print is the `T1_Q2` source-template factor:

```
 q_2(1+eps_2)N_src / (s q_1^{t_2} m_R^{t_2-1})  <=  2 q_2^2 / q_1^{t_2}  <=  2,
```

"The reduced constant row, not the unreduced quotient, enters its coefficient
derivation" (`06:1598--1599`).

`06:1628--1631` forbids a formalizer to supply `(C_u, d_u)`, so the statement is
made at **every** pair admissible under `06:1511--1512`'s `max{1, C_u}` floor
and any positive driver, rather than at an invented one.  General in the driver, the
coefficient, the degree, and in any value the printed reduction bounds by two. -/
theorem reducedSourceTemplate_checked {P C d v : ℕ} (hd : d ≤ 8) (hP : 1 ≤ P)
    (hC : 1 ≤ C) (hv : v ≤ 2) : RowChecked P ⟨v, C, d, hd⟩ := by
  have hpow : 1 ≤ P ^ d := Nat.one_le_pow _ _ (by omega)
  have hexp : 1 ≤ C * P ^ d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have : (2 : ℕ) ^ 1 ≤ 2 ^ (C * P ^ d) := Nat.pow_le_pow_right (by norm_num) hexp
  simp only [RowChecked]
  omega

/-! ## Part 2: the two frozen absorptions of `06:1631--1634` -/

/-- **The checked shift absorption** -- `06-parameter-schedule.tex:1631--1633`:
"Here `A_pre >= 16`, so `L >= 1`, and every row carries the checked absorption
`(L+2)^{d_u} <= 3^{d_u} L^{d_u}`."

The side condition `L >= 1` is the frozen one and is not weakened; the banked
`EnvelopeRealization.four_le_normalizedL` supplies `L = clog_2(A_pre) >= 4` at
every use site.  General in `L >= 1` and in the degree. -/
theorem shiftAbsorption (L d : ℕ) (hL : 1 ≤ L) : (L + 2) ^ d ≤ 3 ^ d * L ^ d := by
  have h : L + 2 ≤ 3 * L := by omega
  calc (L + 2) ^ d ≤ (3 * L) ^ d := Nat.pow_le_pow_left h d
    _ = 3 ^ d * L ^ d := Nat.mul_pow 3 L d

/-- **Statement pole: the shift absorption really needs `L >= 1`.**

At `L = 0` and degree one the frozen inequality reads `2 <= 0` and fails, so
`06:1631`'s appeal to `A_pre >= 16` is content and not decoration.  Exhibited in
the kernel rather than argued in prose. -/
theorem shiftAbsorption_needs_positive_L :
    ¬ ((0 : ℕ) + 2) ^ 1 ≤ 3 ^ 1 * (0 : ℕ) ^ 1 := by norm_num

/-- **The checked degree promotion** -- `06-parameter-schedule.tex:1633--1634`:
"The later promotion from degree `d_u <= 8` to degree eight also uses `L >= 1`."

General in `L >= 1` and in any degree under the frozen guard. -/
theorem degreePromotion (L d : ℕ) (hL : 1 ≤ L) (hd : d ≤ 8) : L ^ d ≤ L ^ 8 :=
  Nat.pow_le_pow_right hL hd

/-- **Statement pole: the degree guard `d_u <= 8` is content.**

A row of degree nine is not promoted to degree eight: at `L = 2` the promotion
would read `2^9 <= 2^8`.  So `CoeffRow.degree_le_eight` is a genuine legality
guard on the registry's rows and not a convenience. -/
theorem degreeGuard_is_content : ¬ (2 : ℕ) ^ 9 ≤ 2 ^ 8 := by norm_num

/-- **Aux 4 (`W` is monotone in the recorded coefficient).**  A general property
of the banked `SizePropagation.structuralW`, used to move from a single row's
`3^{d_u} C_u` to the literal maximum `C_size`.  General. -/
theorem structuralW_mono_csize {C C' : ℕ} (L : ℕ) (h : C ≤ C') :
    structuralW C L ≤ structuralW C' L :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h)

/-! ## Part 3: one checked row under the structural majorant -/

/-- **One second-pass row under `W(L)`.**

The frozen composition of `06:1631--1634` with `eq:structural-majorants`' first
row: a row checked at the pass's own driver `L + 2`, whose absorbed coefficient
`3^{d_u} C_u` is dominated by the recorded `C_size`, has

```
 val(u) <= 2^{C_u (L+2)^{d_u}} <= 2^{(3^{d_u} C_u) L^{d_u}}
        <= 2^{C_size L^{d_u}}  <= 2^{C_size L^8} = W(L),
```

using the checked shift absorption, the dominance, and the degree promotion in
that order.  `W` is the banked `SizePropagation.structuralW`, consumed by pin.

General in the row, in `L >= 1` and in the recorded coefficient. -/
theorem row_le_structuralW (L Csize : ℕ) (hL : 1 ≤ L) (r : CoeffRow)
    (hchk : RowChecked (L + 2) r) (hC : 3 ^ r.degree * r.coeff ≤ Csize) :
    r.value ≤ structuralW Csize L := by
  have h1 : r.coeff * (L + 2) ^ r.degree ≤ r.coeff * (3 ^ r.degree * L ^ r.degree) :=
    Nat.mul_le_mul_left _ (shiftAbsorption L r.degree hL)
  have h2 : r.coeff * (3 ^ r.degree * L ^ r.degree)
      = (3 ^ r.degree * r.coeff) * L ^ r.degree := by ring
  have h3 : (3 ^ r.degree * r.coeff) * L ^ r.degree ≤ Csize * L ^ r.degree :=
    Nat.mul_le_mul_right _ hC
  have h4 : Csize * L ^ r.degree ≤ Csize * L ^ 8 :=
    Nat.mul_le_mul_left _ (degreePromotion L r.degree hL r.degree_le_eight)
  have hexp : r.coeff * (L + 2) ^ r.degree ≤ Csize * L ^ 8 := by omega
  calc r.value ≤ 2 ^ (r.coeff * (L + 2) ^ r.degree) := hchk
    _ ≤ 2 ^ (Csize * L ^ 8) := Nat.pow_le_pow_right (by norm_num) hexp
    _ = structuralW Csize L := rfl

/-- **One `T3_B1` row under its own majorant** -- `06:1634--1637`: "The seven T3
rows instead have checked degree `d_u <= 2` in the driver `A_*`, so they feed
`2^{C_size A_*^2}` directly and undergo no `L+2`-to-`L` shift."

Stated at the *bare* coefficient `C_u <= C_size` -- which is exactly how
`eq:Csize-literal-producer`'s third set enters the banked `csizeLiteral`'s
`rows3` argument -- and at driver `A_*` with the frozen degree bound two, with
**no** factor `3^{d_u}` anywhere.  General in `A_* >= 1`, the row and the
recorded coefficient. -/
theorem tailRow_le_tailMajorant (Astar Csize : ℕ) (hA : 1 ≤ Astar) (r : CoeffRow)
    (hd : r.degree ≤ 2) (hchk : RowChecked Astar r) (hC : r.coeff ≤ Csize) :
    r.value ≤ 2 ^ (Csize * Astar ^ 2) := by
  have h1 : r.coeff * Astar ^ r.degree ≤ Csize * Astar ^ r.degree :=
    Nat.mul_le_mul_right _ hC
  have h2 : Csize * Astar ^ r.degree ≤ Csize * Astar ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hA hd)
  exact le_trans hchk (Nat.pow_le_pow_right (by norm_num) (by omega))

/-! ## Part 4: the second pass, and `hstruct` as a theorem -/

/-- **The `L+2` pass's coefficient table**, in the shape
`eq:Csize-literal-producer`'s first set feeds the banked producer: one pair
`(C_u, d_u)` per row, in the pass's own order.  A `def` over the row list, never
a stored field. -/
def passRows12 (rows : List CoeffRow) : List (ℕ × ℕ) :=
  rows.map fun r => (r.coeff, r.degree)

/-- **`C_size` at a traversal's two tables** -- `eq:Csize-literal-producer`
(`06-parameter-schedule.tex`, label line 1624) through the **banked**
`SizePropagation.csizeLiteral`, consumed by pin and not restated.  `rows3`
carries the seven `T3_B1` bare coefficients of `06:1601--1606`. -/
def passCsize (rows : List CoeffRow) (rows3 : List ℕ) : ℕ :=
  csizeLiteral (passRows12 rows) rows3

/-- **The traversal's majorised list**: the requested roots' values, in the
pass's order. -/
def passValues (rows : List CoeffRow) : List ℕ := rows.map CoeffRow.value

@[simp] theorem passRows12_nil : passRows12 [] = [] := rfl

@[simp] theorem passRows12_cons (r : CoeffRow) (t : List CoeffRow) :
    passRows12 (r :: t) = (r.coeff, r.degree) :: passRows12 t := rfl

@[simp] theorem passValues_cons (r : CoeffRow) (t : List CoeffRow) :
    passValues (r :: t) = r.value :: passValues t := rfl

/-- **Aux 5 (`06:1689`: the producer returns `C_size >= 2`).**  "Equation
`eq:Csize-literal-producer`, rather than the four-row degree summary, produces
`C_size >= 2`."  Read off the banked producer's own specification; nothing is
recomputed and the degree summary is not consulted.  General in both tables. -/
theorem two_le_passCsize (rows : List CoeffRow) (rows3 : List ℕ) :
    2 ≤ passCsize rows rows3 :=
  (csizeLiteral_spec (passRows12 rows) rows3).1

/-- **Aux 6 (every row of the pass is dominated by the recorded `C_size`).**
The absorbed coefficient `3^{d_u} C_u` of `eq:Csize-literal-producer`'s first
set, at the row's own entry in the table.  General in both tables. -/
theorem passCsize_dominates {rows : List CoeffRow} {rows3 : List ℕ} {r : CoeffRow}
    (hr : r ∈ rows) : 3 ^ r.degree * r.coeff ≤ passCsize rows rows3 := by
  have hmem : (r.coeff, r.degree) ∈ passRows12 rows :=
    List.mem_map.mpr ⟨r, hr, rfl⟩
  exact (csizeLiteral_spec (passRows12 rows) rows3).2.1 _ hmem

/-- **The first row of `eq:structural-majorants`, as a theorem.**

`06-parameter-schedule.tex`, label line 1701, display lines 1691--1702:

```
 every new logarithmic side length and auxiliary scale <= W(L) := 2^{C_size L^8}
```

`06:1687--1690` is the frozen instruction this discharges: "Run the same finite
traversal again with this integer substituted for `X`.  Equation
`eq:Csize-literal-producer` ... produces `C_size >= 2`.  Beyond the constant
input cutoffs emitted by that traversal, ..."

**This is `EnvelopeRealization`'s `hstruct` turned from a hypothesis into a
theorem**, and -- read at the single value `clog_2 q_2` for the source-width
companion `hstructSrc` -- it retires that module's GAP-EXPOSED 2 in full; the
four wirings are Part 6's.  What is assumed is not
the conclusion but the pass's per-root output at its own driver: each requested
root carries its checked row `val(u) <= 2^{C_u (L+2)^{d_u}}` at degree
`d_u <= 8`.  The passage from those rows to the display is the frozen
shift-absorb / dominate / promote chain of `06:1631--1634`, proved here.

General in the row list, in the `T3` table and in `L >= 1`. -/
theorem structuralMajorantRow (rows : List CoeffRow) (rows3 : List ℕ) (L : ℕ)
    (hL : 1 ≤ L) (hchk : ∀ r ∈ rows, RowChecked (L + 2) r) :
    ∀ x ∈ passValues rows, x ≤ structuralW (passCsize rows rows3) L := by
  intro x hx
  obtain ⟨r, hr, hrx⟩ := List.mem_map.mp hx
  subst hrx
  exact row_le_structuralW L _ hL r (hchk r hr) (passCsize_dominates hr)

/-- **Statement pole: the checked rows carry the whole content.**

Dropping `hchk` makes `structuralMajorantRow` false, and concretely so: the
one-element table `[(0, 0)]` records coefficient zero at degree zero, so the
banked producer returns its floor `C_size = 2` and `W(1) = 2^2 = 4`, while the
row's value is `5`.  Hence the conclusion is not a consequence of the row list's
shape, and in particular the trivial witness -- a row with no checked derivation
-- fails it. -/
theorem structuralMajorantRow_needs_the_checked_rows :
    ¬ (∀ x ∈ passValues [(⟨5, 0, 0, by norm_num⟩ : CoeffRow)],
        x ≤ structuralW (passCsize [(⟨5, 0, 0, by norm_num⟩ : CoeffRow)] []) 1) := by
  intro h
  have h5 := h 5 (by simp [passValues])
  have hC : passCsize [(⟨5, 0, 0, by norm_num⟩ : CoeffRow)] [] = 2 := by
    simp [passCsize, passRows12, csizeLiteral, maxFrom]
  rw [hC] at h5
  simp [structuralW] at h5

/-- **Hypothesis-consistency, with a tight row (BEYOND-PAPER).**

The full hypothesis bundle of `structuralMajorantRow` is exhibited satisfied
**together with its conclusion**, at a row where the checked derivation is an
equality, so no slack hides an inconsistency: the row
`(2^{(L+2)^8}, 1, 8)` is checked at driver `L + 2` by `le_refl`, its absorbed
coefficient is `3^8 = 6561`, and the conclusion still holds through the frozen
absorption.  No `False` derives from the bundle.

**BEYOND-PAPER, and labelled so:** the registry's own `(C_u, d_u)` table is
compiler data that `06:1628--1631` forbids a formalizer to supply, so this row
audits our encoding at a tightness point the paper never prints.  It is strictly weaker
evidence than the paper's application point and is **not** a canonical
inhabitation; that obligation is registered (GAP-EXPOSED 2). -/
theorem structuralMajorantRow_hypotheses_consistent (L : ℕ) (hL : 1 ≤ L) :
    ∃ rows : List CoeffRow,
      (∀ r ∈ rows, RowChecked (L + 2) r) ∧
        passCsize rows [] = 6561 ∧
        passValues rows = [2 ^ (L + 2) ^ 8] ∧
        (∀ x ∈ passValues rows, x ≤ structuralW (passCsize rows []) L) := by
  set r0 : CoeffRow := ⟨2 ^ (L + 2) ^ 8, 1, 8, le_refl 8⟩ with hr0
  have hchk0 : RowChecked (L + 2) r0 := by
    simp [RowChecked, hr0]
  have hC : passCsize [r0] [] = 6561 := by
    simp [passCsize, passRows12, csizeLiteral, maxFrom, hr0]
  refine ⟨[r0], ?_, hC, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact hchk0
  · simp [passValues, hr0]
  · intro x hx
    rw [hC]
    simp only [passValues, List.map_cons, List.map_nil, List.mem_singleton] at hx
    subst hx
    exact row_le_structuralW L 6561 hL r0 hchk0 (by simp [hr0])

/-! ## Part 5: the first pass, and the substitution `X := A_wrap`

`06-parameter-schedule.tex:1539--1541`, `1555--1565`, `1662--1686`. -/

/-- **A requested exceptional-set root of the first pass** --
`eq:exceptional-coefficient-roots` (`06-parameter-schedule.tex`, label line 1553,
display 1542--1554) traversed at driver `P = L_P + 2` (line 1541).

`06:1555--1558`: "Direct collection in this fixed subgraph first writes the raw
coefficient in each row uniquely as the affine expression
`bar c_0(u) + bar b_0(u) clog_2(X+2)`, with computed nonnegative integers
`bar c_0(u), bar b_0(u)`."

Three data components and **no** guard: the two recorded integers carry no
positivity in the frozen text, and imposing one would be over-strong.  The
shifted pair `c_0(u) = 9 bar c_0(u)`, `b_0(u) = 9 bar b_0(u)` of line 1564 is a
`def` on the record, never a field, so no derived telescope is restated. -/
structure ExcRow where
  /-- The requested exceptional-set binary length. -/
  value : ℕ
  /-- `bar c_0(u)`, the raw constant coefficient of `06:1557`. -/
  cbar : ℕ
  /-- `bar b_0(u)`, the raw slope on `clog_2(X+2)` of `06:1557`. -/
  bbar : ℕ

/-- `c_0(u) = 9 bar c_0(u)` -- `06-parameter-schedule.tex:1563--1564`, "The
coefficient row explicitly applies this shift rule and sets
`c_0(u) = 9 bar c_0(u)` and `b_0(u) = 9 bar b_0(u)`." -/
def excConst (r : ExcRow) : ℕ := 9 * r.cbar

/-- `b_0(u) = 9 bar b_0(u)` -- `06-parameter-schedule.tex:1564`. -/
def excSlope (r : ExcRow) : ℕ := 9 * r.bbar

/-- **The first pass's raw row at its own driver** --
`06-parameter-schedule.tex:1539--1541` and `1555--1558`: the requested binary
length is bounded by the raw affine coefficient times the driver `(L_P + 2)`
squared, *before* the factor-nine shift. -/
def ExcChecked (X LP : ℕ) (r : ExcRow) : Prop :=
  r.value ≤ (r.cbar + r.bbar * Nat.clog 2 (X + 2)) * (LP + 2) ^ 2

/-- **The frozen factor-nine shift rule** --
`06-parameter-schedule.tex:1558--1562`: "Since the schedule has `P_0 >= 16`, we
have `L_P >= 1`, and therefore `(L_P+2)^2 <= 9 L_P^2`."

The side condition is the frozen one; the banked
`ParameterSchedule.four_le_LPwidth_sched` supplies `L_P >= 4` at every scheduled
use site.  General in `L_P >= 1`. -/
theorem lpShift (LP : ℕ) (hLP : 1 ≤ LP) : (LP + 2) ^ 2 ≤ 9 * LP ^ 2 := by
  have h : LP + 2 ≤ 3 * LP := by omega
  calc (LP + 2) ^ 2 ≤ (3 * LP) ^ 2 := Nat.pow_le_pow_left h 2
    _ = 9 * LP ^ 2 := by ring

/-- **Statement pole: the shift rule needs `L_P >= 1`.**  At `L_P = 0` the frozen
inequality reads `4 <= 0`, so `06:1559`'s appeal to `P_0 >= 16` is content. -/
theorem lpShift_needs_positive_LP : ¬ ((0 : ℕ) + 2) ^ 2 ≤ 9 * (0 : ℕ) ^ 2 := by
  norm_num

/-- **The first pass's shifted row** -- `06-parameter-schedule.tex:1563--1569`,
the form `eq:Cexc0-literal-producer` takes its two maxima over:

```
 (c_0(u) + b_0(u) clog_2(X+2)) L_P^2
```

The right-hand side is the **banked** `IterationAssembly.excAffine` at the
shifted pair, consumed by pin and not restated.  General in the formal leaf `X`,
in `L_P >= 1` and in the row. -/
theorem excRow_shifted (r : ExcRow) (X LP : ℕ) (hLP : 1 ≤ LP)
    (h : ExcChecked X LP r) :
    r.value ≤ excAffine (excConst r) (excSlope r) X LP := by
  have hshift : (r.cbar + r.bbar * Nat.clog 2 (X + 2)) * (LP + 2) ^ 2
      ≤ (r.cbar + r.bbar * Nat.clog 2 (X + 2)) * (9 * LP ^ 2) :=
    Nat.mul_le_mul_left _ (lpShift LP hLP)
  have heq : (r.cbar + r.bbar * Nat.clog 2 (X + 2)) * (9 * LP ^ 2)
      = excAffine (excConst r) (excSlope r) X LP := by
    simp only [excAffine, excConst, excSlope]
    ring
  calc r.value ≤ (r.cbar + r.bbar * Nat.clog 2 (X + 2)) * (LP + 2) ^ 2 := h
    _ ≤ (r.cbar + r.bbar * Nat.clog 2 (X + 2)) * (9 * LP ^ 2) := hshift
    _ = excAffine (excConst r) (excSlope r) X LP := heq

/-- **The recorded exceptional table of a first-pass row list** -- one pair
`(c_0(u), b_0(u))` per requested root, in the pass's printed order, in the shape
the banked `IterationAssembly.cexcZero` / `.bexcZero` consume. -/
def excTable (rows : List ExcRow) : List (ℕ × ℕ) :=
  rows.map fun r => (excConst r, excSlope r)

/-- **Aux 7 (the two literal maxima dominate each row's shifted pair).**
`eq:Cexc0-literal-producer` (`06-parameter-schedule.tex`, label line 1574) taken
over the pass's own table, through the banked `IterationAssembly.le_literalMax`.
General in the row list. -/
theorem excTable_dominates {rows : List ExcRow} {r : ExcRow} (hr : r ∈ rows) :
    excConst r ≤ cexcZero (excTable rows) ∧
      excSlope r ≤ bexcZero (excTable rows) := by
  constructor
  · exact le_literalMax (List.mem_map.mpr ⟨(excConst r, excSlope r),
      List.mem_map.mpr ⟨r, hr, rfl⟩, rfl⟩)
  · exact le_literalMax (List.mem_map.mpr ⟨(excConst r, excSlope r),
      List.mem_map.mpr ⟨r, hr, rfl⟩, rfl⟩)

/-- **The first pass, closed: every requested exceptional binary length is at
most `C_exc L_P^2`.**

`06-parameter-schedule.tex:1670--1686`.  The search is the **banked**
`IterationAssembly.awrap` at the two literal maxima, `C_exc` is the banked
`.cexcOf`, and `06:1687--1688`'s instruction is exactly the substitution made
here: "Run the same finite traversal again with this integer substituted for
`X`."  So the row is read at `X := A_wrap`, and the conclusion is the third row
of `eq:structural-majorants` (`06:1697--1698`,
`log_2(e_0^max E_T u_term B_theta + 2) <= C_exc L_P^2`) at a single requested
root.

General in the seed constant, in `L_P >= 1` and in the pass's row list. -/
theorem excRow_le_cexc (rows : List ExcRow) (r : ExcRow) (hr : r ∈ rows)
    (cseed LP : ℕ) (hLP : 1 ≤ LP)
    (h : ExcChecked (awrap cseed (cexcZero (excTable rows)) (bexcZero (excTable rows)))
      LP r) :
    r.value ≤ cexcOf cseed (cexcZero (excTable rows)) (bexcZero (excTable rows)) * LP ^ 2 := by
  set C0 : ℕ := cexcZero (excTable rows) with hC0
  set B0 : ℕ := bexcZero (excTable rows) with hB0
  set A : ℕ := awrap cseed C0 B0 with hA
  obtain ⟨hc, hb⟩ := excTable_dominates hr
  have hstep := excRow_shifted r A LP hLP h
  have hmono : excAffine (excConst r) (excSlope r) A LP ≤ excAffine C0 B0 A LP := by
    simp only [excAffine]
    exact Nat.mul_le_mul_right _
      (Nat.add_le_add hc (Nat.mul_le_mul_right _ hb))
  have heq : excAffine C0 B0 A LP = cexcOf cseed C0 B0 * LP ^ 2 := by
    simp only [excAffine, cexcOf, hA]
  calc r.value ≤ excAffine (excConst r) (excSlope r) A LP := hstep
    _ ≤ excAffine C0 B0 A LP := hmono
    _ = cexcOf cseed C0 B0 * LP ^ 2 := heq

/-- **The two passes are linked exactly as `06:1686--1688` links them.**

Three conclusions about the *same* triple, all from the banked
`IterationAssembly.coefficientPass_awrap`, none re-derived:

* the search terminates and `A_wrap` is its least tested value above `c_seed`;
* `A_wrap > C_exc` -- the frozen "This search terminates and gives
  `A_wrap > C_exc`" of line 1686;
* the numeral that the second pass substitutes for the formal leaf `X` is that
  same `A_wrap` -- recorded here as the definitional identity, so that no other
  integer can be slipped in at `06:1687`'s "with this integer substituted".

General in the seed constant and in the pass's row list. -/
theorem firstPass_feeds_secondPass (rows : List ExcRow) (cseed : ℕ) :
    cseed < awrap cseed (cexcZero (excTable rows)) (bexcZero (excTable rows)) ∧
      cexcOf cseed (cexcZero (excTable rows)) (bexcZero (excTable rows))
        < awrap cseed (cexcZero (excTable rows)) (bexcZero (excTable rows)) ∧
      cexcOf cseed (cexcZero (excTable rows)) (bexcZero (excTable rows))
        = cexcZero (excTable rows) + bexcZero (excTable rows) *
            Nat.clog 2 (awrap cseed (cexcZero (excTable rows))
              (bexcZero (excTable rows)) + 2) := by
  obtain ⟨-, -, h1, -, h2⟩ :=
    coefficientPass_awrap cseed (cexcZero (excTable rows)) (bexcZero (excTable rows))
  exact ⟨h1, h2, rfl⟩

/-- **Non-vacuity: the first pass's premise is inhabited at the paper's own
scheduled `L_P`, nondegenerately.**

The empty row list would satisfy `ExcChecked` vacuously, so the premise is
exhibited at a **nonempty** list whose single row has a positive requested
binary length and a positive slope -- the frozen text's own warning at
`06:1577--1579` that retaining `B_exc^0` "is essential: repeated occurrences of
the formal leaf `X` are not silently assigned coefficient one".  `L_P` is the
banked `ParameterSchedule.LPwidth` at `.P0sched`, evaluated, never a numeral,
and its guard `L_P >= 4 >= 1` is the banked `.four_le_LPwidth_sched`.

**BEYOND-PAPER at the recorded pair only:** `(bar c_0, bar b_0) = (1, 1)` is our
value, because the registry's exceptional table is compiler data; the *driver*,
the *shift* and the *search* are all the paper's, evaluated. -/
theorem excPass_premise_inhabited (Ccert s lq2 clU0 zR : ℕ) :
    ∃ rows : List ExcRow, rows ≠ [] ∧
      (∀ r ∈ rows, 0 < r.value ∧ 0 < r.bbar) ∧
      (∀ r ∈ rows,
        ExcChecked (awrap ParameterSchedule.cSeed (cexcZero (excTable rows))
            (bexcZero (excTable rows)))
          (ParameterSchedule.LPwidth (ParameterSchedule.P0sched Ccert s lq2 clU0 zR)) r) := by
  refine ⟨[⟨1, 1, 1⟩], by simp, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨by norm_num, by norm_num⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    have hLP : 4 ≤ ParameterSchedule.LPwidth
        (ParameterSchedule.P0sched Ccert s lq2 clU0 zR) :=
      ParameterSchedule.four_le_LPwidth_sched Ccert s lq2 clU0 zR
    simp only [ExcChecked]
    have h1 : (1 : ℕ) ≤ (1 + 1 * Nat.clog 2
        (awrap ParameterSchedule.cSeed
          (cexcZero (excTable [(⟨1, 1, 1⟩ : ExcRow)]))
          (bexcZero (excTable [(⟨1, 1, 1⟩ : ExcRow)])) + 2)) := by omega
    have h2 : (1 : ℕ) ≤ (ParameterSchedule.LPwidth
        (ParameterSchedule.P0sched Ccert s lq2 clU0 zR) + 2) ^ 2 :=
      Nat.one_le_pow _ _ (by omega)
    calc (1 : ℕ) = 1 * 1 := by norm_num
      _ ≤ _ := Nat.mul_le_mul h1 h2

/-! ## Part 6: `EnvelopeRealization`'s GAP-EXPOSED 2, retired -/

/-- **The second-pass traversal bound, with `hstruct` discharged.**

`EnvelopeRealization.traversalRealization` is consumed by pin at
`Csize := passCsize rows rows3`, and the hypothesis it could not supply --
`hstruct`, the first row of `eq:structural-majorants` -- is now the theorem
`structuralMajorantRow`.  Nothing of that module is restated: only the
`hstruct` binder disappears.

`13-iteration-assembly.tex:300--308` is what the conclusion says: "The
second-pass traversal then bounds every newly constructed auxiliary width other
than the numerical source width, both new logarithmic side lengths, the inverse
tolerances and robustness depths, and the updated public budgets by
`E_{16(c_r+1)}(n)`."

General in the emission, the traversal's two tables, `L`, the exponent, the
source size and the output record. -/
theorem traversalRealization_of_rows (Em : CutoffEmission)
    (rows : List CoeffRow) (rows3 : List ℕ) (L c n : ℕ) (O : SuccessorOutputs)
    (hn : 1 ≤ n) (hL1 : 1 ≤ L)
    (habs : (absorbedCoeff (passCsize rows rows3) c, dExp c, eExp c) ∈ Em.pArgs c)
    (hL : L ≤ (ellN n + 2) ^ (c + 1))
    (hmaj : O.majorised = passValues rows)
    (hchk : ∀ r ∈ rows, RowChecked (L + 2) r)
    (hcut : Em.nStep c ≤ n) :
    ∀ x ∈ O.majorised, x ≤ envE (eExp c) n := by
  refine traversalRealization Em (passCsize rows rows3) L c n O hn habs hL ?_ hcut
  intro x hx
  rw [hmaj] at hx
  exact structuralMajorantRow rows rows3 L hL1 hchk x hx

/-- **The source-width logarithmic row, with its `hstruct` companion
discharged.**

`13-iteration-assembly.tex:312--313` through `06:1703--1704`: "Here `q_2` itself
is not called an auxiliary scale: only `log_2 q_2` appears among the new
logarithmic side lengths."  So the source width's *logarithm* is one of the
traversal's requested roots, and the hypothesis is exactly that -- membership in
the pass's own value list -- rather than a second free bound.

General in every argument. -/
theorem srcWidthLogRealization_of_rows (Em : CutoffEmission)
    (rows : List CoeffRow) (rows3 : List ℕ) (L c n : ℕ) (O : SuccessorOutputs)
    (hn : 1 ≤ n) (hL1 : 1 ≤ L)
    (habs : (absorbedCoeff (passCsize rows rows3) c, dExp c, eExp c) ∈ Em.pArgs c)
    (hL : L ≤ (ellN n + 2) ^ (c + 1))
    (hmem : Nat.clog 2 O.srcWidth ∈ passValues rows)
    (hchk : ∀ r ∈ rows, RowChecked (L + 2) r)
    (hcut : Em.nStep c ≤ n) :
    Nat.clog 2 O.srcWidth ≤ envE (eExp c) n :=
  srcWidthLogRealization Em (passCsize rows rows3) L c n O hn habs hL
    (structuralMajorantRow rows rows3 L hL1 hchk _ hmem) hcut

/-- **The `htraversal` inhabitant, with `hstruct` discharged.**

The banked `EnvelopeRealization.htraversal_of_state` in its exact binder shape,
with the structural row supplied by the traversal instead of assumed.  `L` is
not free here: it is the banked `EnvelopeRealization.normalizedL`, i.e.
`L = clog_2(A_pre)`, and its `L >= 1` side condition is **derived** from the
banked `four_le_normalizedL` rather than assumed.

General in every argument. -/
theorem htraversal_of_state_of_rows (Em : CutoffEmission)
    (rows : List CoeffRow) (rows3 : List ℕ) (bout Bpub zR clE c n : ℕ)
    (S : LevelState) (O : SuccessorOutputs) (hn : 1 ≤ n) (hc : 3 ≤ c)
    (habs : (absorbedCoeff (passCsize rows rows3) c, dExp c, eExp c) ∈ Em.pArgs c)
    (hboutS : bout ∈ S.quantities) (hBpubS : Bpub ∈ S.quantities)
    (hzRS : zR ∈ S.quantities) (hclE : clE ≤ envE c n)
    (hmaj : O.majorised = passValues rows)
    (hchk : ∀ r ∈ rows, RowChecked (normalizedL bout Bpub zR clE + 2) r) :
    Em.nStep c ≤ n → S.UnderEnvelope c n →
      ∀ x ∈ O.majorised, x ≤ envE (16 * (c + 1)) n := by
  have hL1 : 1 ≤ normalizedL bout Bpub zR clE := by
    have := four_le_normalizedL bout Bpub zR clE
    omega
  refine htraversal_of_state Em (passCsize rows rows3) bout Bpub zR clE c n S O hn hc
    habs hboutS hBpubS hzRS hclE ?_
  intro x hx
  rw [hmaj] at hx
  exact structuralMajorantRow rows rows3 _ hL1 hchk x hx

/-- **The `hsrclog` inhabitant, with `hstructSrc` discharged.**

The source-width twin of `htraversal_of_state_of_rows`, and the fourth and last
of `EnvelopeRealization`'s hypothesis-bearing deliverables.  The banked
`EnvelopeRealization.hsrclog_of_state` is consumed by pin in its exact binder
shape, and the hypothesis it could not supply -- `hstructSrc`, the first row of
`eq:structural-majorants` read at the single requested root `clog_2 q_2` -- is
now `structuralMajorantRow` applied at that root's membership in the pass's own
value list.

`06:1703--1704` is why the membership premise is the right one, and why this is
not a second free bound: "Here `q_2` itself is not called an auxiliary scale:
only `log_2 q_2` appears among the new logarithmic side lengths."  So the source
width's *logarithm* is one of the traversal's requested roots, exactly as in
`srcWidthLogRealization_of_rows` -- but here, as in `htraversal_of_state_of_rows`
and unlike there, `L` is **not** free: it is the banked
`EnvelopeRealization.normalizedL`, i.e. `L = clog_2(A_pre)`, its `L >= 1` side
condition is **derived** from the banked `four_le_normalizedL` rather than
assumed, and the conclusion stands behind the two frozen antecedents rather than
unconditionally.  The **exponent is the same** in both: `EnvelopeRealization.lean:538`
reads `def eExp (c : ℕ) : ℕ := 16 * (c + 1)`, so `envE (eExp c) n` and
`envE (16 * (c + 1)) n` are the same term by `rfl` and there is no exponent
difference to claim.

With this and `htraversal_of_state_of_rows`, **both** antecedent slots of
`SuccessorMajorant.successorMajorant` (`SuccessorMajorant.lean:656--662`) are
filled from checked rows alone: `13-iteration-assembly.tex:312--313`'s "its
logarithm remains in the displayed majorant" no longer travels as a
structural-majorant hypothesis at any consumer.

General in every argument. -/
theorem hsrclog_of_state_of_rows (Em : CutoffEmission)
    (rows : List CoeffRow) (rows3 : List ℕ) (bout Bpub zR clE c n : ℕ)
    (S : LevelState) (O : SuccessorOutputs) (hn : 1 ≤ n) (hc : 3 ≤ c)
    (habs : (absorbedCoeff (passCsize rows rows3) c, dExp c, eExp c) ∈ Em.pArgs c)
    (hboutS : bout ∈ S.quantities) (hBpubS : Bpub ∈ S.quantities)
    (hzRS : zR ∈ S.quantities) (hclE : clE ≤ envE c n)
    (hmem : Nat.clog 2 O.srcWidth ∈ passValues rows)
    (hchk : ∀ r ∈ rows, RowChecked (normalizedL bout Bpub zR clE + 2) r) :
    Em.nStep c ≤ n → S.UnderEnvelope c n →
      Nat.clog 2 O.srcWidth ≤ envE (16 * (c + 1)) n := by
  have hL1 : 1 ≤ normalizedL bout Bpub zR clE := by
    have := four_le_normalizedL bout Bpub zR clE
    omega
  exact hsrclog_of_state Em (passCsize rows rows3) bout Bpub zR clE c n S O hn hc
    habs hboutS hBpubS hzRS hclE
    (structuralMajorantRow rows rows3 _ hL1 hchk _ hmem)

/-- **Non-vacuity of the composed premise pair `hmaj`, `hchk`.**

`SuccessorOutputs.majorised` is not a free list: `13-iteration-assembly.tex:303`
fixes its shape as `auxWidths ++ [logRow, logCol] ++ invTolerances ++
robustDepths ++ [budgetD, budgetY]`, so it always contains the four printed
scalar slots.  Equating it to a traversal's value list is therefore a genuine
constraint, and a row list shorter than four could never satisfy it -- which
would make every theorem of Part 6 vacuous through `hmaj` alone.

The pair is exhibited satisfied at a **six-row** list, together with the
structural conclusion, so no `False` follows from combining them.  The row used
is the tight one of `structuralMajorantRow_hypotheses_consistent` and carries the
same BEYOND-PAPER label: the registry's coefficient table is compiler data
(GAP-EXPOSED 2).  General in `L >= 1`. -/
theorem traversalPremises_inhabited (L : ℕ) (hL : 1 ≤ L) :
    ∃ (rows : List CoeffRow) (O : SuccessorOutputs),
      rows.length = 6 ∧
        O.majorised = passValues rows ∧
        (∀ r ∈ rows, RowChecked (L + 2) r) ∧
        (∀ x ∈ O.majorised, x ≤ structuralW (passCsize rows []) L) := by
  set v : ℕ := 2 ^ (L + 2) ^ 8 with hv
  set r0 : CoeffRow := ⟨v, 1, 8, le_refl 8⟩ with hr0
  have hchk0 : RowChecked (L + 2) r0 := by simp [RowChecked, hr0, hv]
  have hC : passCsize [r0, r0, r0, r0, r0, r0] [] = 6561 := by
    simp [passCsize, passRows12, csizeLiteral, maxFrom, hr0]
  refine ⟨[r0, r0, r0, r0, r0, r0],
    ⟨[], v, v, [v], [v], v, v, v⟩, by simp,
    by simp [SuccessorOutputs.majorised, passValues, hr0],
    ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h <;> (subst h; exact hchk0)
  · intro x hx
    rw [hC]
    simp only [SuccessorOutputs.majorised, List.nil_append, List.cons_append,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    have hle : v ≤ structuralW 6561 L :=
      row_le_structuralW L 6561 hL r0 hchk0 (by simp [hr0])
    rcases hx with h | h | h | h | h | h <;> (subst h; exact hle)

/-- **Both antecedent slots of `successorMajorant`, jointly inhabited from
checked rows alone (BEYOND-PAPER).**

`traversalPremises_inhabited` exhibits `hmaj` and `hchk` together, but it says
nothing about the *second* slot's premise
`hmem : clog_2 q_2 ∈ passValues rows`, which both
`srcWidthLogRealization_of_rows` and `hsrclog_of_state_of_rows` carry.  A module
whose headline is that **both** antecedent slots of
`SuccessorMajorant.successorMajorant` (`SuccessorMajorant.lean:656--662`) are
fillable from checked rows alone owes one row list and one output record
satisfying **all three** premises at once, together with both structural
conclusions; a type-level claim standing on premises no exhibited tuple meets
would be vacuous.  That joint tuple is what this exhibits, so no `False` follows
from combining `hmaj`, `hchk` and `hmem`.

The witness extends `traversalPremises_inhabited`'s -- the same tight row
`r0 = (2^{(L+2)^8}, 1, 8)`, checked at driver `L + 2` by `le_refl`, repeated --
and changes the output record in exactly two places:

* `auxWidths := [v]`.  `13-iteration-assembly.tex:303--304` gives `majorised` one
  genuinely variable-length auxiliary-width slot ("every newly constructed
  auxiliary width other than the numerical source width"); leaving it empty
  would exercise only the four printed scalar slots and the two remaining list
  slots.  Here all three list slots are non-empty, so the row count is
  **seven**.
* `srcWidth := 2^v`.  This is the **eighth** field, which `13:303--304` excludes
  from `majorised` by construction -- "other than the numerical source width" --
  so `SuccessorOutputs.majorised` is untouched by the retune and `hmaj` survives
  verbatim.  Then `Nat.clog 2 (2^v) = v` by `Nat.clog_pow`, and `v` is exactly
  what `passValues rows` contains.  That is `06:1703--1704` realized -- "Here
  `q_2` itself is not called an auxiliary scale: only `log_2 q_2` appears among
  the new logarithmic side lengths" -- the source width's *logarithm*, not the
  width, is one of the traversal's requested roots, which is why `hmem` is a
  membership and not a second free bound.

**Why no trivial witness satisfies this.**  `rows = []` fails twice over:
`passValues [] = []` has no member, so `hmem` is unsatisfiable, and
`SuccessorOutputs.majorised` always contains the four printed scalar slots
`logRow, logCol, budgetD, budgetY`, so `hmaj` already forces
`rows.length >= 4`.  Nor does *any* record whose `srcWidth` is a value of the
pass do: at the r1 shape `srcWidth := v` one would need
`Nat.clog 2 v = (L+2)^8` to lie in `passValues rows = [v, ...]`, i.e.
`(L+2)^8 = 2^{(L+2)^8}`, which is false for every `L >= 1`.  It is precisely the
`v` versus `2^v` distinction -- the width against its logarithm -- that the
witness has to get right, which is `06:1703--1704`'s point.

**BEYOND-PAPER, and labelled so**, on the same ground as
`structuralMajorantRow_hypotheses_consistent` and `traversalPremises_inhabited`:
`06:1628--1631` forbids a formalizer to supply the registry's `(C_u, d_u)`
table, so this audits our encoding at a point the paper never prints.  It is
**not** a canonical inhabitation, and it is strictly weaker evidence than the
paper's own application point; that obligation stays registered
(GAP-EXPOSED 2).  General in `L >= 1`. -/
theorem bothSlots_premises_inhabited (L : ℕ) (hL : 1 ≤ L) :
    ∃ (rows : List CoeffRow) (O : SuccessorOutputs),
      rows.length = 7 ∧
        O.auxWidths ≠ [] ∧
        O.majorised = passValues rows ∧
        (∀ r ∈ rows, RowChecked (L + 2) r) ∧
        Nat.clog 2 O.srcWidth ∈ passValues rows ∧
        (∀ x ∈ O.majorised, x ≤ structuralW (passCsize rows []) L) ∧
        Nat.clog 2 O.srcWidth ≤ structuralW (passCsize rows []) L := by
  set v : ℕ := 2 ^ (L + 2) ^ 8 with hv
  set r0 : CoeffRow := ⟨v, 1, 8, le_refl 8⟩ with hr0
  have hchk0 : RowChecked (L + 2) r0 := by simp [RowChecked, hr0, hv]
  have hC : passCsize [r0, r0, r0, r0, r0, r0, r0] [] = 6561 := by
    simp [passCsize, passRows12, csizeLiteral, maxFrom, hr0]
  have hclog : Nat.clog 2 (2 ^ v) = v := Nat.clog_pow 2 v one_lt_two
  have hle : v ≤ structuralW 6561 L :=
    row_le_structuralW L 6561 hL r0 hchk0 (by simp [hr0])
  refine ⟨[r0, r0, r0, r0, r0, r0, r0],
    ⟨[v], v, v, [v], [v], v, v, 2 ^ v⟩, by simp, by simp,
    by simp [SuccessorOutputs.majorised, passValues, hr0],
    ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h <;> (subst h; exact hchk0)
  · simp [hclog, passValues, hr0]
  · intro x hx
    rw [hC]
    simp only [SuccessorOutputs.majorised, List.nil_append, List.cons_append,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h <;> (subst h; exact hle)
  · rw [hC]
    simpa [hclog] using hle

/-! ## Part 7: the canonical inhabitation of `m_{N,i}` and `n_{N,i}`

`SIZE-001`'s registered deferral (7 August 2026), discharged with the paper's
own construction. -/

/-- **`m_N = |Rows(N)|`, evaluated through the paper's construction.**

`08-dense-stage4.tex:145--147` sets `N = A^T`, and `08:154--156` fixes the
orientation convention for the whole section, so a **row** of `N` is a **column**
of `A`.  The column carrier of `A` is `eq:protected-labelled-carriers`
(`08:81--95`) at the frozen multiplicities of `eq:protected-multiplicities`
(`08:98--109`), i.e. the banked `DenseStageFourOpening.ProtColsFrozen`, whose
cardinality `eq:protected-carrier-cardinalities` (`08:111--122`) fixes as
`184 M_0 S_0 D_0`.

This is `12-iteration-specification.tex:255--256`'s `m_{N,i} = |Rows(N_i)|`
**evaluated**, not recorded: no numeral is assigned and no binder is left. -/
def rowsN (F : FiniteSlots.Stage1SlotBinding) (q : ℕ) (Y : Type*) [Fintype Y] : ℕ :=
  Fintype.card (DenseStageFourOpening.ProtColsFrozen F q Y)

/-- **`n_N = |Cols(N)|`, evaluated through the paper's construction.**

By the same `N = A^T` of `08:147`, a column of `N` is a row of `A`, whose
carrier is the banked `DenseStageFourOpening.ProtRowsFrozen` with cardinality
`2^{22} X_0 T_raw V_raw B_raw` (`eq:protected-carrier-cardinalities`).  This is
`12:256--257`'s `n_{N,i} = |Cols(N_i)|` evaluated. -/
def colsN (F : FiniteSlots.Stage1SlotBinding) (V X L₂ : Type*) [Fintype V]
    [Fintype X] [Fintype L₂] : ℕ :=
  Fintype.card (DenseStageFourOpening.ProtRowsFrozen F V X L₂)

/-- **Aux 8 (`eq:protected-carrier-cardinalities` read through the transpose).**
The two evaluated counts are the frozen totals of `08:111--122`, with the
row/column exchange of `08:147` applied once.  Consumes the banked
`DenseStageFourOpening.card_ProtColsFrozen` / `.card_ProtRowsFrozen`; nothing is
recomputed.  General in the Section-8 reservoir data. -/
theorem paperN_counts_eq (F : FiniteSlots.Stage1SlotBinding) (q : ℕ)
    (V X L₂ Y : Type*) [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y] :
    rowsN F q Y =
        184 * (Fintype.card (DenseStageFourOpening.Omega F q Y) *
          Fintype.card (DenseStageFourOpening.SelCar F q Y) *
          Fintype.card (DenseStageFourOpening.DiagCar F q Y)) ∧
      colsN F V X L₂ =
        2 ^ 22 * (Fintype.card (DenseStageFourOpening.RowsB F V X L₂) *
          Fintype.card (DenseStageFourOpening.TempCar F L₂) *
          Fintype.card (DenseStageFourOpening.VertCar F V X) *
          Fintype.card (DenseStageFourOpening.BlockCar F X)) :=
  ⟨DenseStageFourOpening.card_ProtColsFrozen F q Y,
    DenseStageFourOpening.card_ProtRowsFrozen F V X L₂⟩

/-- **Aux 9 (the two evaluated counts are the carriers of the paper's own `N`).**

Stated in the kernel, on the matrix `N = A^T` the frozen section actually builds:
`DenseStageFourOpening.transposeN` applied to `.protectedAFrozen`.  The two sides
are the banked `BridgeOutputEquality.rowsCard` / `.colsCard` of that matrix, so
`rowsN` and `colsN` are not merely numbers that happen to agree with the display
-- they are the cardinalities of the carriers `N` is defined on.  General. -/
theorem paperN_counts_are_the_carriers {F : FiniteSlots.Stage1SlotBinding} {q : ℕ}
    {V X L₂ Y : Type*} [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y]
    (Bmat : DenseStageFourOpening.RowsB F V X L₂ →
      DenseStageFourOpening.Omega F q Y → Bool) (y₀ : Y) :
    BridgeOutputEquality.rowsCard
        (DenseStageFourOpening.transposeN
          (DenseStageFourOpening.protectedAFrozen Bmat y₀)) = rowsN F q Y ∧
      BridgeOutputEquality.colsCard
        (DenseStageFourOpening.transposeN
          (DenseStageFourOpening.protectedAFrozen Bmat y₀)) = colsN F V X L₂ :=
  ⟨rfl, rfl⟩

/-- **Aux 10 (the two counts are nondegenerate at legal parameters).**

`184 <= m_N` and `2^{22} <= n_N`: the protection really is a `184`-fold and a
`2^{22}`-fold blow-up, which is what the frozen masses `1/184` and `2^{-22}`
mean.  Consumes the banked
`DenseStageFourOpening.protectedAFrozen_carriers_nondegenerate` by pin; the
legality inputs are the frozen `0 < q_2` of `06:124` and `s >= 4` of `08:402`,
plus inhabitants of the four reservoir index carriers. -/
theorem paperN_counts_nondegenerate (F : FiniteSlots.Stage1SlotBinding) {q : ℕ}
    {V X L₂ Y : Type*} [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y]
    (hq : 0 < q) (hs : 4 ≤ F.s) (y₀ : Y) (v₀ : V) (x₀ : X) (l₀ : L₂) :
    184 ≤ rowsN F q Y ∧ 2 ^ 22 ≤ colsN F V X L₂ :=
  DenseStageFourOpening.protectedAFrozen_carriers_nondegenerate F hq hs y₀ v₀ x₀ l₀

/-- **The two `LevelCarrierSpec` guards `m_{N,i} >= 1`, `n_{N,i} >= 1`,
derived** from the frozen `184`- and `2^{22}`-fold blow-up rather than assumed.
Stated as one pair so that both halves of the Section-8 reservoir data really
occur in the type. -/
theorem paperN_counts_pos (F : FiniteSlots.Stage1SlotBinding) {q : ℕ}
    {V X L₂ Y : Type*} [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y]
    (hq : 0 < q) (hs : 4 ≤ F.s) (y₀ : Y) (v₀ : V) (x₀ : X) (l₀ : L₂) :
    1 ≤ rowsN F q Y ∧ 1 ≤ colsN F V X L₂ := by
  obtain ⟨hr, hc⟩ := paperN_counts_nondegenerate (V := V) (X := X) (L₂ := L₂)
    F hq hs y₀ v₀ x₀ l₀
  have h : (1 : ℕ) ≤ 2 ^ 22 := Nat.one_le_pow _ _ (by norm_num)
  exact ⟨by omega, by omega⟩

/-- **The paper's own carrier specification, with the two Stage-4 counts
evaluated.**

`FixedLevelCarriers.paperSeedSpec` is the banked canonical instance of
`12:360--368`, in which every schedule field is the paper's own evaluated value
and only `mN`, `nN` were left as binders (that module's GAP-EXPOSED 2, registered
against `SIZE-001`).  Here those two binders receive the paper's own
construction: `m_{N,i} = |Rows(N)|` and `n_{N,i} = |Cols(N)|` for `N = A^T` over
the protected duplicate, with the positivity guards **derived** from the frozen
`184`- and `2^{22}`-fold blow-up rather than assumed.

**Disclosed reading (GAP-EXPOSED 5).**  The Section-8 reservoir data
`(F, q, V, X, L_2, Y)` is held **level-uniformly**: producing level `i`'s data
from the previous level's output `R_i` is `STAGE1-001` .. `WRAP-001`, none of
which is in Lean, so the instance is exhibited at one legal choice of that data.
That is strictly narrower than the previous deferral -- the counts are no longer
recorded integers -- and it is what remains open. -/
noncomputable def paperCarrierSpec (F : FiniteSlots.Stage1SlotBinding) {q : ℕ}
    {V X L₂ Y : Type*} [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y]
    (hq : 0 < q) (hs : 4 ≤ F.s) (y₀ : Y) (v₀ : V) (x₀ : X) (l₀ : L₂)
    (n C0 B0 Ccert sPar lq2 clU0 zR : ℕ) (dv zeta : ℝ) :
    FixedLevelCarriers.LevelCarrierSpec :=
  FixedLevelCarriers.paperSeedSpec n C0 B0 Ccert sPar lq2 clU0 zR dv zeta
    (fun _ => rowsN F q Y) (fun _ => colsN F V X L₂)
    (fun _ => (paperN_counts_pos (V := V) (X := X) (L₂ := L₂) F hq hs y₀ v₀ x₀ l₀).1)
    (fun _ => (paperN_counts_pos (V := V) (X := X) (L₂ := L₂) F hq hs y₀ v₀ x₀ l₀).2)

/-- **Canonical inhabitation, discharged: the exact carrier recurrence fires at
the paper's own pre-wrapper matrix.**

`FixedLevelCarriers.fixedLevelCarriers_realized` is consumed by pin at
`N := transposeN (protectedAFrozen Bmat y_0)` -- the frozen `N = A^T` of
`08:147` over the protected duplicate of `eq:protected-labelled-carriers` at the
frozen multiplicities -- and both realization hypotheses hold **by `rfl`**,
because the specification's two counts *are* that matrix's carrier
cardinalities.

This **supersedes** `FixedLevelCarriers.fixedLevelCarriers_realized_fires`,
whose count-realizing stand-in `fun (_ : Fin (S.mN i)) (_ : Fin (S.nN i)) => false`
was labelled NON-FIDELITY and certified only that the hypothesis pair was
satisfiable.  Here the matrix is the paper's construction, so
`eq:fixed-level-carriers` (`12:260--265`) is delivered at the paper's own `N`.

General in the Section-8 data, in the raw Stage-4 matrix `B`, in the schedule
inputs and in the level index. -/
theorem paperCarrierSpec_realized (F : FiniteSlots.Stage1SlotBinding) {q : ℕ}
    {V X L₂ Y : Type*} [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y]
    (hq : 0 < q) (hs : 4 ≤ F.s) (y₀ : Y) (v₀ : V) (x₀ : X) (l₀ : L₂)
    (Bmat : DenseStageFourOpening.RowsB F V X L₂ →
      DenseStageFourOpening.Omega F q Y → Bool)
    (n C0 B0 Ccert sPar lq2 clU0 zR : ℕ) (dv zeta : ℝ) (i : ℕ) :
    BridgeOutputEquality.rowsCard
        (OneLevelCompletion.levelOutput
          (DenseStageFourOpening.transposeN
            (DenseStageFourOpening.protectedAFrozen Bmat y₀))
          ((paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR
            dv zeta).qExp i)
          ((paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR
            dv zeta).bout i)
          ((paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR
            dv zeta).dU i))
        = (paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR
            dv zeta).rowCarrier (i + 1) ∧
      BridgeOutputEquality.colsCard
        (OneLevelCompletion.levelOutput
          (DenseStageFourOpening.transposeN
            (DenseStageFourOpening.protectedAFrozen Bmat y₀))
          ((paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR
            dv zeta).qExp i)
          ((paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR
            dv zeta).bout i)
          ((paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR
            dv zeta).dU i))
        = (paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR
            dv zeta).colCarrier (i + 1) :=
  FixedLevelCarriers.fixedLevelCarriers_realized
    (paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR dv zeta)
    i _ rfl rfl

/-- **Statement pole: the paper's counts are not the stand-in's.**

`FixedLevelCarriers.fixedLevelCarriers_realized_fires` realizes the counts with
a matrix on `Fin (m_N) x Fin (n_N)` carrying the constant value `false`; the
paper's `N` carries the protected duplicate's entries and lives on the labelled
carriers.  The separation shown here is on the *carrier types*: the paper's row
carrier has at least `184` elements at legal parameters, so the specification's
`m_{N,i}` is bounded below by the frozen blow-up factor and cannot be the
degenerate `1` a collapsed stand-in would allow.  Hence the discharge is content
and not a renaming. -/
theorem paperCarrierSpec_counts_are_not_the_stand_in
    (F : FiniteSlots.Stage1SlotBinding) {q : ℕ} {V X L₂ Y : Type*} [Fintype V]
    [Fintype X] [Fintype L₂] [Fintype Y] (hq : 0 < q) (hs : 4 ≤ F.s) (y₀ : Y)
    (v₀ : V) (x₀ : X) (l₀ : L₂)
    (n C0 B0 Ccert sPar lq2 clU0 zR : ℕ) (dv zeta : ℝ) (i : ℕ) :
    184 ≤ (paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR
        dv zeta).mN i ∧
      2 ^ 22 ≤ (paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR
        dv zeta).nN i :=
  paperN_counts_nondegenerate (V := V) (X := X) (L₂ := L₂) F hq hs y₀ v₀ x₀ l₀

end EthInapproximability.ParameterizedNP.CoefficientTraversal
