import EthInapproximability.ParameterizedNP.SuccessorMajorant
import EthInapproximability.ParameterizedNP.PilotPCut

/-!
# Parameterized NP route: the envelope realization

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: opened under **`PARAM-001`** (the schedule-compiler thread), wiring
into `SIZE-001`'s `SuccessorMajorant`.

`SuccessorMajorant.lean` (tranche 62) landed `eq:iteration-successor-majorant`
with the second-pass traversal carried as a **named hypothesis** `htraversal`,
and recorded **GAP-EXPOSED 7**: no instance in that tranche inhabited
`htraversal`, so the composed two-sided width bound
`47104000 b_i q_i <= Q_i <= E_{c_{r+1}}(n)` had no in-tranche witness.  This
module builds that inhabitant **as the paper's own construction**, by evaluating
the schedule's definitional chain at the paper's inputs.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

## The frozen chain this module evaluates

The proof of `thm:eff-ledger` closes its `Successor_16` obligation root by root,
not from a degree annotation.  `02-mechanical-contract.tex:1373--1389`, opened
and read first-hand this tranche:

```
After (eq:L-ell-sandwich), each of these four cases is bounded by
     2^{C(l(n)+2)^{8(c+1)}}
for its recorded integer coefficient C.  Put d_c = 8(c+1) and e_c = 16(c+1).
The absorbed PCut(2^{d_c}C, d_c, e_c) successor row emitted in C6 has root at
most R(c), while l(n) - 2 >= R(c).  Its persistence predicate at that exact
index, followed by lem:shifted-pcut-absorption, proves
     C(l(n)+2)^{d_c} <= l(n)^{e_c}.
Thus every named root is at most E_{16(c+1)}(n).
```

Five frozen displays supply the five links, and every one of them is opened at
its own anchor rather than recalled:

1. `eq:structural-majorants` (`06-parameter-schedule.tex`, label line 1701,
   display lines 1691--1702): "every new logarithmic side length and auxiliary
   scale `<= W(L) := 2^{C_size L^8}`".  `W` is the **banked**
   `SizePropagation.structuralW`, consumed by pin and not restated.
2. `eq:L-ell-sandwich` (label line 1849, display line 1848):
   `l(n) - 2 <= L <= (l(n)+2)^{c+1}`, with lines 1851--1853: "The lower bound
   follows from the normalised source size, and the upper bound from the
   incoming `E_c(n)` bounds and sparsity of the source graph."  The **upper**
   half is what the successor argument uses, and this module **derives** it
   (`lSandwich_upper`) from `L = clog_2(A_pre)` (`06:1869`) and the incoming
   envelope, rather than assuming it.
3. `eq:successor-pcut-normal-form` (label line 1933, display lines 1930--1934):
   "if a C7 root has the checked pre-cutoff row `u <= 2^{C_u(l(n)+2)^{d_c}}`,
   `d_c = 8(c+1)`, `e_c = 16(c+1)`, then `P(c)` contains exactly the absorbed
   tuple `(2^{d_c}C_u, d_c, e_c)`."
4. `eq:persistent-cutoffs` (label line 1810, display lines 1797--1811) and
   `eq:R-exact` (label line 1951, display lines 1944--1952), `eq:nstep`
   (label line 1956): the three least-value searches, their literal maximum
   `R(c)`, and `n_step(c) = 2^{2^{R(c)+2}}`.
5. `lem:shifted-pcut-absorption` (label line 1819, statement 1818--1829, proof
   1831--1844), already **banked** as `PilotPCut.pCut_shifted_certificate` with
   `PilotPCut.PCutPred`; both are consumed by pin and neither is restated.

The eligibility step is `13-iteration-assembly.tex:246--252`: "If
`n >= n_step(c)`, then `n + 16 > 2^{2^{R(c)+2}}`.  Since `l(n)` is the least
integer `r >= 2` for which `n + 16 <= 2^{2^r}`, this implies `l(n) >= R(c)+3`,
and in particular `l(n) >= R(c)+2`."  It is proved here (`ellN_ge_of_cutoff`)
from the banked `IterationAssembly.ellN_spec`.

## What lands

* `ECutPred`, `DCutPred`, `eCut`, `pCut`, `dCut` -- the three frozen searches of
  `eq:persistent-cutoffs`, transcribed as printed.  `PCutPred` itself is the
  banked `PilotPCut.PCutPred` and is **not** restated.  Termination is proved
  for `PCut` at the frozen side condition `e > d` (`pCut_nonempty`), which is
  the only one the successor argument evaluates.
* `CutoffEmission` -- the four finite argument lists `F(c)`, `E(c)`, `P(c)`,
  `D(c)` of `06:1855--1860`, as **data only**, with `R` the literal maximum of
  `eq:R-exact` and `nStep` the display `eq:nstep`.  No `Prop` field; the
  compiler's own schema and numerical checks (`SchemaChecked`, `NumChecked`) are
  **not** modelled and are not claimed (GAP-EXPOSED 1).
* `successorRootBound` -- the frozen five-line argument of `02:1373--1389` in
  full: a root with the checked pre-cutoff row, whose absorbed tuple is emitted,
  is at most `E_{16(c+1)}(n)` once `n >= n_step(c)`.
* `normalizedL`, `lSandwich_upper` -- `L = clog_2(A_pre)` (`06:1869`) over the
  banked `ParameterSchedule.Apre`, and the **derived** upper half of
  `eq:L-ell-sandwich`.
* `traversalRealization`, `srcWidthLogRealization`, `htraversal_of_state`,
  `hsrclog_of_state` -- the two `PARAM-001` hypotheses of
  `SuccessorMajorant`, **built rather than assumed**, in exactly the binder
  shape those theorems expect.
* `successorMajorant_realized`, `successorMajorant_chains_realized`,
  `iteratedStateMajorant_realized`, `sourceWidthSeparate_realized`,
  `dominantWidth_enveloped_realized`, `dominantRowSide_enveloped_realized` --
  the **six** pending `SuccessorMajorant` deliverables, each consumed by pin and
  re-delivered with its `htraversal` (and, where present, `hsrclog`) discharged.
* `envelopeRealization_closes_the_two_sided_bound` and
  `dominantWidth_two_sided_at_paperSpec` -- **GAP-EXPOSED 7 closed**: the
  composed bound `47104000 b_i q_i <= Q_i <= E_{c_{r+1}}(n)` and the carrier
  chain `q_i <= ceil(log_2 m_{i+1}) <= O.logRow <= E_{c_{r+1}}(n)` now have an
  in-tranche witness at the paper's own `FixedLevelCarriers.paperSeedSpec`, on
  the record `enveloping_premises_inhabited` exhibits.
* `structuralRow_satisfiable`, `twoSidedBound_bundle_consistent` and
  `envelopeRealization_hypotheses_consistent` -- the non-vacuity battery: the one
  new premise is never empty, and the principal deliverable's full hypothesis
  bundle is exhibited satisfied **together with all of its conclusions**, so no
  `False` derives from it.

## DEFINED-vs-FREE

* **DEFINED, reified and evaluated, never assigned a numeral:** `ECut`, `PCut`,
  `DCut` (`eq:persistent-cutoffs`), `R(c)` (`eq:R-exact`), `n_step(c)`
  (`eq:nstep`), `d_c` and `e_c` (`02:1377--1378`, `06:1927`), the absorbed
  coefficient `2^{d_c}C_u` (`eq:successor-pcut-normal-form`), `W(L)` (banked
  `structuralW`), `L = clog_2(A_pre)` (`06:1869`) over the banked
  `ParameterSchedule.Apre`, `E_c(n)` and `l(n)` (banked
  `IterationAssembly.envE`, `.ellN`), `c_j` (banked `.cexp`).
* **FREE in the paper itself, therefore binders:** the recorded coefficient
  `C_size` (`eq:Csize-literal-producer` reads it off the registry's coefficient
  table, which is compiler data -- the banked `SizePropagation.csizeLiteral` is
  the producer, and its own floor `C_size >= 2` is *not* imposed here because
  the successor argument does not use it, and imposing an unused hypothesis
  would be over-strong); the four `A_pre` inputs `b_out`, `B_pub`, `z_R`,
  `clog_2(|E|+2)`; the emitted lists themselves.
* Where a probe needs a value at a free input, it takes the frozen producer's
  **evaluated** output (`csizeLiteral [] []`), never a bare numeral, and the
  probe is labelled BEYOND-PAPER.

## Reader counterparts

The reader artifact of the same frozen release,
`routes/parameterized-np/reader-facing/sections/`, was opened first-hand this
tranche and every candidate read in place.

**Three reader items are claimed, by three distinct declarations, none of them
previously assigned.**

* `05-iteration.tex:201--204` -- "There are the total computable successor
  `F(c) = 16(c+1)`, a total computable cutoff `n_step : N -> N`, and a
  deterministic parameter producer with the following property." -- the
  reader's statement that the cutoff is a total computable function of the
  exponent, claimed by `CutoffEmission.nStep`.  It is theorem statement text,
  not proof prose.  The earlier rows on that file take `:109`, `:176`,
  `:194--196`, `:221--226`, `:226--229`, `:272`, `:278--280`, `:280--283`,
  `:289`, `:308--310`, `:318--357` and `:349--351`; none reaches 201--204.
* `C-effectivity-details.tex:82--84` -- "Its nodes contain exact integer or
  rational operations, named analytic lemmas, or least cutoffs for persistent
  inequalities." -- the reader's one naming of the persistent-inequality
  cutoffs, claimed by `pCut`, the single one of the three searches this module
  evaluates.  Reader appendix C had **no** assignment in the ledger or the
  crosswalk before this row.
* `C-effectivity-details.tex:86--88` -- "Because the graph is finite and every
  search has an explicit terminating comparison, this is a total algorithm." --
  the reader's termination claim, claimed by `pCut_nonempty`.

Both appendix-C sentences are subsection main text, not inside a proof
environment.

**No reader item is claimed by any other declaration here, and the reason is
recorded.**  The reader never prints `ECut`, `DCut`, `R(c)`, `C_size`, `W(L)`,
the pre-cutoff row, the absorbed tuple, or the `L`-sandwich: a search of all
nine reader section files for `PCut`, `ECut`, `DCut`, `C_{\mathrm{size}}`,
`cutoff` and `persisten` returns, besides the three items above, only
`05-iteration.tex:245--246` ("Every eventual comparison is decided by a
terminating integer cutoff search.  Their maximum defines `n_step(c)`.") and
`:247--248` ("The successor calculation bounds every named output root by
`E_{16(c+1)}(n)`."), **both inside `\begin{proof}`**, hence proof prose, which
the reader-counterpart rule forbids citing as a statement.  `ECutPred`,
`DCutPred`, `eCut` and `dCut` therefore claim **no** reader item: the reader
names all three searches in the single sentence already assigned to `pCut`, and
assigning it twice is what the rule forbids.  The reader's one displayed
successor bound, `thm:paper-effective-level`'s
`z(N), q, Q, z(R^+), D^+, Y^+ <= E_{F(c)}(n)` (`05-iteration.tex:221--226`), is
**already assigned** to `SizePropagation.effectiveParameterSchedule`, and
re-citing it would be the same double assignment.

Crosswalk: no new row; the three assignments and the compiler's remaining
Lean-pending status are recorded in the existing row **6, "Simultaneous
parameters and size"**, of `READER_CROSSWALK.md`, which is `PARAM-001`'s row.

## Status and dependencies

* Proof status: **new (elementary)** throughout.  Every declaration is a
  transcription of a frozen display, a general property of that transcription,
  or a composition of banked results.  No communication-complexity lemma is
  introduced, adapted or re-proved, and no banked module is edited.
* Consumed by pin, never restated: `PilotPCut.PCutPred`,
  `.pCut_shifted_certificate`; `IterationAssembly.ellN`, `.ellN_spec`, `.envE`,
  `.cexp`, `.cexp_zero`, `.nval`, `.literalMax`, `.literalMax_cons`,
  `.le_literalMax`; `SizePropagation.structuralW`, `.csizeLiteral`,
  `.two_le_ellN`; `ParameterSchedule.Apre`, `.sixteen_le_Apre`,
  `.lt_clog_of_pow_lt`; `SuccessorMajorant.LevelState`, `.SuccessorOutputs`,
  `.successorMajorant`, `.successorMajorant_chains`, `.iteratedStateMajorant`,
  `.sourceWidthSeparate`, `.dominantWidth_enveloped`,
  `.dominantRowSide_enveloped`, `.enveloping_premises_inhabited`,
  `.mem_majorised_of_mem_auxWidths`; `DominantWidthBound.ScheduleTolerance`,
  `.paperSeedSpec_scheduleTolerance`; `FixedLevelCarriers.LevelCarrierSpec`,
  `.paperSeedSpec`.
* Imports: `SuccessorMajorant` and `PilotPCut`, hence transitively
  `DominantWidthBound`, `PaddingAndClock`, `FixedLevelCarriers`,
  `SizePropagation`, `IterationAssembly`, `ParameterSchedule`, `EntryGates` and
  `EthInapproximability.Prelude`, hence `LegacyNPCC.Core` (project-axiom-free)
  and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is **not** imported, so the
  cited AGHP balanced-family axiom is not in scope, and there is no contact with
  `EXPANDER-001` (which by design has no Lean declaration).
* External adapters: none.  Nothing here is axiomatized; no new `axiom`, no
  opaque certificate.
* Axiom surface (Appendix D, and `#print axioms`): at most `propext`,
  `Classical.choice`, `Quot.sound`.

## Faithfulness notes (mechanical rules M1--M10)

* **The one new structure carries data only.**  `CutoffEmission` has exactly the
  four emitted argument lists of `06:1855--1860` and nothing else: no `Prop`
  field, no complexity or robustness conclusion, no promise branch, and in
  particular **not** the successor bound itself, which is a theorem about the
  record.  No field restates a derived telescope: `R` and `nStep` are `def`s
  computed from the fields, not stored.
* **Both interlace widths stay distinct.**  `q_i` and `Q_i` enter only through
  the banked `FixedLevelCarriers.LevelCarrierSpec.q` and `.Q`, and the width
  `Q_i` is seen only as a member of the auxiliary-width list.
* **Every comparison is transcribed as printed.**  `l(n) >= R(c)+3` and
  `l(n)-2 >= R(c)` are non-strict as at `13:250--252`; the `PCut` predicate's
  `A(r+2)^d <= (r+2)^e` is non-strict as at `06:1802`; the successor conclusion
  `<= E_{16(c+1)}(n)` is non-strict as at `02:547--551`.
* **Trivial-witness poles.**  `cutoff_hypothesis_not_free` exhibits, at every
  exponent and source size, a coefficient and a root satisfying the pre-cutoff
  row whose value exceeds `E_{16(c+1)}(n)`, so the emitted-tuple and cutoff
  hypotheses of `successorRootBound` carry the whole content.
  `absorbed_tuple_is_not_the_raw_tuple` shows in the kernel that the emitted
  first component is `2^{d_c}C_u` and not `C_u`, so
  `eq:successor-pcut-normal-form`'s absorption is not decoration.
  `dominantWidth_two_sided_at_paperSpec` pins its existential witness by two
  equations (`auxWidths = [Q_i]` and `logRow = ceil(log_2 m_{i+1})`), so the
  empty record fails on the first conjunct.

## GAP-EXPOSED

1. **The compiler itself is not built.**  `thm:eff-ledger`'s existential --
   the universal configuration `K_*`, the certificate function
   `c |-> Cert_c`, the byte machine `A_cert`, `SchemaChecked` and `NumChecked`
   -- has no Lean declaration and none is given.  What is proved here is the
   frozen *derivation* `02:1373--1389`: **given** the emitted absorbed tuple and
   the checked pre-cutoff row, the successor bound follows.  Nothing below
   asserts that any concrete compiler emits them, and nothing below is an axiom.
2. **The pre-cutoff rows are the traversal's own output and are named, not
   derived.**  `eq:structural-majorants`' first row is the conclusion of the
   two-pass coefficient traversal over the whole Section-6 gate list; that
   traversal is not formalized, so `hstruct` (and its source-width companion) is
   an explicit hypothesis at the frozen display, with `structuralW_le_preCutoffRow`
   supplying the frozen substitution that turns it into `02:1375`'s row and
   `structuralRow_satisfiable` showing it is never an empty premise.  This
   is a PARK with the dependency named: **the second-pass coefficient traversal
   of `06:1660--1706`**.
3. **`ECut` and `DCut` termination is not proved.**  `06:1812--1817` asserts
   that each of the three searches terminates; only the `PCut` case is used by
   the successor argument and only it is proved (`pCut_nonempty`).  `eCut` and
   `dCut` are `sInf` of their frozen predicate sets, so on an empty set they
   return the junk value `0`.  That can only **lower** `R(c)`, hence lower
   `n_step(c)`, hence **weaken** the hypothesis `n >= n_step(c)`; no conclusion
   is strengthened by it.  `R_mono` records the direction in the kernel.
4. **This is still a candidate tuple, not a realized one.**
   `13:313--315` -- "This is a successor statement for a candidate tuple inside
   the exact balanced-family envelope.  The realization theorem supplies the
   actual tuple and trace on the same index."  `thm:effective-materialization`
   and `cor:realized-effective-prefix` (`MATERIALIZE-001`) are untouched.
   `SuccessorMajorant`'s GAP-EXPOSED 3 -- canonical inhabitation of
   `SuccessorOutputs` by the paper's own realized outputs -- stays **registered
   as deferred**; what closes here is GAP-EXPOSED 7, the *witness for the
   composed two-sided bound*, not the realization of the output tuple.
5. **The two consistency probes claim no legality.**
   `envelopeRealization_hypotheses_consistent` is **BEYOND-PAPER**: it audits our
   encoding at a point the paper never visits (a one-row emission at the seed
   exponent).  `twoSidedBound_bundle_consistent` exhibits the principal
   deliverable's full bundle satisfied together with all its conclusions, at an
   arbitrary `ScheduleTolerance` specification and hence at the paper's own
   `paperSeedSpec`, but its incoming state, its four `A_pre` inputs and its
   recorded coefficient are **probe values**, not the frozen producer's outputs.
   Both are strictly weaker evidence than the canonical statement
   `dominantWidth_two_sided_at_paperSpec` and stand in for nothing.
6. **No asymptotic statement is made.**  `E_c(n) = n^{o(1)}` is not claimed in
   either direction.
7. **No route completion is claimed.**  Stages 1--4, the materialization, the
   slow clock beyond what is banked, and the ETH consequence are untouched.
-/

namespace EthInapproximability.ParameterizedNP.EnvelopeRealization

open EthInapproximability.ParameterizedNP.IterationAssembly
open EthInapproximability.ParameterizedNP.SizePropagation
open EthInapproximability.ParameterizedNP.DominantWidthBound
open EthInapproximability.ParameterizedNP.SuccessorMajorant

/-! ## Part 1: the three persistent cutoff searches (`eq:persistent-cutoffs`) -/

/-- **`ECut(A,d) = min{r >= 2 : 2^{r-2} >= A(r+2)^d, (r+3)^d <= 2(r+2)^d}`** --
`eq:persistent-cutoffs` (`06-parameter-schedule.tex`, label line 1810, display
lines 1797--1811), first clause.

Both conditions of the frozen brace are transcribed, in the printed order, and
the frozen `r - 2` is the ordinary truncated subtraction, which is exact on the
search domain `r >= 2`. -/
def ECutPred (A d r : ℕ) : Prop :=
  2 ≤ r ∧ A * (r + 2) ^ d ≤ 2 ^ (r - 2) ∧ (r + 3) ^ d ≤ 2 * (r + 2) ^ d

/-- **`DCut(A,d) = min{r >= 2 : 2^{r^2} >= A(r+2)^d, (r+3)^d <= 2^{2r+1}(r+2)^d}`**
-- `eq:persistent-cutoffs`, third clause, both conditions as printed. -/
def DCutPred (A d r : ℕ) : Prop :=
  2 ≤ r ∧ A * (r + 2) ^ d ≤ 2 ^ r ^ 2 ∧ (r + 3) ^ d ≤ 2 ^ (2 * r + 1) * (r + 2) ^ d

/-- **`ECut(A,d)`**, the least-value search of `eq:persistent-cutoffs`.

`sInf` is the frozen `min`.  Termination is asserted by `06:1812--1817` and is
**not proved here** (GAP-EXPOSED 3): on an empty predicate set this returns `0`,
which can only lower `R(c)` and hence weaken the cutoff hypothesis. -/
noncomputable def eCut (A d : ℕ) : ℕ := sInf {r | ECutPred A d r}

/-- **`PCut(A,d,e)`**, the least-value search of `eq:persistent-cutoffs`,
second clause, over the **banked** `PilotPCut.PCutPred`
(`2 <= r` and `A(r+2)^d <= (r+2)^e`), which is consumed by pin and not
restated.  Termination at the frozen side condition `e > d` is `pCut_nonempty`
below.

Reader counterpart: `C-effectivity-details.tex:82--84`, "Its nodes contain exact
integer or rational operations, named analytic lemmas, or least cutoffs for
persistent inequalities."  That sentence names all three searches at once and is
claimed here, once; `ECutPred`, `DCutPred`, `eCut` and `dCut` claim no reader
item. -/
noncomputable def pCut (A d e : ℕ) : ℕ := sInf {r | PCutPred A d e r}

/-- **`DCut(A,d)`**, the least-value search of `eq:persistent-cutoffs`, third
clause.  Termination is asserted at `06:1812--1817` and not proved here
(GAP-EXPOSED 3); see `eCut`. -/
noncomputable def dCut (A d : ℕ) : ℕ := sInf {r | DCutPred A d r}

/-- **Aux 1 (the frozen `PCut` search terminates at its own side condition).**

`06:1796` defines the three cutoffs "for positive integers `A, d`, and `e > d`",
and `06:1812--1813` records "Each search terminates".  At `e > d` the index
`r = max{2, A}` already satisfies the predicate, because
`(r+2)^{e-d} >= r + 2 >= A`.  This is the one termination claim the successor
argument evaluates.  General in all three arguments.

Reader counterpart: `C-effectivity-details.tex:86--88`, "Because the graph is
finite and every search has an explicit terminating comparison, this is a total
algorithm." -/
theorem pCut_nonempty (A d e : ℕ) (hde : d < e) :
    {r | PCutPred A d e r}.Nonempty := by
  refine ⟨max 2 A, le_max_left 2 A, ?_⟩
  have hA : A ≤ max 2 A + 2 := le_trans (le_max_right 2 A) (by omega)
  have h1 : (max 2 A + 2) ^ 1 ≤ (max 2 A + 2) ^ (e - d) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  rw [pow_one] at h1
  calc A * (max 2 A + 2) ^ d
      ≤ (max 2 A + 2) ^ (e - d) * (max 2 A + 2) ^ d :=
        Nat.mul_le_mul_right _ (le_trans hA h1)
    _ = (max 2 A + 2) ^ (e - d + d) := (pow_add _ _ _).symm
    _ = (max 2 A + 2) ^ e := by congr 1; omega

/-- **Aux 2 (the emitted `PCut` root satisfies its own predicate).**

`Nat.sInf_mem` at `pCut_nonempty`: the frozen `min` really is attained, so the
stored root is usable.  General. -/
theorem pCut_spec (A d e : ℕ) (hde : d < e) : PCutPred A d e (pCut A d e) :=
  Nat.sInf_mem (pCut_nonempty A d e hde)

/-- **Aux 3 (`PCut` persistence: the predicate survives every larger index).**

`06:1813--1817`: "each predicate remains true for every larger `r` ... in
`PCut`, the quotient power is nondecreasing."  Transcribed exactly: cancel the
common `(r+2)^d`, read off `A <= (r+2)^{e-d}`, and enlarge the base.  This is
the step `02:1381--1383` calls "its persistence predicate at that exact index".
General in the coefficient, both degrees and both indices. -/
theorem pCutPred_persist {A d e r r' : ℕ} (hde : d ≤ e) (h : PCutPred A d e r)
    (hr : r ≤ r') : PCutPred A d e r' := by
  obtain ⟨h2, hle⟩ := h
  refine ⟨by omega, ?_⟩
  have hpos : 0 < (r + 2) ^ d := pow_pos (by omega) d
  have hsplit : (r + 2) ^ e = (r + 2) ^ (e - d) * (r + 2) ^ d := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit] at hle
  have hA : A ≤ (r + 2) ^ (e - d) := Nat.le_of_mul_le_mul_right hle hpos
  have hmono : (r + 2) ^ (e - d) ≤ (r' + 2) ^ (e - d) :=
    Nat.pow_le_pow_left (by omega) _
  have hsplit' : (r' + 2) ^ e = (r' + 2) ^ (e - d) * (r' + 2) ^ d := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit']
  exact Nat.mul_le_mul_right _ (le_trans hA hmono)

/-! ## Part 2: the emitted argument lists, `R(c)` and `n_step(c)` -/

/-- **The four finite argument lists the normalization program emits at exponent
`c`** -- `06-parameter-schedule.tex:1855--1860`: "Let `E(c) subset N^2`,
`P(c) subset N^3`, and `D(c) subset N^2` be the finite lists of arguments it
emits for `ECut`, `PCut`, and `DCut`, respectively", together with
`06:1939--1941`, "Fixed rational gates emit their directly checked constant
cutoff; collect these in the finite set `F(c)`."

**Data only** (rules M1, M2, M4).  There is no `Prop` field: the compiler's own
`SchemaChecked` and `NumChecked` predicates are *not* modelled (GAP-EXPOSED 1),
the successor bound is a theorem about this record and never a field of it, and
`R` and `nStep` below are computed rather than stored, so no field restates a
derived telescope.  The lists are functions of the exponent because
`thm:eff-ledger`(b) fixes `Cert : N -> EffectiveScheduleCertificate` before the
recursion. -/
structure CutoffEmission where
  /-- `F(c)`, the directly checked constant cutoffs of the fixed rational gates
  (`06:1939--1941`). -/
  fixedRational : ℕ → List ℕ
  /-- `E(c)`, the `ECut` argument list (`06:1856--1860`). -/
  eArgs : ℕ → List (ℕ × ℕ)
  /-- `P(c)`, the `PCut` argument list (`06:1856--1860`). -/
  pArgs : ℕ → List (ℕ × ℕ × ℕ)
  /-- `D(c)`, the `DCut` argument list (`06:1856--1860`). -/
  dArgs : ℕ → List (ℕ × ℕ)

namespace CutoffEmission

/-- The roots of `eq:R-exact`, in the frozen printed order of the union
`F(c)`, `ECut` roots, `PCut` roots, `DCut` roots
(`06-parameter-schedule.tex`, label line 1951, display lines 1944--1952). -/
noncomputable def roots (Em : CutoffEmission) (c : ℕ) : List ℕ :=
  Em.fixedRational c ++ (Em.eArgs c).map (fun p => eCut p.1 p.2) ++
    (Em.pArgs c).map (fun t => pCut t.1 t.2.1 t.2.2) ++
    (Em.dArgs c).map (fun p => dCut p.1 p.2)

/-- **`R(c) = max({2} u F(c) u {ECut(A,d)} u {PCut(A,d,e)} u {DCut(A,d)})`** --
`eq:R-exact` (`06-parameter-schedule.tex`, label line 1951, display lines
1944--1952), the "literal integer" of line 1943.

The frozen floor `{2}` is the outer `max 2`; the banked
`IterationAssembly.literalMax` supplies the rest (its own floor `1` is absorbed
by the `2`). -/
noncomputable def R (Em : CutoffEmission) (c : ℕ) : ℕ :=
  max 2 (literalMax (Em.roots c))

/-- **`n_step(c) = 2^{2^{R(c)+2}}`** -- `eq:nstep`
(`06-parameter-schedule.tex`, label line 1956, display line 1955), repeated at
`13-iteration-assembly.tex:246`.  Total in `c` by construction, which is the
frozen "total computable cutoff".

Reader counterpart: `05-iteration.tex:201--204`, "There are the total computable
successor `F(c) = 16(c+1)`, a total computable cutoff `n_step : N -> N`, and a
deterministic parameter producer with the following property." -/
noncomputable def nStep (Em : CutoffEmission) (c : ℕ) : ℕ := 2 ^ 2 ^ (Em.R c + 2)

end CutoffEmission

/-- **Aux 4 (the frozen floor of `eq:R-exact`).**  `R(c) >= 2`, from the `{2}`
inside the displayed maximum.  General. -/
theorem two_le_R (Em : CutoffEmission) (c : ℕ) : 2 ≤ Em.R c := le_max_left 2 _

/-- **Aux 5 (an emitted `PCut` argument's root is dominated by `R(c)`).**

The one property of `eq:R-exact` the successor argument uses, and the frozen
sentence `02:1378--1380`, "the absorbed `PCut(2^{d_c}C, d_c, e_c)` successor row
emitted in C6 has root at most `R(c)`".  General in the emission, the exponent
and the tuple. -/
theorem pCut_le_R {Em : CutoffEmission} {c A d e : ℕ} (h : (A, d, e) ∈ Em.pArgs c) :
    pCut A d e ≤ Em.R c := by
  refine le_trans (le_literalMax ?_) (le_max_right 2 _)
  simp only [CutoffEmission.roots, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨(A, d, e), h, rfl⟩)

/-- **Aux 6 (the literal maximum is bounded by any dominating bound).**

The dual half of the banked `IterationAssembly.le_literalMax`, needed for
monotonicity of `eq:R-exact` in the emitted lists.  General. -/
theorem literalMax_le {xs : List ℕ} {b : ℕ} (hb : 1 ≤ b) (h : ∀ x ∈ xs, x ≤ b) :
    literalMax xs ≤ b := by
  induction xs with
  | nil => simpa [literalMax] using hb
  | cons a t ih =>
    rw [literalMax_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

/-- **Aux 7 (`R(c)` and `n_step(c)` are monotone in the emitted roots).**

Adjoining rows to the emission can only raise the literal maximum, hence only
raise the cutoff, hence only **strengthen** the eligibility hypothesis
`n >= n_step(c)`.  This is what makes GAP-EXPOSED 3 harmless in direction: an
unproved `ECut`/`DCut` termination lowers `R(c)`, and a lower `R(c)` never
strengthens a conclusion.  General in both emissions and the exponent. -/
theorem R_mono {Em Em' : CutoffEmission} {c : ℕ}
    (h : ∀ x ∈ Em.roots c, x ∈ Em'.roots c) :
    Em.R c ≤ Em'.R c ∧ Em.nStep c ≤ Em'.nStep c := by
  have hR : Em.R c ≤ Em'.R c := by
    refine max_le (le_max_left 2 _) ?_
    refine literalMax_le (le_trans (by norm_num) (two_le_R Em' c)) ?_
    intro x hx
    exact le_trans (le_literalMax (h x hx)) (le_max_right 2 _)
  refine ⟨hR, ?_⟩
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) (by omega))

/-! ## Part 3: eligibility -- `13-iteration-assembly.tex:246--252` -/

/-- **Aux 8 (`n >= 2^{2^{R+2}}` forces `l(n) >= R+3`).**

`13-iteration-assembly.tex:246--252`, transcribed as printed: "If
`n >= n_step(c)`, then `n + 16 > 2^{2^{R(c)+2}}`.  Since `l(n)` is the least
integer `r >= 2` for which `n + 16 <= 2^{2^r}`, this implies `l(n) >= R(c)+3`,
and in particular `l(n) >= R(c)+2`."  The proof is the frozen minimality of
`l(n)`, through the banked `IterationAssembly.ellN_spec`.  General in the source
size and the root. -/
theorem ellN_ge_of_cutoff {n Rv : ℕ} (hn : 1 ≤ n) (h : 2 ^ 2 ^ (Rv + 2) ≤ n) :
    Rv + 3 ≤ ellN n := by
  by_contra hcon
  have hle : ellN n ≤ Rv + 2 := by omega
  obtain ⟨⟨-, hspec⟩, -, -⟩ := ellN_spec n hn
  have h1 : (2 : ℕ) ^ 2 ^ ellN n ≤ 2 ^ 2 ^ (Rv + 2) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hle)
  omega

/-- **Aux 9 (the two frozen consequences of the cutoff at an emission).**

`l(n) >= R(c)+3` and the guard `l(n) >= 4` that
`lem:shifted-pcut-absorption` demands (`06:1824`, "one has `lambda >= 4`"),
here obtained from `R(c) >= 2`.  General. -/
theorem cutoff_eligibility (Em : CutoffEmission) (c n : ℕ) (hn : 1 ≤ n)
    (h : Em.nStep c ≤ n) : Em.R c + 3 ≤ ellN n ∧ 4 ≤ ellN n := by
  have hcut : (2 : ℕ) ^ 2 ^ (Em.R c + 2) ≤ n := h
  have hell := ellN_ge_of_cutoff hn hcut
  have h2 := two_le_R Em c
  exact ⟨hell, by omega⟩

/-! ## Part 4: the root-by-root envelope realization -/

/-- **`d_c = 8(c+1)`** -- `02-mechanical-contract.tex:1379` ("Put `d_c = 8(c+1)`
and `e_c = 16(c+1)`") and `06-parameter-schedule.tex:1927`. -/
def dExp (c : ℕ) : ℕ := 8 * (c + 1)

/-- **`e_c = 16(c+1)`** -- `02-mechanical-contract.tex:1379--1380` and
`06-parameter-schedule.tex:1927`, the same integer as the successor exponent of
`eq:iteration-successor-majorant`. -/
def eExp (c : ℕ) : ℕ := 16 * (c + 1)

/-- **Aux 10 (the frozen side condition `e > d` of `eq:persistent-cutoffs`).**

`06:1796` defines `PCut(A,d,e)` "for positive integers `A, d`, and `e > d`", and
the emitted successor tuple has exactly `d_c = 8(c+1) < 16(c+1) = e_c`.  General
in the exponent. -/
theorem dExp_lt_eExp (c : ℕ) : dExp c < eExp c := by
  unfold dExp eExp; omega

/-- **The checked pre-cutoff row `u <= 2^{C_u(l(n)+2)^{d_c}}`** --
`eq:successor-pcut-normal-form` (`06-parameter-schedule.tex`, label line 1933,
display lines 1930--1934), and `02-mechanical-contract.tex:1373--1376`, "each of
these four cases is bounded by `2^{C(l(n)+2)^{8(c+1)}}` for its recorded integer
coefficient `C`". -/
def preCutoffRow (C c n : ℕ) : ℕ := 2 ^ (C * (ellN n + 2) ^ dExp c)

/-- **The absorbed coefficient `Chat_u = 2^{d_c}C_u`** --
`eq:successor-pcut-normal-form` (`06:1924--1934`): "`P(c)` contains exactly the
absorbed tuple `(Chat_u, d_c, e_c)`, `Chat_u = 2^{d_c}C_u`", with `06:1935--1938`
recording that "the registry stores the raw literal `C_u` ... and reconstructs
`Chat_u` by the displayed multiplication". -/
def absorbedCoeff (C c : ℕ) : ℕ := 2 ^ dExp c * C

/-- **The envelope realization, root by root** --
`02-mechanical-contract.tex:1373--1389`, the frozen closing paragraph of
`thm:eff-ledger`'s proof:

```
After (eq:L-ell-sandwich), each of these four cases is bounded by
2^{C(l(n)+2)^{8(c+1)}} for its recorded integer coefficient C.  Put
d_c = 8(c+1) and e_c = 16(c+1).  The absorbed PCut(2^{d_c}C, d_c, e_c)
successor row emitted in C6 has root at most R(c), while l(n) - 2 >= R(c).
Its persistence predicate at that exact index, followed by
lem:shifted-pcut-absorption, proves  C(l(n)+2)^{d_c} <= l(n)^{e_c}.
Thus every named root is at most E_{16(c+1)}(n).
```

Every link is the paper's own and is discharged here: the emitted tuple bounds
`PCut` by `R(c)` (`pCut_le_R`), the cutoff bounds `R(c)` by `l(n)-2`
(`cutoff_eligibility`), persistence transports the predicate to that exact index
(`pCutPred_persist`), and the banked `PilotPCut.pCut_shifted_certificate` --
which **is** `lem:shifted-pcut-absorption` -- closes the absorption.  Nothing is
assumed beyond the checked pre-cutoff row and the emission.

General in the emission, the recorded coefficient, the exponent, the source size
and the root value.

Reader counterpart: none; `05-iteration.tex:247--248` states this sentence
inside `\begin{proof}` and is proof prose. -/
theorem successorRootBound (Em : CutoffEmission) (C c n u : ℕ) (hn : 1 ≤ n)
    (habs : (absorbedCoeff C c, dExp c, eExp c) ∈ Em.pArgs c)
    (hcut : Em.nStep c ≤ n) (hrow : u ≤ preCutoffRow C c n) :
    u ≤ envE (eExp c) n := by
  obtain ⟨hell, hell4⟩ := cutoff_eligibility Em c n hn hcut
  have hspec : PCutPred (absorbedCoeff C c) (dExp c) (eExp c)
      (pCut (absorbedCoeff C c) (dExp c) (eExp c)) :=
    pCut_spec _ _ _ (dExp_lt_eExp c)
  have hroot : pCut (absorbedCoeff C c) (dExp c) (eExp c) ≤ Em.R c := pCut_le_R habs
  have hle : pCut (absorbedCoeff C c) (dExp c) (eExp c) ≤ ellN n - 2 := by omega
  have hpers : PCutPred (absorbedCoeff C c) (dExp c) (eExp c) (ellN n - 2) :=
    pCutPred_persist (le_of_lt (dExp_lt_eExp c)) hspec hle
  have hcomm : absorbedCoeff C c = C * 2 ^ dExp c := Nat.mul_comm _ _
  rw [hcomm] at hpers
  have habsorb : C * (ellN n + 2) ^ dExp c ≤ ellN n ^ eExp c :=
    pCut_shifted_certificate hell4 hpers
  calc u ≤ preCutoffRow C c n := hrow
    _ = 2 ^ (C * (ellN n + 2) ^ dExp c) := rfl
    _ ≤ 2 ^ ellN n ^ eExp c := Nat.pow_le_pow_right (by norm_num) habsorb
    _ = envE (eExp c) n := rfl

/-! ## Part 5: the structural majorant, substituted -/

/-- **Aux 11 (`eq:structural-majorants` becomes the checked pre-cutoff row).**

The frozen substitution of `06:1846--1852`: "the normalization program
substitutes `l(n)-2 <= L <= (l(n)+2)^{c+1}` into
`eq:structural-majorants`--`eq:four-tail-errors`".  Applying the **upper** half
to `W(L) = 2^{C_size L^8}` (the banked `SizePropagation.structuralW`,
`eq:structural-majorants` line 1694) gives exactly
`2^{C_size(l(n)+2)^{8(c+1)}}`, which is `02:1374`'s row: the degree-eight
exponent of line 1694 and the degree `c+1` of the sandwich multiply to `d_c`.

General in the recorded coefficient, in `L`, in the exponent and in the source
size. -/
theorem structuralW_le_preCutoffRow (Csize L c n : ℕ)
    (hL : L ≤ (ellN n + 2) ^ (c + 1)) :
    structuralW Csize L ≤ preCutoffRow Csize c n := by
  have h8 : L ^ 8 ≤ (ellN n + 2) ^ dExp c := by
    calc L ^ 8 ≤ ((ellN n + 2) ^ (c + 1)) ^ 8 := Nat.pow_le_pow_left hL 8
      _ = (ellN n + 2) ^ ((c + 1) * 8) := by rw [← pow_mul]
      _ = (ellN n + 2) ^ dExp c := by unfold dExp; congr 1; ring
  simp only [structuralW, preCutoffRow]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h8)

/-- **Aux 16 (the structural row is never an empty premise).**

`hstruct` -- the first row of `eq:structural-majorants` at a record's majorised
list -- is the one hypothesis this module adds beyond the emission and the
cutoff, and under LANE-GATE 3 it must be exhibited satisfiable rather than
merely assumed.  It is: at any `L >= 1` (and `L = clog_2(A_pre) >= 4` always, by
`four_le_normalizedL`), every finite list of quantities is under `W(L)` at some
recorded coefficient, because `W` is exponential in that coefficient.  Hence no
hypothesis bundle below is vacuous through this premise, and in particular no
`False` derives from combining it with the two-sided width bound, whose lower
half `Q_i >= 47104000 b_i q_i` is an arbitrary finite number.

The coefficient exhibited here is a **consistency-probe** value claiming no
legality: the paper's own recorded coefficient is the banked producer
`SizePropagation.csizeLiteral` read off the registry's coefficient table
(`eq:Csize-literal-producer`), not this maximum.  General in the list and in
`L >= 1`. -/
theorem structuralRow_satisfiable (xs : List ℕ) {L : ℕ} (hL : 1 ≤ L) :
    ∀ x ∈ xs, x ≤ structuralW (literalMax xs) L := by
  intro x hx
  have h1 : x ≤ literalMax xs := le_literalMax hx
  have h2 : literalMax xs ≤ 2 ^ literalMax xs := Nat.le_of_lt Nat.lt_two_pow_self
  have h3 : (1 : ℕ) ≤ L ^ 8 := Nat.one_le_pow _ _ (by omega)
  have h4 : literalMax xs ≤ literalMax xs * L ^ 8 :=
    Nat.le_mul_of_pos_right _ (by omega)
  have h5 : (2 : ℕ) ^ literalMax xs ≤ 2 ^ (literalMax xs * L ^ 8) :=
    Nat.pow_le_pow_right (by norm_num) h4
  simp only [structuralW]
  omega

/-- **`L = clog_2(A_pre)`** -- `06-parameter-schedule.tex:1867--1869`: "Since
`A_pre >= 16` and `L = clog_2(A_pre)`, we have `L >= 4`".

`A_pre` is the banked `ParameterSchedule.Apre`, the frozen
`max{16, b_out, B_pub, z_R, clog_2(|E|+2)}` of `eq:s-choice` (`06:109--121`),
consumed by pin.  This is a DEFINED quantity and is reified, never assigned. -/
def normalizedL (bout Bpub zR clE : ℕ) : ℕ :=
  Nat.clog 2 (ParameterSchedule.Apre bout Bpub zR clE)

/-- **Aux 12 (`L >= 4`, derived).**  `06:1868--1869`, "we have `L >= 4`", from
the banked `ParameterSchedule.sixteen_le_Apre` through the frozen minimality
eliminator `ParameterSchedule.lt_clog_of_pow_lt` (`06:75--76`).  General in the
four public inputs. -/
theorem four_le_normalizedL (bout Bpub zR clE : ℕ) :
    4 ≤ normalizedL bout Bpub zR clE := by
  have h16 := ParameterSchedule.sixteen_le_Apre bout Bpub zR clE
  have h : (2 : ℕ) ^ 3 < ParameterSchedule.Apre bout Bpub zR clE := by
    have : (2 : ℕ) ^ 3 = 8 := by norm_num
    omega
  have := ParameterSchedule.lt_clog_of_pow_lt (b := 2) (by norm_num) h
  unfold normalizedL
  omega

/-- **The upper half of `eq:L-ell-sandwich`, derived from the incoming
envelope** -- `eq:L-ell-sandwich` (`06-parameter-schedule.tex`, label line 1849,
display line 1848) with its own justification at lines 1851--1853: "The lower
bound follows from the normalised source size, and the upper bound from the
incoming `E_c(n)` bounds and sparsity of the source graph."

That is exactly what is proved here.  Each of the five branches of `A_pre`
(`eq:s-choice`, `06:111--115`) is at most `E_c(n) = 2^{l(n)^c}`: the constant
`16`, the three public quantities `b_out`, `B_pub`, `z_R` carried by the
incoming state's envelope, and `clog_2(|E|+2)`, which is the sparsity input.
Hence `L = clog_2(A_pre) <= l(n)^c <= (l(n)+2)^{c+1}`.

The **lower** half `l(n)-2 <= L` is not claimed: it comes from the normalised
source size, which is not in scope here, and no declaration below uses it.

General in the four public inputs, the exponent and the source size. -/
theorem lSandwich_upper (bout Bpub zR clE c n : ℕ) (h16 : 16 ≤ envE c n)
    (hbout : bout ≤ envE c n) (hBpub : Bpub ≤ envE c n) (hzR : zR ≤ envE c n)
    (hclE : clE ≤ envE c n) :
    normalizedL bout Bpub zR clE ≤ (ellN n + 2) ^ (c + 1) := by
  have hApre : ParameterSchedule.Apre bout Bpub zR clE ≤ 2 ^ ellN n ^ c := by
    simp only [ParameterSchedule.Apre]
    exact max_le (max_le (max_le (max_le h16 hbout) hBpub) hzR) hclE
  have hclog : normalizedL bout Bpub zR clE ≤ ellN n ^ c :=
    Nat.clog_le_of_le_pow hApre
  refine le_trans hclog ?_
  calc ellN n ^ c ≤ (ellN n + 2) ^ c := Nat.pow_le_pow_left (by omega) c
    _ ≤ (ellN n + 2) ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)

/-- **Aux 13 (the envelope clears the frozen `16` branch at every scheduled
exponent).**

`eq:s-choice`'s first branch is the literal `16`; the scheduled exponents are
the banked `IterationAssembly.cexp`, whose floor is `c_j >= 3`
(`13:259--262`, banked `cexp_ge_three_and_lt`).  Since `l(n) >= 2` (banked
`SizePropagation.two_le_ellN`), `E_c(n) = 2^{l(n)^c} >= 2^8 >= 16`.  General in
the exponent above the frozen floor and in the source size. -/
theorem sixteen_le_envE {c : ℕ} (n : ℕ) (hc : 3 ≤ c) : 16 ≤ envE c n := by
  have hell : 2 ≤ ellN n := two_le_ellN n
  have h1 : (2 : ℕ) ^ 3 ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc
  have h2 : (2 : ℕ) ^ c ≤ ellN n ^ c := Nat.pow_le_pow_left hell c
  have h3 : (8 : ℕ) ≤ ellN n ^ c := by
    have : (2 : ℕ) ^ 3 = 8 := by norm_num
    omega
  have h4 : (2 : ℕ) ^ 4 ≤ 2 ^ ellN n ^ c :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : (2 : ℕ) ^ 4 = 16 := by norm_num
  change 16 ≤ 2 ^ ellN n ^ c
  omega

/-! ## Part 6: the two `PARAM-001` hypotheses, built -/

/-- **The second-pass traversal bound, realized.**

`13-iteration-assembly.tex:300--308` -- "The second-pass traversal then bounds
every newly constructed auxiliary width other than the numerical source width,
both new logarithmic side lengths, the inverse tolerances and robustness depths,
and the updated public budgets by `E_{16(c_r+1)}(n)`" -- delivered from the
paper's own chain rather than assumed.

The one input beyond the emission and the cutoff is `hstruct`, the first row of
`eq:structural-majorants` (`06:1691--1702`) at the record's majorised list.  That
row is the output of the two-pass coefficient traversal of `06:1660--1706`,
which is not formalized, so it is a named hypothesis at its own anchor
(GAP-EXPOSED 2) -- **not** the successor bound itself, which is what this theorem
proves.

General in the emission, the recorded coefficient, `L`, the exponent, the source
size and the output record. -/
theorem traversalRealization (Em : CutoffEmission) (Csize L c n : ℕ)
    (O : SuccessorOutputs) (hn : 1 ≤ n)
    (habs : (absorbedCoeff Csize c, dExp c, eExp c) ∈ Em.pArgs c)
    (hL : L ≤ (ellN n + 2) ^ (c + 1))
    (hstruct : ∀ x ∈ O.majorised, x ≤ structuralW Csize L)
    (hcut : Em.nStep c ≤ n) :
    ∀ x ∈ O.majorised, x ≤ envE (eExp c) n := fun x hx =>
  successorRootBound Em Csize c n x hn habs hcut
    (le_trans (hstruct x hx) (structuralW_le_preCutoffRow Csize L c n hL))

/-- **The source-width logarithmic row, realized.**

`13-iteration-assembly.tex:312--313`, "its logarithm remains in the displayed
majorant", corroborated by `06-parameter-schedule.tex:2073--2075`.  The frozen
sentence that puts `log_2 q_2` inside the structural row rather than outside it
is `06:1703--1704`: "Here `q_2` itself is not called an auxiliary scale: only
`log_2 q_2` appears among the new logarithmic side lengths."  So the same
`eq:structural-majorants` row applies to the *logarithm* of the numerical source
width, and the same realization closes it.

General in every argument. -/
theorem srcWidthLogRealization (Em : CutoffEmission) (Csize L c n : ℕ)
    (O : SuccessorOutputs) (hn : 1 ≤ n)
    (habs : (absorbedCoeff Csize c, dExp c, eExp c) ∈ Em.pArgs c)
    (hL : L ≤ (ellN n + 2) ^ (c + 1))
    (hstructSrc : Nat.clog 2 O.srcWidth ≤ structuralW Csize L)
    (hcut : Em.nStep c ≤ n) :
    Nat.clog 2 O.srcWidth ≤ envE (eExp c) n :=
  successorRootBound Em Csize c n _ hn habs hcut
    (le_trans hstructSrc (structuralW_le_preCutoffRow Csize L c n hL))

/-- **The `htraversal` inhabitant, in the banked binder shape.**

This is the term `SuccessorMajorant` could not supply (its GAP-EXPOSED 7): a
proof of

```
n_step(c_r) <= n  ->  S under E_{c_r}(n)  ->
    every majorised quantity <= E_{16(c_r+1)}(n)
```

built from the paper's own chain.  **Both** antecedents are used, neither is
decoration: the first is the eligibility the absorption needs, and the second is
what bounds the four public branches of `A_pre`, hence `L`, hence the frozen
sandwich -- so the incoming envelope really does drive the outgoing one, exactly
as `13:296--308` reads.

`hboutS`, `hBpubS`, `hzRS` say that the three public inputs of `eq:s-choice`
are quantities of the incoming state (its side lengths, budgets and depth), and
`hclE` is the sparsity input `clog_2(|E|+2)`, which is not a state slot and
carries its own frozen bound.

General in every argument. -/
theorem htraversal_of_state (Em : CutoffEmission) (Csize bout Bpub zR clE c n : ℕ)
    (S : LevelState) (O : SuccessorOutputs) (hn : 1 ≤ n) (hc : 3 ≤ c)
    (habs : (absorbedCoeff Csize c, dExp c, eExp c) ∈ Em.pArgs c)
    (hboutS : bout ∈ S.quantities) (hBpubS : Bpub ∈ S.quantities)
    (hzRS : zR ∈ S.quantities) (hclE : clE ≤ envE c n)
    (hstruct : ∀ x ∈ O.majorised,
      x ≤ structuralW Csize (normalizedL bout Bpub zR clE)) :
    Em.nStep c ≤ n → S.UnderEnvelope c n →
      ∀ x ∈ O.majorised, x ≤ envE (16 * (c + 1)) n := by
  intro hcut hstate
  have hL := lSandwich_upper bout Bpub zR clE c n (sixteen_le_envE n hc)
    (hstate _ hboutS) (hstate _ hBpubS) (hstate _ hzRS) hclE
  exact traversalRealization Em Csize _ c n O hn habs hL hstruct hcut

/-- **The `hsrclog` inhabitant, in the banked binder shape.**

The companion of `htraversal_of_state` for the second `PARAM-001` hypothesis of
`SuccessorMajorant.successorMajorant` and `.sourceWidthSeparate`, at the same
anchors (`13:312--313`, `06:1703--1704`, `06:2073--2075`).

General in every argument. -/
theorem hsrclog_of_state (Em : CutoffEmission) (Csize bout Bpub zR clE c n : ℕ)
    (S : LevelState) (O : SuccessorOutputs) (hn : 1 ≤ n) (hc : 3 ≤ c)
    (habs : (absorbedCoeff Csize c, dExp c, eExp c) ∈ Em.pArgs c)
    (hboutS : bout ∈ S.quantities) (hBpubS : Bpub ∈ S.quantities)
    (hzRS : zR ∈ S.quantities) (hclE : clE ≤ envE c n)
    (hstructSrc : Nat.clog 2 O.srcWidth
      ≤ structuralW Csize (normalizedL bout Bpub zR clE)) :
    Em.nStep c ≤ n → S.UnderEnvelope c n →
      Nat.clog 2 O.srcWidth ≤ envE (16 * (c + 1)) n := by
  intro hcut hstate
  have hL := lSandwich_upper bout Bpub zR clE c n (sixteen_le_envE n hc)
    (hstate _ hboutS) (hstate _ hBpubS) (hstate _ hzRS) hclE
  exact srcWidthLogRealization Em Csize _ c n O hn habs hL hstructSrc hcut

/-! ## Part 7: the six pending `SuccessorMajorant` deliverables, wired

Each banked theorem is consumed **by pin** -- its statement is not restated and
its proof is not re-derived -- and re-delivered with the `PARAM-001` hypotheses
discharged by Part 6. -/

/-- **`eq:iteration-successor-majorant`, unconditionally on the traversal.**

`SuccessorMajorant.successorMajorant` with both of its `PARAM-001` hypotheses
built.  All four frozen conclusions survive: the eligibility of `13:297--298`,
the exponent identity of line 308, the majorant of lines 303--307, and the
source-width logarithmic row of line 313.

General in every argument. -/
theorem successorMajorant_realized (Em : CutoffEmission)
    (Csize bout Bpub zR clE n r : ℕ) (S : LevelState) (O : SuccessorOutputs)
    (hn : 1 ≤ n) (hstate : S.UnderEnvelope (cexp r) n)
    (hnval : nval Em.nStep (r + 1) ≤ n)
    (habs : (absorbedCoeff Csize (cexp r), dExp (cexp r), eExp (cexp r))
      ∈ Em.pArgs (cexp r))
    (hboutS : bout ∈ S.quantities) (hBpubS : Bpub ∈ S.quantities)
    (hzRS : zR ∈ S.quantities) (hclE : clE ≤ envE (cexp r) n)
    (hstruct : ∀ x ∈ O.majorised,
      x ≤ structuralW Csize (normalizedL bout Bpub zR clE))
    (hstructSrc : Nat.clog 2 O.srcWidth
      ≤ structuralW Csize (normalizedL bout Bpub zR clE)) :
    Em.nStep (cexp r) ≤ n ∧
      envE (16 * (cexp r + 1)) n = envE (cexp (r + 1)) n ∧
      O.UnderEnvelope (cexp (r + 1)) n ∧
      Nat.clog 2 O.srcWidth ≤ envE (cexp (r + 1)) n :=
  successorMajorant Em.nStep n r S O hstate hnval
    (htraversal_of_state Em Csize bout Bpub zR clE (cexp r) n S O hn
      (cexp_ge_three_and_lt r).1 habs hboutS hBpubS hzRS hclE hstruct)
    (hsrclog_of_state Em Csize bout Bpub zR clE (cexp r) n S O hn
      (cexp_ge_three_and_lt r).1 habs hboutS hBpubS hzRS hclE hstructSrc)

/-- **The successor state re-enters the envelope, unconditionally on the
traversal.**

`SuccessorMajorant.successorMajorant_chains` with its `PARAM-001` hypothesis
built.  `hsrclog` is deliberately absent there and stays absent here.

General in every argument. -/
theorem successorMajorant_chains_realized (Em : CutoffEmission)
    (Csize bout Bpub zR clE n r : ℕ) (S : LevelState) (O : SuccessorOutputs)
    (hn : 1 ≤ n) (hstate : S.UnderEnvelope (cexp r) n)
    (hnval : nval Em.nStep (r + 1) ≤ n)
    (habs : (absorbedCoeff Csize (cexp r), dExp (cexp r), eExp (cexp r))
      ∈ Em.pArgs (cexp r))
    (hboutS : bout ∈ S.quantities) (hBpubS : Bpub ∈ S.quantities)
    (hzRS : zR ∈ S.quantities) (hclE : clE ≤ envE (cexp r) n)
    (hstruct : ∀ x ∈ O.majorised,
      x ≤ structuralW Csize (normalizedL bout Bpub zR clE)) :
    (O.nextState S).UnderEnvelope (cexp (r + 1)) n :=
  successorMajorant_chains Em.nStep n r S O hstate hnval
    (htraversal_of_state Em Csize bout Bpub zR clE (cexp r) n S O hn
      (cexp_ge_three_and_lt r).1 habs hboutS hBpubS hzRS hclE hstruct)

/-- **The state induction of the reading warning, unconditionally on the
traversal.**

`SuccessorMajorant.iteratedStateMajorant` with its per-arrow `PARAM-001`
hypothesis built at every arrow.  The recorded coefficient, the three public
`A_pre` inputs and the sparsity input are per-arrow functions, because
`eq:s-choice` is evaluated at each level's own public data; the emission is a
single object, because `thm:eff-ledger`(b) fixes `Cert` before the recursion.

General in every argument. -/
theorem iteratedStateMajorant_realized (Em : CutoffEmission) (n k : ℕ)
    (Cs bo Bp zr cle : ℕ → ℕ) (St : ℕ → LevelState) (Out : ℕ → SuccessorOutputs)
    (hn : 1 ≤ n) (hseed : (St 0).UnderEnvelope (cexp 0) n)
    (hnval : nval Em.nStep k ≤ n)
    (hchain : ∀ i, i < k → St (i + 1) = (Out i).nextState (St i))
    (habs : ∀ i, i < k →
      (absorbedCoeff (Cs i) (cexp i), dExp (cexp i), eExp (cexp i))
        ∈ Em.pArgs (cexp i))
    (hboutS : ∀ i, i < k → bo i ∈ (St i).quantities)
    (hBpubS : ∀ i, i < k → Bp i ∈ (St i).quantities)
    (hzRS : ∀ i, i < k → zr i ∈ (St i).quantities)
    (hclE : ∀ i, i < k → cle i ≤ envE (cexp i) n)
    (hstruct : ∀ i, i < k → ∀ x ∈ (Out i).majorised,
      x ≤ structuralW (Cs i) (normalizedL (bo i) (Bp i) (zr i) (cle i))) :
    (∀ i, i ≤ k → (St i).UnderEnvelope (cexp i) n) ∧
      ∀ i, i ≤ k → (St i).UnderEnvelope (cexp k) n :=
  iteratedStateMajorant Em.nStep n k St Out hseed hnval hchain
    (fun i hi => htraversal_of_state Em (Cs i) (bo i) (Bp i) (zr i) (cle i)
      (cexp i) n (St i) (Out i) hn (cexp_ge_three_and_lt i).1 (habs i hi)
      (hboutS i hi) (hBpubS i hi) (hzRS i hi) (hclE i hi) (hstruct i hi))

/-- **The separate numerical source width, unconditionally on the traversal.**

`SuccessorMajorant.sourceWidthSeparate` with both `PARAM-001` hypotheses built.
All four frozen conclusions survive, including the **strict** graph row
`q_{2,r+1} < 24 s_{r+1} |E(G)|` of `13:312`, which stays an explicit hypothesis
because line 311 leaves the numerical width to the source graph.

General in every argument. -/
theorem sourceWidthSeparate_realized (Em : CutoffEmission)
    (Csize bout Bpub zR clE n r : ℕ) (S : LevelState) (O : SuccessorOutputs)
    (s edges : ℕ) (hn : 1 ≤ n) (hgraph : O.srcWidth < 24 * s * edges)
    (hstate : S.UnderEnvelope (cexp r) n) (hnval : nval Em.nStep (r + 1) ≤ n)
    (habs : (absorbedCoeff Csize (cexp r), dExp (cexp r), eExp (cexp r))
      ∈ Em.pArgs (cexp r))
    (hboutS : bout ∈ S.quantities) (hBpubS : Bpub ∈ S.quantities)
    (hzRS : zR ∈ S.quantities) (hclE : clE ≤ envE (cexp r) n)
    (hstruct : ∀ x ∈ O.majorised,
      x ≤ structuralW Csize (normalizedL bout Bpub zR clE))
    (hstructSrc : Nat.clog 2 O.srcWidth
      ≤ structuralW Csize (normalizedL bout Bpub zR clE)) :
    O.UnderEnvelope (cexp (r + 1)) n ∧
      O.srcWidth < 24 * s * edges ∧
      Nat.clog 2 O.srcWidth ≤ envE (cexp (r + 1)) n ∧
      O.srcWidth ≤ 2 ^ envE (cexp (r + 1)) n :=
  sourceWidthSeparate Em.nStep n r S O s edges hgraph hstate hnval
    (htraversal_of_state Em Csize bout Bpub zR clE (cexp r) n S O hn
      (cexp_ge_three_and_lt r).1 habs hboutS hBpubS hzRS hclE hstruct)
    (hsrclog_of_state Em Csize bout Bpub zR clE (cexp r) n S O hn
      (cexp_ge_three_and_lt r).1 habs hboutS hBpubS hzRS hclE hstructSrc)

/-- **The dominant-branch width bound, enveloped -- unconditionally.**

`SuccessorMajorant.dominantWidth_enveloped` with its `PARAM-001` hypothesis
built.  The composed two-sided bound

```
47104000 b_i q_i  <=  Q_i  <=  E_{c_{r+1}}(n)
```

therefore now holds outright at every point where the emission, the incoming
state and the structural row are supplied -- which is the half of tranche 62's
GAP-EXPOSED 7 that concerns the width.

General in every argument. -/
theorem dominantWidth_enveloped_realized
    (Sp : FixedLevelCarriers.LevelCarrierSpec) {s : ℕ} {dv zeta : ℝ}
    (hsched : ScheduleTolerance Sp s dv zeta) (hs : 3 < s) (hdv : 0 < dv)
    (hz : 0 < zeta) (i : ℕ) (hb : 1 ≤ Sp.bout i) (Em : CutoffEmission)
    (Csize bout Bpub zR clE n r : ℕ) (S : LevelState) (O : SuccessorOutputs)
    (hn : 1 ≤ n) (hmem : Sp.Q i ∈ O.auxWidths)
    (hstate : S.UnderEnvelope (cexp r) n) (hnval : nval Em.nStep (r + 1) ≤ n)
    (habs : (absorbedCoeff Csize (cexp r), dExp (cexp r), eExp (cexp r))
      ∈ Em.pArgs (cexp r))
    (hboutS : bout ∈ S.quantities) (hBpubS : Bpub ∈ S.quantities)
    (hzRS : zR ∈ S.quantities) (hclE : clE ≤ envE (cexp r) n)
    (hstruct : ∀ x ∈ O.majorised,
      x ≤ structuralW Csize (normalizedL bout Bpub zR clE)) :
    47104000 * Sp.bout i * Sp.q i ≤ Sp.Q i ∧
      Sp.Q i ≤ envE (cexp (r + 1)) n ∧
      47104000 * Sp.bout i * Sp.q i ≤ envE (cexp (r + 1)) n :=
  dominantWidth_enveloped Sp hsched hs hdv hz i hb Em.nStep n r S O hmem hstate
    hnval
    (htraversal_of_state Em Csize bout Bpub zR clE (cexp r) n S O hn
      (cexp_ge_three_and_lt r).1 habs hboutS hBpubS hzRS hclE hstruct)

/-- **The carrier half of the same envelope -- unconditionally.**

`SuccessorMajorant.dominantRowSide_enveloped` with its `PARAM-001` hypothesis
built, closing the other half of tranche 62's GAP-EXPOSED 7:

```
q_i  <=  ceil(log_2 m_{i+1})  <=  O.logRow  <=  E_{c_{r+1}}(n).
```

General in every argument. -/
theorem dominantRowSide_enveloped_realized
    (Sp : FixedLevelCarriers.LevelCarrierSpec) {s : ℕ} {dv zeta : ℝ}
    (hsched : ScheduleTolerance Sp s dv zeta) (hs : 3 < s) (hdv : 0 < dv)
    (hz : 0 < zeta) (i : ℕ) (hb : 1 ≤ Sp.bout i) (Em : CutoffEmission)
    (Csize bout Bpub zR clE n r : ℕ) (S : LevelState) (O : SuccessorOutputs)
    (hn : 1 ≤ n) (hside : Nat.clog 2 (Sp.rowCarrier (i + 1)) ≤ O.logRow)
    (hstate : S.UnderEnvelope (cexp r) n) (hnval : nval Em.nStep (r + 1) ≤ n)
    (habs : (absorbedCoeff Csize (cexp r), dExp (cexp r), eExp (cexp r))
      ∈ Em.pArgs (cexp r))
    (hboutS : bout ∈ S.quantities) (hBpubS : Bpub ∈ S.quantities)
    (hzRS : zR ∈ S.quantities) (hclE : clE ≤ envE (cexp r) n)
    (hstruct : ∀ x ∈ O.majorised,
      x ≤ structuralW Csize (normalizedL bout Bpub zR clE)) :
    Sp.q i ≤ Nat.clog 2 (Sp.rowCarrier (i + 1)) ∧
      Sp.q i ≤ O.logRow ∧ O.logRow ≤ envE (cexp (r + 1)) n :=
  dominantRowSide_enveloped Sp hsched hs hdv hz i hb Em.nStep n r S O hside
    hstate hnval
    (htraversal_of_state Em Csize bout Bpub zR clE (cexp r) n S O hn
      (cexp_ge_three_and_lt r).1 habs hboutS hBpubS hzRS hclE hstruct)

/-! ## Part 8: GAP-EXPOSED 7 closed at the paper's own carrier specification -/

/-- **Both halves of the composed bound, at one record, unconditionally.**

Tranche 62 recorded (GAP-EXPOSED 7) that its two enveloping theorems were
delivered *conditionally* and that "no instance in this tranche inhabits
`htraversal` at such a record".  Here both are delivered at one and the same
output record, with `htraversal` built by Part 6 -- so the meeting of the two
directions has an in-tranche witness for the first time.

The record is pinned by the same two equations
`enveloping_premises_inhabited` uses, so it is the same point: `auxWidths` is the
singleton `[Q_i]` and `logRow` is the **evaluated** `ceil(log_2 m_{i+1})`.

General in the specification, the level, the emission, the recorded coefficient,
the public inputs, the state, the source size and the arrow. -/
theorem envelopeRealization_closes_the_two_sided_bound
    (Sp : FixedLevelCarriers.LevelCarrierSpec) {s : ℕ} {dv zeta : ℝ}
    (hsched : ScheduleTolerance Sp s dv zeta) (hs : 3 < s) (hdv : 0 < dv)
    (hz : 0 < zeta) (i : ℕ) (hb : 1 ≤ Sp.bout i) (Em : CutoffEmission)
    (Csize bout Bpub zR clE n r : ℕ) (S : LevelState) (O : SuccessorOutputs)
    (hn : 1 ≤ n) (hQ : O.auxWidths = [Sp.Q i])
    (hrow : O.logRow = Nat.clog 2 (Sp.rowCarrier (i + 1)))
    (hstate : S.UnderEnvelope (cexp r) n) (hnval : nval Em.nStep (r + 1) ≤ n)
    (habs : (absorbedCoeff Csize (cexp r), dExp (cexp r), eExp (cexp r))
      ∈ Em.pArgs (cexp r))
    (hboutS : bout ∈ S.quantities) (hBpubS : Bpub ∈ S.quantities)
    (hzRS : zR ∈ S.quantities) (hclE : clE ≤ envE (cexp r) n)
    (hstruct : ∀ x ∈ O.majorised,
      x ≤ structuralW Csize (normalizedL bout Bpub zR clE)) :
    (47104000 * Sp.bout i * Sp.q i ≤ Sp.Q i ∧
        Sp.Q i ≤ envE (cexp (r + 1)) n ∧
        47104000 * Sp.bout i * Sp.q i ≤ envE (cexp (r + 1)) n) ∧
      Sp.q i ≤ Nat.clog 2 (Sp.rowCarrier (i + 1)) ∧
        Sp.q i ≤ O.logRow ∧ O.logRow ≤ envE (cexp (r + 1)) n := by
  have hmem : Sp.Q i ∈ O.auxWidths := by rw [hQ]; simp
  have hside : Nat.clog 2 (Sp.rowCarrier (i + 1)) ≤ O.logRow := by rw [hrow]
  exact ⟨dominantWidth_enveloped_realized Sp hsched hs hdv hz i hb Em Csize bout
      Bpub zR clE n r S O hn hmem hstate hnval habs hboutS hBpubS hzRS hclE
      hstruct,
    dominantRowSide_enveloped_realized Sp hsched hs hdv hz i hb Em Csize bout
      Bpub zR clE n r S O hn hside hstate hnval habs hboutS hBpubS hzRS hclE
      hstruct⟩

/-- **GAP-EXPOSED 7, closed at the paper's own carrier specification.**

The canonical-inhabitation test: the record `enveloping_premises_inhabited`
exhibits at `FixedLevelCarriers.paperSeedSpec` -- the paper's own instance,
whose every field is the frozen value evaluated through its own defining chain
-- now carries **both** two-sided conclusions outright.  The existential witness
is pinned by the same two equations, so the empty record fails on the very first
conjunct and no convenient completion can be substituted; the six remaining
slots stay universally quantified.

`ScheduleTolerance` at that instance is the banked
`DominantWidthBound.paperSeedSpec_scheduleTolerance`, and the depth guard
`1 <= b_i` is the frozen `B(n) >= 512` of `13:415`, taken from the banked
`IterationAssembly.depthB_ge` at the instance's own level-zero depth.

What is **not** claimed: the record is still a *candidate* tuple in the sense of
`13:313--315`, and `SuccessorMajorant`'s GAP-EXPOSED 3 (canonical inhabitation of
`SuccessorOutputs` by the paper's realized outputs) stays registered as deferred
under `MATERIALIZE-001`.

General in every free input of `paperSeedSpec`, in the level, in the emission,
in the recorded coefficient, in the public inputs, in the state and in the six
unconstrained output slots. -/
theorem dominantWidth_two_sided_at_paperSpec (nv C0 B0 Ccert : ℕ) {s : ℕ}
    (lq2 clU0 zRspec : ℕ) {dv zeta : ℝ} (hnv : 1 ≤ nv) (hs : 3 < s)
    (hdv : 0 < dv) (hz : 0 < zeta) (mN nN : ℕ → ℕ) (hmN : ∀ i, 1 ≤ mN i)
    (hnN : ∀ i, 1 ≤ nN i) (i : ℕ) (Em : CutoffEmission)
    (Csize bout Bpub zR clE n r : ℕ) (S : LevelState)
    (logCol D Y q2 : ℕ) (invTol robDepths : List ℕ) (hn : 1 ≤ n)
    (hstate : S.UnderEnvelope (cexp r) n) (hnval : nval Em.nStep (r + 1) ≤ n)
    (habs : (absorbedCoeff Csize (cexp r), dExp (cexp r), eExp (cexp r))
      ∈ Em.pArgs (cexp r))
    (hboutS : bout ∈ S.quantities) (hBpubS : Bpub ∈ S.quantities)
    (hzRS : zR ∈ S.quantities) (hclE : clE ≤ envE (cexp r) n)
    (hQrow : (FixedLevelCarriers.paperSeedSpec nv C0 B0 Ccert s lq2 clU0 zRspec
        dv zeta mN nN hmN hnN).Q i
      ≤ structuralW Csize (normalizedL bout Bpub zR clE))
    (hRowrow : Nat.clog 2
        ((FixedLevelCarriers.paperSeedSpec nv C0 B0 Ccert s lq2 clU0 zRspec dv
          zeta mN nN hmN hnN).rowCarrier (i + 1))
      ≤ structuralW Csize (normalizedL bout Bpub zR clE))
    (hColrow : logCol ≤ structuralW Csize (normalizedL bout Bpub zR clE))
    (hInvTol : ∀ x ∈ invTol,
      x ≤ structuralW Csize (normalizedL bout Bpub zR clE))
    (hRob : ∀ x ∈ robDepths,
      x ≤ structuralW Csize (normalizedL bout Bpub zR clE))
    (hDrow : D ≤ structuralW Csize (normalizedL bout Bpub zR clE))
    (hYrow : Y ≤ structuralW Csize (normalizedL bout Bpub zR clE)) :
    ∃ O : SuccessorOutputs,
      O.auxWidths =
          [(FixedLevelCarriers.paperSeedSpec nv C0 B0 Ccert s lq2 clU0 zRspec dv
            zeta mN nN hmN hnN).Q i] ∧
        O.logRow = Nat.clog 2
            ((FixedLevelCarriers.paperSeedSpec nv C0 B0 Ccert s lq2 clU0 zRspec
              dv zeta mN nN hmN hnN).rowCarrier (i + 1)) ∧
        O.logCol = logCol ∧ O.invTolerances = invTol ∧
        O.robustDepths = robDepths ∧ O.budgetD = D ∧ O.budgetY = Y ∧
        O.srcWidth = q2 ∧
        (47104000
              * (FixedLevelCarriers.paperSeedSpec nv C0 B0 Ccert s lq2 clU0
                  zRspec dv zeta mN nN hmN hnN).bout i
              * (FixedLevelCarriers.paperSeedSpec nv C0 B0 Ccert s lq2 clU0
                  zRspec dv zeta mN nN hmN hnN).q i
            ≤ (FixedLevelCarriers.paperSeedSpec nv C0 B0 Ccert s lq2 clU0 zRspec
                dv zeta mN nN hmN hnN).Q i ∧
          (FixedLevelCarriers.paperSeedSpec nv C0 B0 Ccert s lq2 clU0 zRspec dv
              zeta mN nN hmN hnN).Q i ≤ envE (cexp (r + 1)) n) ∧
        (FixedLevelCarriers.paperSeedSpec nv C0 B0 Ccert s lq2 clU0 zRspec dv
              zeta mN nN hmN hnN).q i
            ≤ O.logRow ∧
          O.logRow ≤ envE (cexp (r + 1)) n := by
  set Sp := FixedLevelCarriers.paperSeedSpec nv C0 B0 Ccert s lq2 clU0 zRspec dv
    zeta mN nN hmN hnN with hSp
  have hsched : ScheduleTolerance Sp s dv zeta :=
    paperSeedSpec_scheduleTolerance nv C0 B0 Ccert s lq2 clU0 zRspec dv zeta mN
      nN hmN hnN
  have hdepth : Sp.bout i = depthB nv := rfl
  have hb : 1 ≤ Sp.bout i := by
    rw [hdepth]; exact (depthB_ge nv hnv).2
  refine ⟨⟨[Sp.Q i], Nat.clog 2 (Sp.rowCarrier (i + 1)), logCol, invTol,
    robDepths, D, Y, q2⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have hstruct : ∀ x ∈ (⟨[Sp.Q i], Nat.clog 2 (Sp.rowCarrier (i + 1)), logCol,
      invTol, robDepths, D, Y, q2⟩ : SuccessorOutputs).majorised,
      x ≤ structuralW Csize (normalizedL bout Bpub zR clE) := by
    intro x hx
    simp only [SuccessorOutputs.majorised, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with ((((hx | rfl | rfl) | hx) | hx) | rfl | rfl)
    · rw [hx]; exact hQrow
    · exact hRowrow
    · exact hColrow
    · exact hInvTol x hx
    · exact hRob x hx
    · exact hDrow
    · exact hYrow
  obtain ⟨⟨hlow, hup, -⟩, -, hqlog, hlogenv⟩ :=
    envelopeRealization_closes_the_two_sided_bound Sp hsched hs hdv hz i hb Em
      Csize bout Bpub zR clE n r S _ hn rfl rfl hstate hnval habs hboutS hBpubS
      hzRS hclE hstruct
  exact ⟨⟨hlow, hup⟩, hqlog, hlogenv⟩

/-! ## Part 9: the statement poles -/

/-- **Vacuous-hypothesis pole: the emitted tuple and the cutoff carry the whole
content.**

Lines `02:1373--1376` alone -- the checked pre-cutoff row -- do **not** bound a
root by `E_{16(c+1)}(n)`.  At every exponent and every source size there is a
recorded coefficient and a root satisfying that row and exceeding the envelope
outright, so `successorRootBound`'s emission and cutoff hypotheses are
load-bearing and the absorption of `eq:successor-pcut-normal-form` is not
decoration.

The coefficient and the root are **rejection-probe values claiming no
legality**: with the emitted tuple present, a coefficient this large forces
`PCut(2^{d_c}C, d_c, e_c)` up, hence `R(c)` up, hence `n_step(c)` up, which is
exactly the mechanism the probe removes.  General in the exponent and the source
size. -/
theorem cutoff_hypothesis_not_free (c n : ℕ) :
    ∃ C u : ℕ, u ≤ preCutoffRow C c n ∧ ¬ u ≤ envE (16 * (c + 1)) n := by
  refine ⟨envE (16 * (c + 1)) n, envE (16 * (c + 1)) n + 1, ?_, by omega⟩
  have h1 : envE (16 * (c + 1)) n + 1 ≤ 2 ^ envE (16 * (c + 1)) n :=
    Nat.lt_two_pow_self
  refine le_trans h1 ?_
  have h2 : (1 : ℕ) ≤ (ellN n + 2) ^ dExp c := Nat.one_le_pow _ _ (by omega)
  refine Nat.pow_le_pow_right (by norm_num) ?_
  exact Nat.le_mul_of_pos_right _ (by omega)

/-- **Absorption pole: the emitted first component is not the recorded
coefficient.**

`eq:successor-pcut-normal-form` emits `(2^{d_c}C_u, d_c, e_c)`, not
`(C_u, d_c, e_c)`, and `06:1935--1938` insists the registry "reconstructs
`Chat_u` by the displayed multiplication".  The two differ at every positive
coefficient and every exponent, so storing the raw literal in the cutoff
argument would be a different search.  General in the coefficient above zero and
in the exponent. -/
theorem absorbed_tuple_is_not_the_raw_tuple (C c : ℕ) (hC : 1 ≤ C) :
    absorbedCoeff C c ≠ C := by
  have hpow : (2 : ℕ) ^ dExp c ≥ 2 := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ dExp c :=
      Nat.pow_le_pow_right (by norm_num) (by unfold dExp; omega)
    simpa using this
  unfold absorbedCoeff
  nlinarith

/-! ## Part 10: the hypothesis-consistency probe (BEYOND-PAPER) -/

/-- **The paper's own successor emission at a coefficient function** --
`eq:successor-pcut-normal-form` (`06:1924--1934`): "`P(c)` contains **exactly**
the absorbed tuple `(Chat_u, d_c, e_c)`".

This is the successor-row half of the emission and nothing else: the fixed
rational cutoffs `F(c)`, the `ECut` list `E(c)` and the `DCut` list `D(c)` are
empty here, so this record is **not** the compiler's full emission.  By `R_mono`
adjoining those rows only raises `R(c)` and hence only strengthens the cutoff
hypothesis, so nothing proved at this emission is weakened by their absence --
but nothing here claims to be `Cert_c` (GAP-EXPOSED 1). -/
noncomputable def absorbedEmission (Cs : ℕ → ℕ) : CutoffEmission where
  fixedRational := fun _ => []
  eArgs := fun _ => []
  pArgs := fun c => [(absorbedCoeff (Cs c) c, dExp c, eExp c)]
  dArgs := fun _ => []

/-- **Aux 14 (the successor emission contains its own absorbed tuple).**
`eq:successor-pcut-normal-form` read off the record.  General. -/
theorem absorbedEmission_mem (Cs : ℕ → ℕ) (c : ℕ) :
    (absorbedCoeff (Cs c) c, dExp c, eExp c) ∈ (absorbedEmission Cs).pArgs c := by
  simp [absorbedEmission]

/-- **Aux 15 (the seed-exponent successor row has cutoff root two).**

At `c = c_0 = 3` the emitted tuple is `(2^{32}C_size, 32, 64)`, and the frozen
`PCut` predicate already holds at its floor `r = 2`, because
`2^{32}C_size * 4^{32} <= 4^{64}` whenever `C_size <= 2`.  Evaluated, not
assumed.  Stated at the frozen producer's own output
`SizePropagation.csizeLiteral [] []`. -/
theorem pCut_at_seed_exponent :
    pCut (absorbedCoeff (csizeLiteral [] []) (cexp 0)) (dExp (cexp 0))
      (eExp (cexp 0)) ≤ 2 := by
  refine Nat.sInf_le ?_
  have hC : csizeLiteral ([] : List (ℕ × ℕ)) ([] : List ℕ) = 2 := rfl
  refine ⟨le_refl 2, ?_⟩
  rw [hC]
  change 2 ^ dExp (cexp 0) * 2 * (2 + 2) ^ dExp (cexp 0) ≤ (2 + 2) ^ eExp (cexp 0)
  have hd : dExp (cexp 0) = 32 := rfl
  have he : eExp (cexp 0) = 64 := rfl
  rw [hd, he]
  have h1 : (4 : ℕ) ^ 32 = 2 ^ 64 := by norm_num
  have h2 : (4 : ℕ) ^ 64 = 2 ^ 128 := by norm_num
  have h3 : (2 : ℕ) ^ 32 * 2 = 2 ^ 33 := by ring
  rw [show (2 + 2 : ℕ) = 4 from rfl, h1, h2, h3, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- **Hypothesis-consistency probe for the envelope realization.**

**BEYOND-PAPER (GAP-EXPOSED 5).**  This audits our encoding at a point the paper
never visits: a one-row emission carrying only the successor tuple, at the seed
exponent `c_0 = 3`.  It claims no legality for any construction and stands in for
no canonical instance; the canonical statement is
`dominantWidth_two_sided_at_paperSpec`.

What it establishes is what the hypothesis-consistency rule demands: the full
hypothesis bundle of `traversalRealization` is satisfiable **together with its
conclusion**, so no `False` derives from it and the realization is not vacuous.
Every numeric input is either the frozen producer's evaluated output
(`C_size = csizeLiteral [] []`, the value `eq:Csize-literal-producer` returns on
an empty coefficient table) or forced by it; the source size stays a binder above
the evaluated cutoff `n_step(c_0) = 2^{2^4}`.

Non-degeneracy: the output record's auxiliary-width list is nonempty and its one
entry sits **at** the structural majorant `W(L)`, not below it, and its first
logarithmic side length is positive -- so the all-zero record does not satisfy
this statement. -/
theorem envelopeRealization_hypotheses_consistent (n : ℕ) (hn : 65536 ≤ n) :
    ∃ (Em : CutoffEmission) (Csize L : ℕ) (O : SuccessorOutputs),
      Csize = csizeLiteral [] [] ∧
        (absorbedCoeff Csize (cexp 0), dExp (cexp 0), eExp (cexp 0))
          ∈ Em.pArgs (cexp 0) ∧
        Em.nStep (cexp 0) ≤ n ∧
        L ≤ (ellN n + 2) ^ (cexp 0 + 1) ∧
        (∀ x ∈ O.majorised, x ≤ structuralW Csize L) ∧
        (∀ x ∈ O.majorised, x ≤ envE (eExp (cexp 0)) n) ∧
        O.auxWidths = [structuralW Csize L] ∧ 1 ≤ O.logRow := by
  classical
  set Cz : ℕ := csizeLiteral ([] : List (ℕ × ℕ)) ([] : List ℕ) with hCz
  set Em : CutoffEmission := absorbedEmission (fun _ => Cz) with hEm
  set O : SuccessorOutputs :=
    ⟨[structuralW Cz 7], 1, 0, [], [], 0, 0, 0⟩ with hO
  have hn1 : 1 ≤ n := by omega
  have habs : (absorbedCoeff Cz (cexp 0), dExp (cexp 0), eExp (cexp 0))
      ∈ Em.pArgs (cexp 0) := absorbedEmission_mem (fun _ => Cz) (cexp 0)
  -- the emission's cutoff root is exactly the frozen floor two
  have hroots : Em.roots (cexp 0)
      = [pCut (absorbedCoeff Cz (cexp 0)) (dExp (cexp 0)) (eExp (cexp 0))] := by
    simp [CutoffEmission.roots, hEm, absorbedEmission]
  have hpc2 : pCut (absorbedCoeff Cz (cexp 0)) (dExp (cexp 0)) (eExp (cexp 0))
      ≤ 2 := pCut_at_seed_exponent
  have hR : Em.R (cexp 0) = 2 := by
    have : literalMax (Em.roots (cexp 0)) ≤ 2 := by
      rw [hroots]
      rw [literalMax_cons]
      exact max_le hpc2 (by simp [literalMax])
    have h2 := two_le_R Em (cexp 0)
    have : Em.R (cexp 0) ≤ 2 := max_le (le_refl 2) this
    omega
  have hcut : Em.nStep (cexp 0) ≤ n := by
    change (2 : ℕ) ^ 2 ^ (Em.R (cexp 0) + 2) ≤ n
    rw [hR]
    have : (2 : ℕ) ^ 2 ^ (2 + 2) = 65536 := by norm_num
    omega
  have hell : 2 ≤ ellN n := two_le_ellN n
  have hL : (7 : ℕ) ≤ (ellN n + 2) ^ (cexp 0 + 1) := by
    have h4 : (4 : ℕ) ^ (cexp 0 + 1) ≤ (ellN n + 2) ^ (cexp 0 + 1) :=
      Nat.pow_le_pow_left (by omega) _
    have : (4 : ℕ) ^ (cexp 0 + 1) = 256 := by norm_num [cexp]
    omega
  have hmaj : O.majorised = [structuralW Cz 7, 1, 0, 0, 0] := by
    simp [hO, SuccessorOutputs.majorised]
  have hpos : (1 : ℕ) ≤ structuralW Cz 7 := by
    unfold structuralW
    exact Nat.one_le_two_pow
  have hstruct : ∀ x ∈ O.majorised, x ≤ structuralW Cz 7 := by
    rw [hmaj]
    refine List.forall_mem_cons.mpr ⟨le_refl _, ?_⟩
    refine List.forall_mem_cons.mpr ⟨hpos, ?_⟩
    refine List.forall_mem_cons.mpr ⟨Nat.zero_le _, ?_⟩
    refine List.forall_mem_cons.mpr ⟨Nat.zero_le _, ?_⟩
    refine List.forall_mem_cons.mpr ⟨Nat.zero_le _, ?_⟩
    simp
  refine ⟨Em, Cz, 7, O, rfl, habs, hcut, hL, hstruct, ?_, rfl, by simp [hO]⟩
  exact traversalRealization Em Cz 7 (cexp 0) n O hn1 habs hL hstruct hcut

/-- **Aux 17 (the cumulative threshold is positive).**

`13-iteration-assembly.tex:267--268` sets `n_val(0) = 1` and takes maxima
afterwards, so the threshold never drops below one at any index.  Needed so that
a probe may take the source size to be the threshold itself and still meet the
frozen `n >= 1` guard.  General in the cutoff function and the index. -/
theorem one_le_nval (nstep : ℕ → ℕ) (j : ℕ) : 1 ≤ nval nstep j := by
  induction j with
  | zero => simp
  | succ m ih => rw [nval_succ]; exact le_trans ih (le_max_left _ _)

/-- **Hypothesis-consistency probe for the closed two-sided bound.**

The rule demands that the full hypothesis bundle of the principal deliverable be
checked for joint satisfiability, so that a green build is not green-because-
vacuous.  Here the bundle of
`envelopeRealization_closes_the_two_sided_bound` is exhibited satisfied
**together with all four of its conclusions**, at an arbitrary carrier
specification satisfying `ScheduleTolerance` -- hence in particular at the
paper's own `FixedLevelCarriers.paperSeedSpec`, through the banked
`DominantWidthBound.paperSeedSpec_scheduleTolerance`.  No `False` derives from
the bundle.

There is no circularity in the choice: the recorded coefficient is read off the
output record, the emission from the coefficient, and only then the source size
from the emission's own threshold; the record's own entries do not depend on the
source size.

**The probe's own values claim no legality.**  The incoming state is the
all-zero record and the four `A_pre` inputs are zero, so `L` collapses to
`clog_2(16) = 4`; the recorded coefficient is the maximum of the record's
entries, not the frozen producer's output.  These are consistency-probe values,
exactly as the rejection probes of `SuccessorMajorant` are, and they stand in
for no paper instance.  The **canonical** statement is
`dominantWidth_two_sided_at_paperSpec`.

General in the specification, the level and the arrow. -/
theorem twoSidedBound_bundle_consistent
    (Sp : FixedLevelCarriers.LevelCarrierSpec) {s : ℕ} {dv zeta : ℝ}
    (hsched : ScheduleTolerance Sp s dv zeta) (hs : 3 < s) (hdv : 0 < dv)
    (hz : 0 < zeta) (i : ℕ) (hb : 1 ≤ Sp.bout i) (r : ℕ) :
    ∃ (Em : CutoffEmission) (Csize n : ℕ) (S : LevelState)
      (O : SuccessorOutputs),
      1 ≤ n ∧ S.UnderEnvelope (cexp r) n ∧ nval Em.nStep (r + 1) ≤ n ∧
        (absorbedCoeff Csize (cexp r), dExp (cexp r), eExp (cexp r))
          ∈ Em.pArgs (cexp r) ∧
        (0 : ℕ) ∈ S.quantities ∧
        (∀ x ∈ O.majorised, x ≤ structuralW Csize (normalizedL 0 0 0 0)) ∧
        O.auxWidths = [Sp.Q i] ∧
        O.logRow = Nat.clog 2 (Sp.rowCarrier (i + 1)) ∧
        47104000 * Sp.bout i * Sp.q i ≤ Sp.Q i ∧
        Sp.Q i ≤ envE (cexp (r + 1)) n ∧
        Sp.q i ≤ O.logRow ∧ O.logRow ≤ envE (cexp (r + 1)) n := by
  classical
  set O : SuccessorOutputs :=
    ⟨[Sp.Q i], Nat.clog 2 (Sp.rowCarrier (i + 1)), 0, [], [], 0, 0, 0⟩ with hO
  set Cz : ℕ := literalMax O.majorised with hCz
  set Em : CutoffEmission := absorbedEmission (fun _ => Cz) with hEm
  set S : LevelState := ⟨0, 0, 0, 0, 0, []⟩ with hS
  set n : ℕ := nval Em.nStep (r + 1) with hnDef
  have hn1 : 1 ≤ n := one_le_nval _ _
  have hq0 : (0 : ℕ) ∈ S.quantities := by simp [hS, LevelState.quantities]
  have hstate : S.UnderEnvelope (cexp r) n := by
    intro x hx
    have hx0 : x = 0 := by simpa [hS, LevelState.quantities] using hx
    simp [hx0]
  have hL : 1 ≤ normalizedL 0 0 0 0 :=
    le_trans (by norm_num) (four_le_normalizedL 0 0 0 0)
  have hstruct : ∀ x ∈ O.majorised,
      x ≤ structuralW Cz (normalizedL 0 0 0 0) :=
    structuralRow_satisfiable O.majorised hL
  have habs : (absorbedCoeff Cz (cexp r), dExp (cexp r), eExp (cexp r))
      ∈ Em.pArgs (cexp r) := absorbedEmission_mem (fun _ => Cz) (cexp r)
  have hQ : O.auxWidths = [Sp.Q i] := rfl
  have hrow : O.logRow = Nat.clog 2 (Sp.rowCarrier (i + 1)) := rfl
  obtain ⟨⟨hlow, hup, -⟩, -, hqlog, hlogenv⟩ :=
    envelopeRealization_closes_the_two_sided_bound Sp hsched hs hdv hz i hb Em
      Cz 0 0 0 0 n r S O hn1 hQ hrow hstate (le_refl _) habs hq0 hq0 hq0
      (Nat.zero_le _) hstruct
  exact ⟨Em, Cz, n, S, O, hn1, hstate, le_refl _, habs, hq0, hstruct, hQ, hrow,
    hlow, hup, hqlog, hlogenv⟩

end EthInapproximability.ParameterizedNP.EnvelopeRealization
