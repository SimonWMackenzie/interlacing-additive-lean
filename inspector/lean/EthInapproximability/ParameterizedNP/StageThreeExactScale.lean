import EthInapproximability.ParameterizedNP.StageTwoRelaxed

/-!
# Parameterized NP route: Stage 3, the exact scale and the Stage-4 handoff

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/07-one-level-construction.tex`,
  **lines 434--697** -- the Stage-3 block of `sec:one-level`.  The anchors
  traced here are, in the order the block prints them:
  * `lem:stage3-exact-scale` (opened at line 435, label line 436, statement
    lines 435--455) with its four assumptions
    `comp(M_2^T) = D_2`, `Lambda_3(M_2^T, 1, 2^{-b_2}, 3/5) >= D_2`,
    `2 <= D_2`, `1 <= b_2`, the scale data `s = 2^{w_s}`, `1 <= w_s <= b_2`,
    the definition `M_3 = Int_s(M_2^T)`, and the output
    `eq:stage3-exact-scale` (label line 453), `comp(M_3) = D_2 + w_s`;
  * the proof, lines 457--493: the sentence "The exact complexity and
    three-rung hypotheses say precisely that `Robust(f, 1/10, b_2)`"
    (lines 458--462); the binder dictionary for
    `NPCC.power_of_two_lower`/`eq:contract-power-two` (lines 463--470); the
    guard list (lines 471--473); the conclusion at
    `y = (1/2 + 1/10)^2 = 9/25` (lines 473--481); the nonemptiness sentence
    "Because `s <= 2^{b_2}`, the full row set in every copy meets the row
    threshold `s 2^{-b_2} <= 1`; the full column set meets the column
    threshold `9/25 <= 1`" (lines 482--486); and the converse selector call
    to `lem:interlace-selector-protocol` with transpose invariance
    (lines 486--491);
  * the instantiation paragraph, lines 495--510: "Stage 3 uses `s`, rather
    than four, classical copies" (495--498), the schedule data
    `w_s = log_2 s`, `s = 2^{w_s}`, `1 <= w_s <= b_2` and the frozen
    `D_2 >= B_cap >= 3` (499--501), the resulting
    `comp(M_3) = B_cap + log_2 q_2 + log_2 s` (502--507), and the closing
    sentence that the strict ceiling gates are *not* the source of this
    increment (508--510);
  * the direct-protocol subsection, lines 609--649: the Stage-1 local
    threshold `x_cap = 2^{a + 1 - b_0}` (lines 611--614), the odd-copy
    capacity inequality `eq:local-capacity-gap` (label line 621) with its
    literal reading `q_1 + 3 = 2^a + 1` (line 623), the `YES` local copy
    count `q_1 + 2 = 2^a` (lines 615--616, 629--630), the outer budget
    `K = a + log_2 q_2 + log_2 s` (line 632), the `YES` upper bound
    `comp(M_4) <= Y + K` (line 636), and the `NO` upper bound
    `eq:stage4-no-upper` (label line 645) with its copy count
    `q_1 + s + 1 <= 2^{a+1}` from `s <= A_* <= 2^a` (lines 638--641);
  * the two-scale profile targets, lines 662--680: the frozen
    `C = D + K + 1` (line 665), `eq:raw-dense` (label line 671) and
    `eq:raw-low` (label line 673), which are recorded here only as the
    *handoff budget*, not proved.
* **Co-anchor (same statements, mechanical-step form):**
  `11-one-level-assembly.tex`, Mechanical Step `step:L-05` (opened line 284,
  lines 284--329) and `step:L-06` (opened line 330, lines 330--358),
  including the binder table for `NPCC.power_of_two_lower` (lines 296--306),
  the separation gates `eq:stage3-separation-gates` (lines 318--329), and the
  displays `exp:E-06-yes` (label line 342) and `exp:E-06-no-upper` (label
  line 358).
* **Reader counterparts** (frozen release,
  `reader-facing/sections/03-parameterized-construction.tex`), one per
  declaration group, none of them shared with another module:
  * `eq:paper-M3-definition` (label line 457) -- `stageThree`;
  * `eq:paper-M3-gates` (label line 467) -- `separationGates`;
  * `eq:paper-M3-exact` (label line 497) -- `stageThree_scale` and
    `stageThree_scale_of_twoDepthCertificate`;
  * the display `K_0 := a + log q_2 + log s` (line 94) -- `outerBudget`;
  * `eq:paper-B-yes` (label line 573) -- `yesBudget_eq` / `yes_local_copies`;
  * `eq:paper-B-no-upper` (label line 582) -- `noBudget_eq` /
    `no_local_copies`.
  The Stage-2 reader displays `eq:paper-M2-robust`/`eq:paper-M2-aux-robust`
  are the *inputs* consumed here; they are the reader counterparts of
  `StageTwoRelaxed.stageTwoTwoDepthCertificate` and are deliberately not
  re-assigned to any declaration below.

## Dependencies, imports and external adapters

* Imports `EthInapproximability.ParameterizedNP.StageTwoRelaxed` only, hence
  transitively `StageOneInterlace`, `PilotStage3`, `PublicRecords`,
  `FiniteSlots` and the project-axiom-free `LegacyNPCC.Core`/`Bridge` facades
  through `EthInapproximability.Prelude`.  `LegacyNPCC.Stage12` -- whose
  closure reaches the cited AGHP balanced-family axiom -- is **not** imported,
  and no declaration here is in its dependency graph.
* Vendored interfaces consumed **by pin, never restated**:
  `NPCC.power_of_two_lower` (`eq:contract-power-two`), `NPCC.IsRobust`
  (`eq:contract-robust`), `NPCC.bracketGE`, `NPCC.bracketGE.nonempty`,
  `NPCC.Dfamily`, `NPCC.LambdaGE`, `NPCC.comp_transpose`
  (`eq:contract-comp-transpose`) and `Workspace.Types.Interlace.interlaceFun`.
* Banked project interfaces consumed **by pin, never restated**:
  `PilotStage3.stage3_exactScale`, `PilotStage3.interlace_selector_upper`,
  `PilotStage3.familyComplexity_le_ambient`,
  `StageOneInterlace.xSeed`, `StageOneInterlace.stage1Legal`,
  `FiniteSlots.Stage1SlotBinding`, `StageTwoRelaxed.StageTwoWidths`,
  `StageTwoRelaxed.stageTwo`, `StageTwoRelaxed.stageTwoT`,
  `StageTwoRelaxed.D_stageTwoT`, `StageTwoRelaxed.dTwo`,
  `StageTwoRelaxed.bigWidths`, `StageTwoRelaxed.depthTwoWitness`,
  `PublicRecords.LevelParams`, `PublicRecords.D_const`.
* Proof status: **adapted**.  The exact-scale equality is the banked pilot
  `PilotStage3.stage3_exactScale` (itself an assembly of the vendored
  `power_of_two_lower` and the banked selector protocol); what is new here is
  (i) the frozen robustness dictionary of lines 458--462, proved in **both**
  directions, and (ii) the discharge of the pilot's bracket-nonemptiness
  binder from the frozen sentence of lines 482--486.  The Stage-4 promise
  budgets are the block's own arithmetic, proved.
* Axiom surface (`#print axioms`, recorded in `tools/AxiomAudit.lean`):
  `propext`, `Classical.choice`, `Quot.sound` only.  No project axiom, no
  unproved placeholder of any kind, no new opaque certificate.

## Candidate encodings of `lem:stage3-exact-scale` (`k = 2`, raced)

* **Candidate A (landed).**  `StageThreeScale` stores exactly the two
  schedule integers the frozen instantiation paragraph names, `w_s` and
  `b_2`, together with the two frozen gates `1 <= w_s` and `w_s <= b_2`
  (`07:499--501`).  The bin count is the *derived* `sVal = 2^{w_s}`, and the
  four hypotheses of the lemma are **explicit binders** on the theorem, with
  `NPCC.IsRobust` obtained from them by the proved dictionary
  `isRobust_iff_lambda`.
* **Candidate B (rejected).**  Store `s` as its own field beside `w_s` with a
  linking field `s = 2^{w_s}`, and store `NPCC.IsRobust f (1/10) b_2` as a
  field of the record, so that the lemma reads "for every Stage-3
  certificate".

  Candidate B is rejected on two kernel-checkable grounds.  First, its `s`
  field restates a derived telescope: under A the frozen selector width is
  `Nat.clog 2 (sVal) = w_s` by `clog_sVal`, with nothing to rewrite.  Second,
  and decisively, a stored `IsRobust` field is a **robustness conclusion in
  constructor data**, which entry requirement 4 of the route ledger and
  mechanical rule `M9` forbid; `constant_not_isRobust` proves in the kernel
  that the would-be field is genuine mathematical content (it fails at the
  legal constant matrix), so B's record could not be inhabited at all at the
  numeric schedule values, and its LANE-GATE 3 witness
  `stageThreeScaleWitness` would not exist.
  Ranking (aux lemmas proved, faithfulness, length): A wins all three.

## Honest scope and recorded coverage limits

1. Nothing here asserts that any concrete matrix is `(1/10, b_2)`-robust.
   The Stage-2 two-depth certificate is consumed as a named binder exactly as
   `StageTwoRelaxed.stageTwoTwoDepthCertificate` leaves it; the four
   inherited endpoints behind it remain open, as that module's coverage limit
   records.  `isRobust_iff_lambda` and `LambdaGE_le_D` establish that the
   hypothesis bundle assumed here is neither stronger nor weaker than the
   vendored premise of `power_of_two_lower`, which is the strongest
   non-vacuity statement available before those endpoints land.
2. The raw Stage-4 matrix `B` of `eq:raw-stage4-universes` is **not** defined
   in this module.  The `YES`/`NO` promise directions are therefore recorded
   in the form the Stage-3 block hands them forward -- the outer budget `K`,
   the two literal copy counts `q_1 + 2 = 2^a` and `q_1 + s + 1 < 2^{a+1}`,
   and the two budget identities `Y + K` and `D + K + 1` -- and **no** claim
   is made about `comp(B)`.
3. `eq:local-capacity-gap` is transcribed as the predicate
   `localCapacityGap`, never asserted.  Its two literal readings
   (`q_1 + 3 = 2^a + 1` and `(1/2 + 1/10)^2 = 9/25`) are proved.
4. No parameter schedule may be read out of `stageThreeScaleWitness` or
   `handoffWitness`; they inherit the coverage limits of
   `StageOneInterlace.stage1Legal` and `StageTwoRelaxed.bigWidths`.
-/

namespace EthInapproximability.ParameterizedNP.StageThreeExactScale

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.StageOneInterlace
open EthInapproximability.ParameterizedNP.StageTwoRelaxed
open EthInapproximability.ParameterizedNP.PublicRecords (LevelParams)

variable {X Y : Type*}

/-! ## §0  The Stage-3 scale record

`07-one-level-construction.tex:441--450` fixes `w_s` by
`s = 2^{w_s}`, `1 <= w_s`, `w_s <= b_2`; `07:499--501` repeats the same three
clauses as the schedule's supply.  Only `1 <= w_s` and `w_s <= b_2` are
fields: `s` is derived, and `s <= 2^{b_2}` -- the first gate of
`eq:stage3-separation-gates` -- is a theorem below, not a field (`M3`). -/

/-- **The Stage-3 scale record.**  Two schedule integers and the two frozen
gates of `lem:stage3-exact-scale` that are not consequences of the rest.

*Honest scope (`M2`/`M4`/`M9`).*  The record asserts nothing about any matrix,
protocol, promise branch or complexity value: `gates_are_numeric` checks that
the whole field bundle is decidable from `(w_s, b_2)` alone. -/
structure StageThreeScale where
  /-- `w_s = log_2 s`, the Stage-3 selector width (`07:447`, `07:500`). -/
  wS : ℕ
  /-- The **ordinary** Stage-2 proof depth `b_2`.  `07:431--433`: "The
  ordinary depth `b_2` controls Stage 3"; the auxiliary depth `b_T` is
  deliberately not a field here. -/
  b₂ : ℕ
  /-- `1 <= w_s` (`07:447`, `07:500`): Stage 3 is a genuine interlace, never
  the one-copy degeneracy. -/
  one_le_wS : 1 ≤ wS
  /-- `w_s <= b_2` (`07:447`, `07:500`): the depth clause that makes the
  `NPCC.power_of_two_lower` call legal and, through `sVal_le_two_pow_b₂`,
  supplies the first gate of `eq:stage3-separation-gates`. -/
  wS_le_b₂ : wS ≤ b₂

namespace StageThreeScale

variable (S : StageThreeScale)

/-- The Stage-3 bin count `s = 2^{w_s}` (`07:447`).  Derived, never stored. -/
def sVal : ℕ := 2 ^ S.wS

@[simp] theorem sVal_eq : S.sVal = 2 ^ S.wS := rfl

/-! ### Aux-lemma battery.  Every lemma in this battery is general in `S`. -/

/-- **Aux 1 (nondegenerate bin count).**  `s >= 2`: the frozen `1 <= w_s`
forbids the one-copy interlace, at which the exact-scale increment would be
`0` and Stage 3 would add nothing. -/
theorem two_le_sVal : 2 ≤ S.sVal := by
  have h : (2:ℕ) ^ 1 ≤ 2 ^ S.wS := Nat.pow_le_pow_right (by norm_num) S.one_le_wS
  simpa [sVal] using h

theorem sVal_pos : 0 < S.sVal := lt_of_lt_of_le (by norm_num) S.two_le_sVal

/-- **Aux 2 (`M3`: the first separation gate is derived, not a field).**
`s <= 2^{b_2}`, the first clause of `eq:stage3-separation-gates`
(`06-parameter-schedule.tex:1084--1089`) and of `eq:paper-M3-gates`, follows
from `w_s <= b_2` alone. -/
theorem sVal_le_two_pow_b₂ : S.sVal ≤ 2 ^ S.b₂ :=
  Nat.pow_le_pow_right (by norm_num) S.wS_le_b₂

/-- **Aux 3 (the exact selector width).**  `ceil(log_2 s) = w_s`, so the
selector protocol of `lem:interlace-selector-protocol` sends exactly `log_2 s`
bits -- the frozen "sends the `s`-selector in `log_2 s` bits"
(`11-one-level-assembly.tex:312--313`) -- with no rounding slack. -/
theorem clog_sVal : Nat.clog 2 S.sVal = S.wS := Nat.clog_pow 2 _ (by norm_num)

theorem log_sVal : Nat.log 2 S.sVal = S.wS := Nat.log_pow (by norm_num) _

/-- **Aux 4 (the frozen row threshold).**  `s 2^{-b_2} <= 1`, the first half
of the nonemptiness sentence at `07:482--483`.  This is the exact real
expression `power_of_two_lower` uses for its bracket row density. -/
theorem rowThreshold_le_one :
    (2 : ℝ) ^ (S.wS : ℕ) * (2 : ℝ) ^ (-(S.b₂ : ℝ)) ≤ 1 := by
  have hcast : ((2 : ℝ) ^ (S.wS : ℕ)) = (2 : ℝ) ^ ((S.wS : ℕ) : ℝ) :=
    (Real.rpow_natCast 2 S.wS).symm
  rw [hcast, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
  have h : ((S.wS : ℕ) : ℝ) ≤ ((S.b₂ : ℕ) : ℝ) := Nat.cast_le.2 S.wS_le_b₂
  linarith

/-- **`M2`/`M4` check.**  The whole field bundle is decidable from the two
numerals alone; no matrix, protocol, promise certificate or complexity value
enters it. -/
theorem gates_are_numeric : 1 ≤ S.wS ∧ S.wS ≤ S.b₂ := ⟨S.one_le_wS, S.wS_le_b₂⟩

theorem one_le_b₂ : 1 ≤ S.b₂ := le_trans S.one_le_wS S.wS_le_b₂

end StageThreeScale

/-- **Aux 5 (the frozen column threshold).**  `(1/2 + 1/10)^2 = 9/25 <= 1`,
the second half of the nonemptiness sentence at `07:483--484`, and the exact
value `07:475--480` prints for the bracket's column density. -/
theorem columnThreshold :
    ((1 : ℝ) / 2 + 1 / 10) ^ 2 = 9 / 25 ∧ (9 : ℝ) / 25 ≤ 1 := by
  constructor <;> norm_num

/-! ## §1  Why bracket nonemptiness is load-bearing

`NPCC.Dfamily` is a `Nat.sInf` and returns `0` on the empty family, so a
family lower bound taken without nonemptiness would be unsound.  The frozen
proof supplies the witness explicitly ("the full row set in every copy ...
the full column set", `07:482--486`), and that is exactly what
`bracketGE.nonempty` consumes. -/

/-- **Aux 6 (`Dfamily` collapses on the empty family).**  General in `f`. -/
theorem Dfamily_empty {A B : Type*} (f : A → B → Bool) :
    Dfamily f (∅ : Set (Finset A × Finset B)) = 0 := by
  have hset :
      {d : ℕ | ∃ RC ∈ (∅ : Set (Finset A × Finset B)),
        d = D (subgame f RC.1 RC.2)} = (∅ : Set ℕ) := by
    ext d
    simp
  rw [Dfamily, hset, Nat.sInf_empty]

/-- **Aux 7 (the discharged binder).**  The bracket family that
`power_of_two_lower` lower-bounds is nonempty at the Stage-3 data, by the
frozen sentence `07:482--486`: the full row set meets `s 2^{-b_2} <= 1` and
the full column set meets `9/25 <= 1`.

The banked pilot `PilotStage3.stage3_exactScale` carries this as a
hypothesis; here it is proved from `w_s <= b_2` and nonemptiness of the row
carrier, so no consumer of `stageThreeExactScale` has to supply it. -/
theorem stageThree_bracket_nonempty {X Y : Type*} [Fintype X] [Fintype Y]
    (S : StageThreeScale) (hX : 1 ≤ Fintype.card X) :
    (bracketGE X Y (2 ^ S.wS)
      ((2 : ℝ) ^ (S.wS : ℕ) * (2 : ℝ) ^ (-(S.b₂ : ℝ)))
      (((1 : ℝ) / 2 + 1 / 10) ^ 2)).Nonempty := by
  classical
  refine bracketGE.nonempty (2 ^ S.wS) _ _ S.rowThreshold_le_one ?_ hX
  rw [columnThreshold.1]
  exact columnThreshold.2

/-! ## §2  The frozen robustness dictionary

`07:458--462`: "Set `f = M_2^T`.  The exact complexity and three-rung
hypotheses say precisely that `Robust(f, 1/10, b_2)`."  The word *precisely*
is transcribed as an `iff`, so the hypothesis bundle assumed by
`stageThreeExactScale` is neither stronger nor weaker than the vendored
premise of `eq:contract-power-two`.

Note the exact density dictionary at `delta = 1/10`, which is why the frozen
`y = 3/5` three-rung quantity is the right object:
`1/2 + delta = 3/5`, `1/4 + delta/2 = 3/10 = (3/5)/2`,
`1/8 + delta/4 = 3/20 = (3/5)/4`. -/

/-- **Aux 8 (the three-rung quantity never exceeds the ambient complexity).**

`Lambda_3(f, 1, x, y) <= comp(f)` whenever the one-copy bracket family is
nonempty.  General in `f`, `x`, `y`.

This is the anti-over-strength check demanded of every new hypothesis bundle:
it shows that the frozen clause `Lambda_3(M_2^T, 1, 2^{-b_2}, 3/5) >= D_2`,
read together with `comp(M_2^T) = D_2`, is a *saturation equality* and can
never be a demand exceeding the ambient complexity.  In particular the bundle
of `stageThreeExactScale` cannot be contradictory for that reason. -/
theorem LambdaGE_le_D {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {x y : ℝ} (hx1 : x ≤ 1) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) :
    LambdaGE f 1 x y ≤ D f := by
  classical
  have hne := bracketGE.nonempty (X := X) (Y := Y) 1 x y hx1 hy1 hX
  have hfam := familyComplexity_le_ambient (interlaceFun f 1) hne
  have hone : D (interlaceFun f 1) ≤ D f := by
    have h1 := interlace_selector_upper f 1 (le_refl 1)
    rwa [Nat.clog_one_right, Nat.add_zero] at h1
  have hmin : LambdaGE f 1 x y ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x y) := by
    simp only [LambdaGE]
    exact min_le_left _ _
  exact le_trans hmin (le_trans hfam hone)

/-- **The frozen dictionary of `07:458--462`, both directions.**

At `delta = 1/10` and depth `b_2`, and given the exact complexity
`comp(f) = D_2` with the frozen `2 <= D_2`, the three-rung certificate
`Lambda_3(f, 1, 2^{-b_2}, 3/5) >= D_2` is **equivalent** to
`NPCC.IsRobust f (1/10) b_2`.

Neither side is an axiom: `IsRobust` is the vendored `eq:contract-robust`
predicate and `LambdaGE` the vendored three-rung minimum, and the proof is
the density dictionary above plus the `ℤ`-to-`ℕ` reading of clauses R3/R4.
The guard `2 <= D_2` is the frozen third assumption of
`lem:stage3-exact-scale`; it is what discharges the vendored clause R1. -/
theorem isRobust_iff_lambda {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (b₂ d : ℕ) (hexact : D f = d) (htwo : 2 ≤ d) :
    IsRobust f (1 / 10) (b₂ : ℝ) ↔ d ≤ LambdaGE f 1 (xSeed b₂) (3 / 5) := by
  have e1 : (1 : ℝ) / 2 + 1 / 10 = 3 / 5 := by norm_num
  have e2 : (1 : ℝ) / 8 + (1 / 10) / 4 = 3 / 5 / 4 := by norm_num
  have e3 : (1 : ℝ) / 4 + (1 / 10) / 2 = 3 / 5 / 2 := by norm_num
  simp only [IsRobust, LambdaGE, xSeed, e1, e2, e3, le_min_iff]
  constructor
  · rintro ⟨-, h2, h3, h4⟩
    rw [hexact] at h2
    rw [hexact] at h3
    rw [hexact] at h4
    exact ⟨h2, by omega, by omega⟩
  · rintro ⟨h2, h3, h4⟩
    rw [hexact]
    exact ⟨by omega, h2, by omega, by omega⟩

/-! ## §3  `lem:stage3-exact-scale`

`07-one-level-construction.tex:435--493` (statement and proof), reader
`eq:paper-M3-exact` (`03-parameterized-construction.tex:493--498`). -/

/-- **`lem:stage3-exact-scale`, in the frozen hypothesis shape.**

Assume, exactly as `07:437--448`,
```
comp(f) = D_2,   Lambda_3(f, 1, 2^{-b_2}, 3/5) >= D_2,   2 <= D_2,   1 <= b_2,
s = 2^{w_s},     1 <= w_s,     w_s <= b_2,
```
and put `M_3 = Int_s(f)`.  Then `comp(M_3) = D_2 + w_s`
(`eq:stage3-exact-scale`).

`1 <= b_2` is the record's `one_le_b₂` and is therefore not a separate binder.
The proof is the banked `PilotStage3.stage3_exactScale` consumed by pin at
`delta = 1/10`, `b = b_2`, `w = w_s`, with two inputs supplied here that the
pilot leaves open: the robustness premise, via the frozen dictionary
`isRobust_iff_lambda`, and the bracket nonemptiness, via
`stageThree_bracket_nonempty`.  Nothing of the pilot is restated.

*On the one extra binder.*  `hX : 1 <= card(Rows(f))` is not an addition to
the frozen hypotheses: at the construction `f = M_2^T`, whose row carrier is
`Cols(M_2) = L_2`, it is the frozen structural field `0 < N_2` of
`def:level-parameters` (`05-public-records.tex:183--186`), and
`stageThree_scale` discharges it from `Pr.N_2pos`, so the theorem at the
construction carries no extra hypothesis at all.  It cannot be dropped in the
abstract statement: `Dfamily_empty` shows that on an empty carrier the bracket
family is empty and `Dfamily` collapses to `0`, so the frozen family lower
bound would be unsound.

*Statement pole.*  The conclusion is not automatic: `exactScale_not_automatic`
exhibits a legal constant matrix at which `comp(Int_s(f)) = 0` while
`comp(f) + w_s = w_s >= 1`, so the hypotheses do real work; the clause that
fails there is `2 <= D_2`. -/
theorem stageThreeExactScale {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (S : StageThreeScale) (d : ℕ)
    (hX : 1 ≤ Fintype.card X)
    (hexact : D f = d)
    (hlambda : d ≤ LambdaGE f 1 (xSeed S.b₂) (3 / 5))
    (htwo : 2 ≤ d) :
    D (interlaceFun f S.sVal) = d + S.wS := by
  classical
  have hrobust : IsRobust f (1 / 10) (S.b₂ : ℝ) :=
    (isRobust_iff_lambda f S.b₂ d hexact htwo).2 hlambda
  have hb : (1 : ℝ) ≤ (S.b₂ : ℝ) := by
    have h : (1 : ℕ) ≤ S.b₂ := S.one_le_b₂
    exact_mod_cast h
  have hwdepth : (S.wS : ℝ) ≤ (S.b₂ : ℝ) := Nat.cast_le.2 S.wS_le_b₂
  have hcomplex : 2 ≤ D f := by rw [hexact]; exact htwo
  have hne := stageThree_bracket_nonempty (X := X) (Y := Y) S hX
  have hmain :=
    stage3_exactScale hrobust hb (by norm_num) (by norm_num) hcomplex S.wS
      S.one_le_wS hwdepth hne
  rw [StageThreeScale.sVal_eq, hmain, hexact]

/-! ## §4  Stage 3 of the construction

`M_3 = Int_s(M_2^T)` (`07:497`), reader `eq:paper-M3-definition`
(`03:454--458`).  The Stage-2 transpose is the banked `stageTwoT`, consumed by
pin; nothing of Stage 2 is restated. -/

/-- **Stage 3, `eq:paper-M3-definition`.**  The classical `s`-fold interlace of
the transposed Stage-2 matrix, with `s = 2^{w_s}` supplied by the record.

The frozen sentence is "Stage 3 uses `s`, rather than four, classical copies"
(`07:495--498`), and that is literally the definition: the vendored
`interlaceFun` at copy count `sVal`. -/
def stageThree (F : Stage1SlotBinding) (R : X → Y → Bool) (W : StageTwoWidths)
    (Pr : LevelParams (Stage1Rows F X) W.q₂) (S : StageThreeScale) :
    Fin S.sVal × Slot Pr.N₂ →
      (Fin S.sVal → Slot W.q₂ × Stage1Cols F Y) → Bool :=
  interlaceFun (stageTwoT F R W Pr) S.sVal

/-- The frozen value equation of Stage 3, definitionally: the Stage-2 entry
read at the selected copy's column tuple. -/
@[simp] theorem stageThree_apply (F : Stage1SlotBinding) (R : X → Y → Bool)
    (W : StageTwoWidths) (Pr : LevelParams (Stage1Rows F X) W.q₂)
    (S : StageThreeScale) (p : Fin S.sVal × Slot Pr.N₂)
    (c : Fin S.sVal → Slot W.q₂ × Stage1Cols F Y) :
    stageThree F R W Pr S p c = stageTwo F R W Pr (c p.1) p.2 := rfl

/-- **Aux 9 (the Stage-3 carriers, `M7`/`M10`).**  `|Rows(M_3)| = s N_2` and
`|Cols(M_3)| = (q_2 n_R^{L_1})^s`, the literal carriers of the classical
interlace at copy count `s`.  Both are nonzero, so neither side of Stage 3 can
silently collapse.  General in `F`, `R`, `W`, `Pr`, `S`, `Y`. -/
theorem stageThree_carriers (F : Stage1SlotBinding) (W : StageTwoWidths)
    (Pr : LevelParams (Stage1Rows F X) W.q₂) (S : StageThreeScale)
    (Y : Type*) [Fintype Y] :
    Fintype.card (Fin S.sVal × Slot Pr.N₂) = S.sVal * Pr.N₂ ∧
      Fintype.card (Fin S.sVal → Slot W.q₂ × Stage1Cols F Y) =
        (W.q₂ * Fintype.card Y ^ F.L₁) ^ S.sVal ∧
      0 < S.sVal * Pr.N₂ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  · rw [Fintype.card_fun, Fintype.card_fin, stageTwo_rows_card F W Y]
  · exact Nat.mul_pos S.sVal_pos Pr.N₂pos

/-- **`eq:paper-M3-exact` / `eq:stage3-exact-scale` at the construction.**

`comp(M_3) = D_2 + w_s`, for `M_3 = Int_s(M_2^T)` and the Stage-2 certified
scale `D_2 = B_cap + log_2 q_2`.

The two remaining binders are precisely the two Stage-2 outputs the frozen
text names at `07:502--503`: the exact transposed scale and the ordinary-depth
three-rung certificate.  `2 <= D_2` is *not* a binder: it is derived from the
frozen `D_2 >= B_cap >= 3` (`07:501`), which is why `hthree` appears instead. -/
theorem stageThree_scale (F : Stage1SlotBinding) (R : X → Y → Bool)
    (W : StageTwoWidths) (Pr : LevelParams (Stage1Rows F X) W.q₂)
    (S : StageThreeScale) [Fintype Y] (bCapVal : ℕ)
    (hthree : 3 ≤ bCapVal)
    (hexact : D (stageTwoT F R W Pr) = dTwo bCapVal W.r₂)
    (hlambda : dTwo bCapVal W.r₂ ≤
      LambdaGE (stageTwoT F R W Pr) 1 (xSeed S.b₂) (3 / 5)) :
    D (stageThree F R W Pr S) = bCapVal + W.r₂ + S.wS := by
  have hX : 1 ≤ Fintype.card (Slot Pr.N₂) := by
    rw [stageTwo_cols_card Pr]; exact Pr.N₂pos
  have htwo : 2 ≤ dTwo bCapVal W.r₂ := by
    simp only [dTwo]
    omega
  have h :=
    stageThreeExactScale (stageTwoT F R W Pr) S (dTwo bCapVal W.r₂) hX hexact
      hlambda htwo
  simpa [stageThree, dTwo] using h

/-- **The Stage-3 scale from the Stage-2 two-depth certificate, by pin.**

This consumes the *exact conclusion type* of
`StageTwoRelaxed.stageTwoTwoDepthCertificate` -- the triple
`comp(M_2) = D_2`, the ordinary-depth `Lambda_3` bound at `b_2`, and the
auxiliary-depth bound at `b_T` -- and produces
`comp(M_3) = B_cap + log_2 q_2 + log_2 s`, which is the frozen display at
`07:502--507`.

Two frozen facts are visible in the proof.  First, `comp(M_2^T) = comp(M_2)`
is the checked `NPCC.comp_transpose`, consumed through the banked
`StageTwoRelaxed.D_stageTwoT`; nothing is re-proved.  Second, **only** the
`b_2` conjunct is used -- `hcert.2.1` is forwarded and `hcert.2.2` is consumed
by nothing -- which is the frozen `07:431--433` role split: the auxiliary
depth `b_T` "is used only in the deletion-stable and scale-alignment parts of
the adapted Stage 4".  The checkable form of that separation is the
`b_T`-free binder list of `stageThree_scale`; see the note below. -/
theorem stageThree_scale_of_twoDepthCertificate (F : Stage1SlotBinding)
    (R : X → Y → Bool) (W : StageTwoWidths)
    (Pr : LevelParams (Stage1Rows F X) W.q₂) (S : StageThreeScale)
    [Fintype Y] (bCapVal bT : ℕ) (hthree : 3 ≤ bCapVal)
    (hcert :
      D (stageTwo F R W Pr) = dTwo bCapVal W.r₂ ∧
        dTwo bCapVal W.r₂ ≤
          LambdaGE (stageTwoT F R W Pr) 1 (xSeed S.b₂) (3 / 5) ∧
        dTwo bCapVal W.r₂ ≤
          LambdaGE (stageTwoT F R W Pr) 1 (xSeed bT) (3 / 5)) :
    D (stageThree F R W Pr S) = bCapVal + W.r₂ + S.wS := by
  refine stageThree_scale F R W Pr S bCapVal hthree ?_ hcert.2.1
  rw [D_stageTwoT F R W Pr]
  exact hcert.1

/-! ### Note: `07:431--433`, which depth controls Stage 3

The frozen sentence reads: "The ordinary depth `b_2` controls Stage 3.  The
auxiliary depth `b_T` is used only in the deletion-stable and scale-alignment
parts of the adapted Stage 4."

That role split is already witnessed, with content, by `stageThree_scale`
above: its statement carries **no** `b_T` binder at all -- the only depth it
mentions is the record's `b_2`, through `xSeed S.b₂` -- and it is the
declaration the construction actually uses.
`stageThree_scale_of_twoDepthCertificate` is the pinned adapter that accepts
the full Stage-2 triple `eq:stage2-two-depth-certificate` and forwards only
`hcert.2.1`, the ordinary-depth conjunct; the auxiliary-depth conjunct
`hcert.2.2` is carried forward to the adapted Stage 4 and is consumed by
nothing in this module.

This is recorded as a note rather than as a theorem, deliberately.  A Lean
statement of the form "the two proofs obtained at auxiliary depths `b_T` and
`b_T'` coincide" is closed by `rfl` for *any* two inhabitants of *any* `Prop`
under Lean 4's definitional proof irrelevance, so it would compile green while
establishing nothing whatever about `b_T`; and the conclusion type of
`stageThree_scale_of_twoDepthCertificate` is already `b_T`-free by
construction, so no content-bearing equational form of the separation exists.
The `b_T`-free binder list of `stageThree_scale` is the kernel-checkable
statement, and it is the one the ledger row cites. -/

/-! ## §5  The separation gates

`eq:stage3-separation-gates` (`06-parameter-schedule.tex:1084--1089`), reader
`eq:paper-M3-gates` (`03:459--468`).  The frozen text is explicit that these
gates feed the classical near-exact separation theorem and are **not** the
source of the exact increment proved in §3 (`07:508--510`,
`11-one-level-assembly.tex:325--329`). -/

/-- **`eq:paper-M3-gates`.**  The two frozen gates at column carrier size
`N_2 = |Cols(M_2)|`:
```
s <= 2^{b_2},        s ceil(2^{1-b_2} N_2) < N_2.
```
A predicate, never an assertion. -/
def separationGates (S : StageThreeScale) (N₂ : ℕ) : Prop :=
  S.sVal ≤ 2 ^ S.b₂ ∧
    S.sVal * ⌈(2 : ℝ) ^ (1 - (S.b₂ : ℝ)) * (N₂ : ℝ)⌉₊ < N₂

/-- **The frozen derivation of the strict ceiling gate**
(`06-parameter-schedule.tex:1069--1081`, reader `03:469--492`):
```
s ceil(2^{1-b_2} N_2) <= N_2/1024 + s <= (513/1024) N_2 < N_2.
```
The two inputs are exactly the frozen ones: the density bound
`s 2^{1-b_2} <= 1/1024` and the carrier bound `2 s <= N_2` (the frozen
`N_2 >= q_2^2 >= 2 s`).  General in `S` and `N_2`. -/
theorem separationGates_of_density (S : StageThreeScale) (N₂ : ℕ)
    (hden : (S.sVal : ℝ) * (2 : ℝ) ^ (1 - (S.b₂ : ℝ)) ≤ 1 / 1024)
    (hcarrier : 2 * S.sVal ≤ N₂) (hN : 0 < N₂) :
    separationGates S N₂ := by
  refine ⟨S.sVal_le_two_pow_b₂, ?_⟩
  have hspos : (0 : ℝ) < (S.sVal : ℝ) := by exact_mod_cast S.sVal_pos
  have hNpos : (0 : ℝ) < (N₂ : ℝ) := by exact_mod_cast hN
  have hzpos : (0 : ℝ) ≤ (2 : ℝ) ^ (1 - (S.b₂ : ℝ)) * (N₂ : ℝ) :=
    le_of_lt (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hNpos)
  have hceil :
      (⌈(2 : ℝ) ^ (1 - (S.b₂ : ℝ)) * (N₂ : ℝ)⌉₊ : ℝ) <
        (2 : ℝ) ^ (1 - (S.b₂ : ℝ)) * (N₂ : ℝ) + 1 :=
    Nat.ceil_lt_add_one hzpos
  have hdenN :
      (S.sVal : ℝ) * ((2 : ℝ) ^ (1 - (S.b₂ : ℝ)) * (N₂ : ℝ)) ≤ (N₂ : ℝ) / 1024 := by
    have := mul_le_mul_of_nonneg_right hden (le_of_lt hNpos)
    calc (S.sVal : ℝ) * ((2 : ℝ) ^ (1 - (S.b₂ : ℝ)) * (N₂ : ℝ))
        = (S.sVal : ℝ) * (2 : ℝ) ^ (1 - (S.b₂ : ℝ)) * (N₂ : ℝ) := by ring
      _ ≤ 1 / 1024 * (N₂ : ℝ) := this
      _ = (N₂ : ℝ) / 1024 := by ring
  have hcar : 2 * (S.sVal : ℝ) ≤ (N₂ : ℝ) := by exact_mod_cast hcarrier
  have hreal :
      (S.sVal : ℝ) * (⌈(2 : ℝ) ^ (1 - (S.b₂ : ℝ)) * (N₂ : ℝ)⌉₊ : ℝ) < (N₂ : ℝ) := by
    have hstep :
        (S.sVal : ℝ) * (⌈(2 : ℝ) ^ (1 - (S.b₂ : ℝ)) * (N₂ : ℝ)⌉₊ : ℝ) <
          (S.sVal : ℝ) * ((2 : ℝ) ^ (1 - (S.b₂ : ℝ)) * (N₂ : ℝ) + 1) :=
      mul_lt_mul_of_pos_left hceil hspos
    nlinarith [hstep, hdenN, hcar, hNpos]
  exact_mod_cast hreal

/-! ## §6  The Stage-3-to-Stage-4 handoff record and both promise directions

`07-one-level-construction.tex:609--649`, reader `03:562--583`.  What Stage 3
hands to Stage 4 is a record of **public integers and gates**: the outer
budget `K`, the two local copy counts, and the two promise budgets.  No claim
about `comp(B)` is made here (coverage limit 2 in the module header). -/

/-- **The Stage-3-to-Stage-4 handoff record.**  The scale record together with
the two frozen linking clauses that the Stage-4 direct protocols need:

* `s = 2^{w_s}` -- the schedule's power-of-two bin count
  (`05-public-records.tex:416--420`, `07:499--500`), tying the banked
  `Stage1SlotBinding.s` to the Stage-3 selector width;
* `s <= 2^a` -- the frozen `s <= A_* <= 2^a` of `07:639--641`
  (`eq:Astar-choice` with `eq:stage1-scales`), reader `03:577--578`, which is
  the only extra input of the `NO` copy count.

*Honest scope (`M9`).*  No complexity, robustness or promise conclusion is a
field: `handoff_is_numeric` checks that the bundle is decidable from
`(a, s, w_s, b_2)` alone. -/
structure StageThreeHandoff (F : Stage1SlotBinding) where
  /-- The Stage-3 schedule integers. -/
  scale : StageThreeScale
  /-- `s = 2^{w_s}`. -/
  s_eq : F.s = scale.sVal
  /-- `s <= 2^a`. -/
  s_le_two_pow_a : F.s ≤ 2 ^ F.a

namespace StageThreeHandoff

theorem handoff_is_numeric {F : Stage1SlotBinding} (H : StageThreeHandoff F) :
    F.s = 2 ^ H.scale.wS ∧ F.s ≤ 2 ^ F.a ∧ 1 ≤ H.scale.wS ∧
      H.scale.wS ≤ H.scale.b₂ :=
  ⟨H.s_eq, H.s_le_two_pow_a, H.scale.one_le_wS, H.scale.wS_le_b₂⟩

/-- **Aux 10 (`s >= 2` at the handoff).**  The Stage-1 seed tail really does
carry at least two active slots, so the Stage-4 substitution `4 |-> s` is not
being applied at a degenerate bin count. -/
theorem two_le_s {F : Stage1SlotBinding} (H : StageThreeHandoff F) : 2 ≤ F.s := by
  rw [H.s_eq]; exact H.scale.two_le_sVal

end StageThreeHandoff

/-- **The outer budget `K = a + log_2 q_2 + log_2 s`** (`07:632`,
`11-one-level-assembly.tex:12`), reader `K_0` (`03:94`).

Like `bCap` and `dTwo`, this is a function of three public integers alone: no
matrix, promise certificate or protocol enters its definition (`M9`). -/
def outerBudget (F : Stage1SlotBinding) (W : StageTwoWidths)
    (S : StageThreeScale) : ℕ :=
  F.a + W.r₂ + S.wS

@[simp] theorem outerBudget_eq (F : Stage1SlotBinding) (W : StageTwoWidths)
    (S : StageThreeScale) : outerBudget F W S = F.a + W.r₂ + S.wS := rfl

/-- **The `YES` local copy count, `eq:paper-B-yes`'s first clause.**
`q_1 + 2 = 2^a` (`07:615--616`, `11:336--338`, reader `03:566--567`): after
the two outer selectors are fixed, a legal source packing exposes the `q_1`
template copies and at most the two permitted source copies. -/
theorem yes_local_copies (F : Stage1SlotBinding) : F.q₁ + 2 = 2 ^ F.a := by
  have h : (2:ℕ) ^ 3 ≤ 2 ^ F.a := Nat.pow_le_pow_right (by norm_num) F.three_le_a
  norm_num at h
  simp only [Stage1SlotBinding.q₁]
  omega

/-- **The `NO` local copy count, `eq:paper-B-no-upper`'s first clause.**
`q_1 + s + 1 < 2^{a+1}` (`07:638--641`, `11:345--355`, reader `03:577--578`),
proved from the frozen `s <= A_* <= 2^a` carried by the handoff record.  The
frozen `07:641` writes the same fact as `q_1 + s + 1 <= 2^{a+1}`, which is
weaker and follows. -/
theorem no_local_copies {F : Stage1SlotBinding} (H : StageThreeHandoff F) :
    F.q₁ + F.s + 1 < 2 ^ (F.a + 1) ∧ F.q₁ + F.s + 1 ≤ 2 ^ (F.a + 1) := by
  have hq : F.q₁ + 2 = 2 ^ F.a := yes_local_copies F
  have hs : F.s ≤ 2 ^ F.a := H.s_le_two_pow_a
  have hs2 : 2 ≤ F.s := H.two_le_s
  have hpow : (2:ℕ) ^ (F.a + 1) = 2 ^ F.a + 2 ^ F.a := by rw [pow_succ]; ring
  constructor <;> omega

/-- **`exp:E-06-yes` / `eq:paper-B-yes`, the `YES` budget identity.**

`Y + a + log_2 q_2 + log_2 s = Y + K`: the two outer selectors (`log_2 s`
bins, then `log_2 q_2` source coordinates), the local copy index (`a` bits by
`yes_local_copies`), and the assumed `Y`-bit protocol for the seed.  General
in `Y`. -/
theorem yesBudget_eq (F : Stage1SlotBinding) (W : StageTwoWidths)
    (S : StageThreeScale) (Yb : ℕ) :
    Yb + F.a + W.r₂ + S.wS = Yb + outerBudget F W S := by
  simp only [outerBudget]
  omega

/-- **`exp:E-06-no-upper` / `eq:stage4-no-upper` / `eq:paper-B-no-upper`, the
`NO` budget identity.**

`D + (a + 1) + log_2 q_2 + log_2 s = D + K + 1 = C`: the same outer protocol,
with the local copy index costing one extra bit because
`no_local_copies` allows `q_1 + s + 1 < 2^{a+1}` seed coordinates.  General in
`D`. -/
theorem noBudget_eq (F : Stage1SlotBinding) (W : StageTwoWidths)
    (S : StageThreeScale) (Dsrc : ℕ) :
    Dsrc + (F.a + 1) + W.r₂ + S.wS = Dsrc + outerBudget F W S + 1 := by
  simp only [outerBudget]
  omega

/-- **The one-bit gap of the block title** (`07:609`, "The direct protocols
and the one-bit gap").

The `NO` budget exceeds the `YES` budget by exactly `(D - Y) + 1`; in
particular the gap is at least one bit for every seed with `Y <= D`, and it is
*exactly* one bit at the frozen `Y = D` boundary.  General in `Y` and `D`. -/
theorem promise_one_bit_gap (F : Stage1SlotBinding) (W : StageTwoWidths)
    (S : StageThreeScale) (Yb Dsrc : ℕ) (hYD : Yb ≤ Dsrc) :
    Yb + outerBudget F W S + ((Dsrc - Yb) + 1) = Dsrc + outerBudget F W S + 1 ∧
      Yb + outerBudget F W S < Dsrc + outerBudget F W S + 1 := by
  constructor <;> omega

/-! ### The Stage-1 local threshold and the odd-copy capacity inequality -/

/-- **`x_cap = 2^{a + 1 - b_0}`** (`07:611--614`), the Stage-1 local threshold
of the companion reduction. -/
noncomputable def xCap (F : Stage1SlotBinding) (b₀ : ℕ) : ℝ :=
  (2 : ℝ) ^ ((F.a : ℝ) + 1 - (b₀ : ℝ))

/-- **`eq:local-capacity-gap` (`07:617--622`), transcribed as a predicate and
never asserted.**

```
comp<R, q_1 + 3, x_cap, 9/25>  >=  D + a + 1.
```
The frozen sentence calls it "the literal inequality"; it is an inherited
odd-copy capacity bound, so it enters downstream statements as a named
hypothesis, exactly like the Stage-2 rung endpoints. -/
def localCapacityGap {X Y : Type*} [Fintype X] [Fintype Y]
    (F : Stage1SlotBinding) (R : X → Y → Bool) (b₀ Dsrc : ℕ) : Prop :=
  Dsrc + F.a + 1 ≤
    Dfamily (interlaceFun R (F.q₁ + 3))
      (bracketGE X Y (F.q₁ + 3) (xCap F b₀) (9 / 25))

/-- **Aux 11 (the two literal readings of `eq:local-capacity-gap`).**
`q_1 + 3 = 2^a + 1` (`07:623`) -- the *odd* copy count, one more than the even
`q_1 + 2 = 2^a` of the `YES` branch -- and `(1/2 + 1/10)^2 = 9/25`, the same
column density the Stage-3 bracket uses.  General in `F`. -/
theorem localCapacityGap_literals (F : Stage1SlotBinding) :
    F.q₁ + 3 = 2 ^ F.a + 1 ∧ Odd (F.q₁ + 3) ∧
      ((1 : ℝ) / 2 + 1 / 10) ^ 2 = 9 / 25 := by
  have hq : F.q₁ + 2 = 2 ^ F.a := yes_local_copies F
  refine ⟨by omega, ?_, columnThreshold.1⟩
  have hpar : Even F.q₁ := q₁_even F
  rcases hpar with ⟨k, hk⟩
  exact ⟨k + 1, by omega⟩

/-! ## §7  Statement poles, non-vacuity witnesses and consistency probes -/

/-- **Statement pole for `stageThreeExactScale`.**

At the legal constant source matrix the conclusion is *false*:
`comp(Int_s(f)) = 0` while `comp(f) + w_s = w_s >= 1`.  So the hypotheses are
genuine content and none can be dropped.  The clause that fails there is
`2 <= D_2`, since `comp(f) = 0`. -/
theorem exactScale_not_automatic (S : StageThreeScale) :
    D (interlaceFun (fun (_ : Bool) (_ : Bool) => false) S.sVal) = 0 ∧
      D (fun (_ : Bool) (_ : Bool) => false) = 0 ∧
      ¬ D (interlaceFun (fun (_ : Bool) (_ : Bool) => false) S.sVal) =
        D (fun (_ : Bool) (_ : Bool) => false) + S.wS := by
  have hconst :
      interlaceFun (fun (_ : Bool) (_ : Bool) => false) S.sVal =
        fun (_ : Fin S.sVal × Bool) (_ : Fin S.sVal → Bool) => false := rfl
  have h1 : D (interlaceFun (fun (_ : Bool) (_ : Bool) => false) S.sVal) = 0 := by
    rw [hconst]; exact PublicRecords.D_const false
  have h2 : D (fun (_ : Bool) (_ : Bool) => false) = 0 :=
    PublicRecords.D_const (X := Bool) (Y := Bool) false
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  have := S.one_le_wS
  omega

/-- **The Candidate-B discriminator, in the kernel.**  `NPCC.IsRobust` is
genuine mathematical content: it fails at the legal constant matrix, because
its clause R1 demands `1 <= comp(f)`.  Hence storing it as a structure field,
as Candidate B does, would put a robustness conclusion into constructor data
and would leave the record uninhabitable at the numeric schedule values.
General in the tolerance and the depth. -/
theorem constant_not_isRobust (δ b : ℝ) :
    ¬ IsRobust (fun (_ : Bool) (_ : Bool) => false) δ b := by
  intro h
  have h1 : 1 ≤ D (fun (_ : Bool) (_ : Bool) => false) := h.1
  rw [PublicRecords.D_const (X := Bool) (Y := Bool) false] at h1
  exact absurd h1 (by norm_num)

/-- **LANE-GATE 3 inhabitant: `StageThreeScale` at legal schedule values.**

`w_s = 6` and `b_2 = 40`.  `w_s = 6` is forced by the banked
`StageOneInterlace.stage1Legal`, whose `s = 64` is the least value meeting the
frozen bin gates `s >= 4` (`04-guarded-source.tex:281`), `s` a positive power
of two and `64 | s` (`05-public-records.tex:416--420`); `b_2 = 40` is the
banked `StageTwoRelaxed.depthTwoWitness`, a positive depth, and `6 <= 40`
supplies the frozen `w_s <= b_2`.

The inhabitant is **nondegenerate**: `s = 64 >= 2`, so this is not the
one-copy interlace, and `s /= 4`, so it is not the classical four-copy Stage 3
the frozen text explicitly replaces ("Stage 3 uses `s`, rather than four,
classical copies", `07:495`).

*Coverage limit, binding.*  No parameter schedule may be read out of this
witness; it inherits the coverage limits of `stage1Legal` and
`depthTwoWitness`. -/
def stageThreeScaleWitness : StageThreeScale where
  wS := 6
  b₂ := depthTwoWitness
  one_le_wS := by norm_num
  wS_le_b₂ := by norm_num [depthTwoWitness]

theorem stageThreeScaleWitness_nondegenerate :
    stageThreeScaleWitness.sVal = 64 ∧
      stageThreeScaleWitness.sVal = stage1Legal.s ∧
      2 ≤ stageThreeScaleWitness.sVal ∧
      stageThreeScaleWitness.sVal ≠ 4 ∧
      1 ≤ stageThreeScaleWitness.wS ∧
      stageThreeScaleWitness.wS ≤ stageThreeScaleWitness.b₂ ∧
      0 < stageThreeScaleWitness.b₂ := by
  refine ⟨rfl, rfl, by norm_num [StageThreeScale.sVal, stageThreeScaleWitness], ?_,
    by norm_num [stageThreeScaleWitness], by norm_num [stageThreeScaleWitness,
      depthTwoWitness], by norm_num [stageThreeScaleWitness, depthTwoWitness]⟩
  norm_num [StageThreeScale.sVal, stageThreeScaleWitness]

theorem stageThreeScale_inhabited : Nonempty StageThreeScale :=
  ⟨stageThreeScaleWitness⟩

/-- **LANE-GATE 3 inhabitant: `StageThreeHandoff` at the legal Stage-1
binding.**  `a = 7`, `s = 64 = 2^6 <= 2^7 = 128`. -/
def handoffWitness : StageThreeHandoff stage1Legal where
  scale := stageThreeScaleWitness
  s_eq := by norm_num [StageThreeScale.sVal, stageThreeScaleWitness, stage1Legal]
  s_le_two_pow_a := by norm_num [stage1Legal]

theorem handoffWitness_nondegenerate :
    stage1Legal.s = 64 ∧ stage1Legal.s ≤ 2 ^ stage1Legal.a ∧
      stage1Legal.s ≠ 2 ^ stage1Legal.a ∧ 2 ≤ stage1Legal.s := by
  refine ⟨rfl, by norm_num [stage1Legal], by norm_num [stage1Legal], by
    norm_num [stage1Legal]⟩

/-- **The frozen outer budget at the witnesses**, and both promise budgets in
closed form: `K = a + r_2 + w_s = 7 + 1026 + 6 = 1039`, the `YES` budget is
`Y + 1039`, and the `NO` budget is `D + 1040`.  The `bigWidths` record is the
banked Stage-2 width witness. -/
theorem budgets_at_witnesses (Yb Dsrc : ℕ) :
    outerBudget stage1Legal bigWidths stageThreeScaleWitness = 1039 ∧
      Yb + outerBudget stage1Legal bigWidths stageThreeScaleWitness = Yb + 1039 ∧
      Dsrc + outerBudget stage1Legal bigWidths stageThreeScaleWitness + 1 =
        Dsrc + 1040 := by
  have hK : outerBudget stage1Legal bigWidths stageThreeScaleWitness = 1039 := by
    norm_num [outerBudget, stage1Legal, bigWidths, stageThreeScaleWitness]
  refine ⟨hK, by omega, by omega⟩

/-- **LANE-GATE 3 inhabitant: `separationGates` at legal values.**

At `w_s = 6` (`s = 64`), `b_2 = 40` and any column carrier of size at least
`128`, both frozen gates of `eq:paper-M3-gates` hold, by
`separationGates_of_density` with `s 2^{1-b_2} = 2^{-33} <= 1/1024`.  The
carrier bound `2 s = 128 <= N_2` is the frozen `N_2 >= q_2^2 >= 2 s`
(`03:485--489`). -/
theorem separationGates_at_legal_values (N₂ : ℕ) (hN : 128 ≤ N₂) :
    separationGates stageThreeScaleWitness N₂ := by
  refine separationGates_of_density stageThreeScaleWitness N₂ ?_ ?_ (by omega)
  · have hs : (stageThreeScaleWitness.sVal : ℝ) = 64 := by
      norm_num [StageThreeScale.sVal, stageThreeScaleWitness]
    have hb : ((stageThreeScaleWitness.b₂ : ℕ) : ℝ) = 40 := by
      norm_num [stageThreeScaleWitness, depthTwoWitness]
    rw [hs, hb]
    have hstep : (2 : ℝ) ^ (1 - (40 : ℝ)) ≤ (2 : ℝ) ^ (-((16 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [two_rpow_neg_natCast 16] at hstep
    calc (64 : ℝ) * (2 : ℝ) ^ (1 - (40 : ℝ)) ≤ 64 * (1 / 2 ^ (16 : ℕ)) := by
          linarith
      _ ≤ 1 / 1024 := by norm_num
  · have hs : stageThreeScaleWitness.sVal = 64 := rfl
    omega

/-- **Consistency probe (HYPOTHESIS-CONSISTENCY RULE) for
`stageThreeExactScale`.**

The hypothesis bundle is *not* contradictory, and its shape is forced: given
the frozen `comp(f) = D_2`, the three-rung clause
`D_2 <= Lambda_3(f, 1, 2^{-b_2}, 3/5)` can only be an **equality**, because
`LambdaGE_le_D` bounds the three-rung quantity above by the ambient
complexity.  So the bundle demands exactly `Lambda_3 = D_2`, never more than
the frozen text, and no contradiction follows from conjoining it with
`2 <= D_2`.

The four hypotheses are also not two cases of a promise split: `07:437--448`
states them as the simultaneous output of the single `NO`-branch Stage-2
certificate `eq:stage2-two-depth-certificate`, so conjoining them is
legitimate.

*Coverage limit, binding.*  This does not exhibit a concrete matrix at which
the bundle holds; that is the Stage-2 endpoint obstruction recorded in
`StageTwoRelaxed`'s header, and `isRobust_iff_lambda` shows the bundle is
inhabited exactly when the vendored `IsRobust` premise is. -/
theorem exactScale_hypotheses_consistent {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (S : StageThreeScale) (d : ℕ)
    (hX : 1 ≤ Fintype.card X)
    (hexact : D f = d)
    (hlambda : d ≤ LambdaGE f 1 (xSeed S.b₂) (3 / 5)) :
    LambdaGE f 1 (xSeed S.b₂) (3 / 5) = d := by
  have hupper : LambdaGE f 1 (xSeed S.b₂) (3 / 5) ≤ D f :=
    LambdaGE_le_D f (xSeed_le_one S.b₂) (by norm_num) hX
  rw [hexact] at hupper
  exact Nat.le_antisymm hupper hlambda

/-- **The numeric shell of the Stage-3 block, simultaneously satisfied.**

The schedule integers, both separation gates, the outer budget and both
promise budgets are exhibited together at the legal witnesses, so no numeric
clause of the block is being satisfied by a degenerate reading. -/
theorem stageThreeBlock_numeric_shell_consistent (Yb Dsrc : ℕ) (hYD : Yb ≤ Dsrc) :
    separationGates stageThreeScaleWitness 128 ∧
      stage1Legal.q₁ + 2 = 2 ^ stage1Legal.a ∧
      stage1Legal.q₁ + stage1Legal.s + 1 < 2 ^ (stage1Legal.a + 1) ∧
      outerBudget stage1Legal bigWidths stageThreeScaleWitness = 1039 ∧
      Yb + 1039 < Dsrc + 1039 + 1 := by
  refine ⟨separationGates_at_legal_values 128 (le_refl 128), yes_local_copies _,
    (no_local_copies handoffWitness).1, (budgets_at_witnesses Yb Dsrc).1, ?_⟩
  omega

end EthInapproximability.ParameterizedNP.StageThreeExactScale
