import EthInapproximability.CurrentPaper.EntryClockPolyTable
import EthInapproximability.CurrentPaper.EntryPrepFinal4
import EthInapproximability.CurrentPaper.EntryPrepPoly

/-!
# Segment 1d: the level-0 instance and its size in the naming bound `p`

Lane owner:b-entry-clock-2 (Paper B, unit 2, CP-EFFECTIVE). Pure arithmetic; no machine.

* `inst0 G n c`: the instance of owner-1's `Inst` at the level-0 data
  (`R := (M0 n).entry`, `family := Iteration.secondFamily ..`,
  `order := GraphVectors.itemOrder ..`, `vectors := GraphVectors.vectors ..`,
  `cap := GraphVectors.supportCap ..`), with EXACTLY the arguments of the admitted
  `EntryTailClear.tailBound`.
* `tailBound_eq`: `EntryTailClear.tailBound G n c` is (definitionally) owner-1's
  `writer_poly` body at `inst0 G n c`.
* `U_inst0_le`: under the naming premise
  `EffectiveIteration.oneLevelBound (P0 G n c) ≤ p` (the admitted one-level bound of the
  level-0 step parameters; the admitted `EffectiveIteration.oneLevelBound_fits` gives
  `2 k * oneLevelBound < n`, i.e. the premise at the manuscript's `p = ⌈n/(2k)⌉`),
  `(inst0 G n c).U ≤ 3 * 2^p + 2 * p + 4 * p^2 + 4 * p * |V|`.

The firstLength component is bounded DIRECTLY in `p` by the admitted
`EffectiveIteration.parameter_size_bounds` (`firstLength ≤ balanceOrder`), so owner-1's
`cy = 1` caveat does not arise: no `cy ≥ 2` premise is needed.
-/

namespace EthInapproximability.CurrentPaper.EntryClockPoly

open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization
open EthInapproximability.ParameterizedNP.GuardedSourceGraph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The level-0 step parameters (the admitted `Iteration.stepParameters` at level 0). -/
abbrev P0 (G : EndpointGraph V E) (n c : ℕ) : Parameters.Input :=
  Iteration.stepParameters G c (EntryTailClear.b0 n) (EntryTailClear.y0 n) 0 (EntryTailClear.M0 n)

/-- The level-0 instance: exactly the arguments of `EntryTailClear.tailBound`. -/
noncomputable def inst0 (G : EndpointGraph V E) (n c : ℕ) : Inst where
  a := Iteration.a G c (EntryTailClear.b0 n) (EntryTailClear.y0 n) 0 (EntryTailClear.M0 n)
  s := Iteration.s G c (EntryTailClear.b0 n) (EntryTailClear.y0 n) 0 (EntryTailClear.M0 n)
  q := Iteration.q₂ G c (EntryTailClear.b0 n) (EntryTailClear.y0 n) 0 (EntryTailClear.M0 n)
  L := Iteration.labels G c (EntryTailClear.b0 n) (EntryTailClear.y0 n) 0 (EntryTailClear.M0 n)
  nv := GraphVectors.vertexCount V
    (Iteration.s G c (EntryTailClear.b0 n) (EntryTailClear.y0 n) 0 (EntryTailClear.M0 n))
  nb := GraphVectors.auxiliaryCount
    (Iteration.s G c (EntryTailClear.b0 n) (EntryTailClear.y0 n) 0 (EntryTailClear.M0 n))
  rx := (EntryTailClear.M0 n).rows
  cy := (EntryTailClear.M0 n).columns
  R := (EntryTailClear.M0 n).entry
  hs := lt_of_lt_of_le (by decide : 0 < 4)
    (Iteration.bins_ge_four G c (EntryTailClear.b0 n) (EntryTailClear.y0 n) 0 (EntryTailClear.M0 n))
  family := Iteration.secondFamily G c (EntryTailClear.b0 n) (EntryTailClear.y0 n) 0
    (EntryTailClear.M0 n)
  order := GraphVectors.itemOrder G
    (Iteration.s G c (EntryTailClear.b0 n) (EntryTailClear.y0 n) 0 (EntryTailClear.M0 n))
  vectors := GraphVectors.vectors G
    (Iteration.s G c (EntryTailClear.b0 n) (EntryTailClear.y0 n) 0 (EntryTailClear.M0 n))
  cap := GraphVectors.supportCap G (le_trans (by decide : 3 ≤ 4)
    (Iteration.bins_ge_four G c (EntryTailClear.b0 n) (EntryTailClear.y0 n) 0 (EntryTailClear.M0 n)))

/-- The admitted tail clock IS owner-1's writer clock at the level-0 instance. -/
theorem tailBound_eq (G : EndpointGraph V E) (n c : ℕ) :
    EntryTailClear.tailBound G n c =
      MatrixTableWriter.writerBound
          (rows (inst0 G n c).s (inst0 G n c).L (inst0 G n c).nv (inst0 G n c).nb (inst0 G n c).rx)
          (cols (inst0 G n c).a (inst0 G n c).s (inst0 G n c).q (inst0 G n c).cy)
          (EntryRunsRaw.tableT (inst0 G n c).R (inst0 G n c).hs (inst0 G n c).family
            (inst0 G n c).order (inst0 G n c).vectors (inst0 G n c).cap) +
        (2 * (rows (inst0 G n c).s (inst0 G n c).L (inst0 G n c).nv (inst0 G n c).nb
          (inst0 G n c).rx * cols (inst0 G n c).a (inst0 G n c).s (inst0 G n c).q
            (inst0 G n c).cy) + 2) + 1 := by
  unfold EntryTailClear.tailBound
  dsimp only [inst0]

/-! ## The level-0 scalars are the admitted parameter formulas -/

theorem inst0_s (G : EndpointGraph V E) (n c : ℕ) :
    (inst0 G n c).s = Parameters.bins (P0 G n c) := rfl
theorem inst0_q (G : EndpointGraph V E) (n c : ℕ) :
    (inst0 G n c).q = Parameters.secondWidth (P0 G n c) := rfl
theorem inst0_L (G : EndpointGraph V E) (n c : ℕ) :
    (inst0 G n c).L = EffectiveIteration.familySize (P0 G n c) := rfl
theorem inst0_rx (G : EndpointGraph V E) (n c : ℕ) :
    (inst0 G n c).rx = (P0 G n c).rows := rfl
theorem inst0_cy (G : EndpointGraph V E) (n c : ℕ) :
    (inst0 G n c).cy = (P0 G n c).columns := rfl
theorem inst0_fl (G : EndpointGraph V E) (n c : ℕ) :
    firstLength (inst0 G n c).a (inst0 G n c).s = Parameters.firstLength (P0 G n c) := by
  show qOne (Parameters.firstExponent (P0 G n c)) + (Parameters.bins (P0 G n c) + 1) =
    Parameters.firstWidth (P0 G n c) + Parameters.bins (P0 G n c) + 1
  unfold qOne Parameters.firstWidth
  omega

/-- The raw column count is one factor of the admitted protected column count. -/
theorem cols_le_protected (G : EndpointGraph V E) (n c : ℕ) :
    cols (inst0 G n c).a (inst0 G n c).s (inst0 G n c).q (inst0 G n c).cy ≤
      EffectiveIteration.protectedColumnCount (P0 G n c) := by
  have hfl := inst0_fl G n c
  unfold cols
  rw [hfl, inst0_q, inst0_cy, inst0_s]
  unfold EffectiveIteration.protectedColumnCount
  dsimp only
  generalize hU : Parameters.secondWidth (P0 G n c) * (P0 G n c).columns ^
    Parameters.firstLength (P0 G n c) = U
  have hq : 0 < Parameters.secondWidth (P0 G n c) := Parameters.secondWidth_pos _
  have hc : 0 < (P0 G n c).columns := (EntryTailClear.M0 n).columns_pos
  have hU1 : 1 ≤ U := by
    rw [← hU]; exact Nat.mul_pos hq (Nat.pow_pos hc)
  have hUs : 1 ≤ U ^ Parameters.bins (P0 G n c) := Nat.one_le_pow _ _ hU1
  generalize (P0 G n c).columns ^ (Parameters.bins (P0 G n c) + 1) *
    U ^ Parameters.bins (P0 G n c) = X
  calc X ≤ 184 * X := by omega
    _ ≤ 184 * X * U := Nat.le_mul_of_pos_right _ hU1
    _ ≤ 184 * X * U * U ^ Parameters.bins (P0 G n c) := Nat.le_mul_of_pos_right _ hUs

/-! ## Segment 1d: the level-0 size in the naming bound -/

/-- `oneLevelBound = 128 * balanceOrder^4` (admitted `nextScale_identity`). -/
theorem oneLevel_eq (G : EndpointGraph V E) (n c : ℕ) :
    EffectiveIteration.oneLevelBound (P0 G n c) = 128 * Parameters.balanceOrder (P0 G n c) ^ 4 := by
  rw [EffectiveIteration.oneLevelBound, EffectiveIteration.nextScale_identity]

theorem U_inst0_le (G : EndpointGraph V E) (n c p : ℕ)
    (hname : EffectiveIteration.oneLevelBound (P0 G n c) ≤ p) :
    (inst0 G n c).U ≤ 3 * 2 ^ p + 2 * p + 4 * p ^ 2 + 4 * p * Fintype.card V := by
  rw [oneLevel_eq] at hname
  obtain ⟨h128, _, _, hs, hfl, _⟩ := EffectiveIteration.parameter_size_bounds (P0 G n c)
  generalize hT : Parameters.balanceOrder (P0 G n c) = T at hname h128 hs hfl
  have hT1 : 1 ≤ T := by omega
  have hT2 : T ^ 2 ≤ T ^ 3 := Nat.pow_le_pow_right hT1 (by decide)
  have hT3 : T ^ 3 ≤ T ^ 4 := Nat.pow_le_pow_right hT1 (by decide)
  have hT14 : T ≤ T ^ 4 := by
    calc T = T ^ 1 := (pow_one T).symm
      _ ≤ T ^ 4 := Nat.pow_le_pow_right hT1 (by decide)
  have hTp : T ≤ p := by omega
  have h3p : 16 * T ^ 3 ≤ p := by omega
  have h2p : 16 * T ^ 2 ≤ p := by omega
  have hpp : p ≤ 2 ^ p := Nat.le_of_lt Nat.lt_two_pow_self
  -- the five components
  have hcols : cols (inst0 G n c).a (inst0 G n c).s (inst0 G n c).q (inst0 G n c).cy ≤ 2 ^ p := by
    have h := (cols_le_protected G n c).trans (EffectiveIteration.protectedColumnCount_bound _)
    rw [hT] at h
    exact h.trans (Nat.pow_le_pow_right (by decide) h3p)
  have hsv : (inst0 G n c).s ≤ p := by rw [inst0_s]; omega
  have hL : (inst0 G n c).L ≤ 2 ^ p := by
    have h := EffectiveIteration.familySize_bound (P0 G n c)
    rw [hT] at h
    rw [inst0_L]
    exact h.trans (Nat.pow_le_pow_right (by decide) h2p)
  have hrx : (inst0 G n c).rx ≤ 2 ^ p := by
    have h := (EffectiveIteration.input_cardinality_bounds (P0 G n c)).1
    rw [hT] at h
    rw [inst0_rx]
    exact h.trans (Nat.pow_le_pow_right (by decide) hTp)
  have hflv : firstLength (inst0 G n c).a (inst0 G n c).s ≤ p := by rw [inst0_fl]; omega
  have hitems : (inst0 G n c).nv + (inst0 G n c).nb ≤ 4 * p * Fintype.card V + 4 * p ^ 2 := by
    show 4 * (inst0 G n c).s * Fintype.card V + 4 * (inst0 G n c).s * ((inst0 G n c).s - 3) ≤ _
    have e1 : 4 * (inst0 G n c).s * Fintype.card V ≤ 4 * p * Fintype.card V :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsv)
    have e2 : 4 * (inst0 G n c).s * ((inst0 G n c).s - 3) ≤ 4 * p * p :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hsv) ((Nat.sub_le _ _).trans hsv)
    have e3 : 4 * p * p = 4 * p ^ 2 := by ring
    omega
  unfold Inst.U
  omega

#print axioms tailBound_eq
#print axioms inst0_fl
#print axioms cols_le_protected
#print axioms U_inst0_le

end EthInapproximability.CurrentPaper.EntryClockPoly
