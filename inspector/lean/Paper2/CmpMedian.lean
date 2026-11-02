import Paper2.CmpSpecProof

/-!
# WP-U18a (ii), segment M2 closed: `CmpSpec` for the physical comparator; the median algorithm
with no comparator premise

Lane `owner:a-cmp-1` (private, 27 September 2026). Paper A, lock v12, I:73-76, I:117-125.
Decisions: D-A1, D-A3 (ii) (lane a-model's `PrefixAlgorithm` and codec, frozen predecessor).

`cmpSpec_holds A : CmpSpec A machine thrW (cmpTC A)` for EVERY prefix-model algorithm `A`, with the
explicit clock `cmpTC A w = cmpTime |w| (outBound A.machine |w| R(|w|) (A.time w))`; the premise
`hC` of lane a-median's `medAlg*` is discharged, and `hT` (polynomial comparator clock) is proved
from `A.Polynomial` (`cmpTC_poly`).
-/

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Paper2.CmpOwner

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.EncodedCommunication (field readField bitsValue natField)
open EthInapproximability.CurrentPaper.EncodedComplexity (pair)
open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.Unit4Shell.Amplification (reps)
open Paper2.MedianOwner Paper2.MedianOwner.Med Paper2.MedianOwner.Final
open Paper2.AModel (PrefixAlgorithm)

theorem cmpTime_mono {wl wl' ol ol' : ℕ} (h1 : wl ≤ wl') (h2 : ol ≤ ol') :
    cmpTime wl ol ≤ cmpTime wl' ol' := by
  unfold cmpTime outTime
  have := Nat.mul_le_mul (Nat.add_le_add_right h2 2)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h2) 3)
  omega

theorem cmpTime_quad (X K : ℕ) (hX : 1 ≤ X) :
    cmpTime X (K * X) ≤ (2 * K * K + 13 * K + 23) * (X * X) := by
  unfold cmpTime outTime
  have h1 : X ≤ X * X := Nat.le_mul_of_pos_left X hX
  have h2 : K * X ≤ K * (X * X) := Nat.mul_le_mul_left K h1
  have h3 : 1 ≤ X * X := by nlinarith
  nlinarith [h1, h2, h3]

/-- The comparator clock handed to the median machine. -/
def cmpTC (A : PrefixAlgorithm) (w : List Bool) : ℕ :=
  cmpTime w.length (outBound A.machine w.length (A.tapeLength w.length) (A.time w))

open Classical in
/-- **`CmpSpec` holds for the physical comparator**, for every prefix-model algorithm `A`. -/
theorem cmpSpec_holds (A : PrefixAlgorithm) : CmpSpec A machine thrW (cmpTC A) := by
  intro w out hout
  have h := cmp_outputs w out
  have hb : spec w out = decide (Below Paper2.AModel.decodeDyadic (thrW w) out) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact spec_iff w out
  rw [hb] at h
  exact outputsWithin_mono machine h (cmpTime_mono le_rfl hout)

/-- The comparator clock is polynomial whenever `A` is (the `hT` premise of `medAlg_polynomial`). -/
theorem cmpTC_poly (A : PrefixAlgorithm) (hA : A.Polynomial) :
    ∃ cT dT : ℕ, ∀ w : List Bool, cmpTC A w ≤ cT * (w.length + 1) ^ dT := by
  obtain ⟨c, d, hA⟩ := hA
  set p := A.machine.pushBound
  set K := 3 + c + c * p with hK
  refine ⟨2 * K * K + 13 * K + 23, 2 * (d + 1), fun w => ?_⟩
  set N := w.length + 1 with hN
  set X := N ^ (d + 1) with hXdef
  have hN1 : 1 ≤ N := by omega
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ hN1
  have hNX : N ≤ X := by
    rw [hXdef]; exact Nat.le_self_pow (by omega) N
  have hdX : N ^ d ≤ X := by rw [hXdef]; exact Nat.pow_le_pow_right hN1 (by omega)
  obtain ⟨hs, ht⟩ := hA w
  have hs' : A.tapeLength w.length ≤ c * X := hs.trans (Nat.mul_le_mul_left c hdX)
  have ht' : A.time w ≤ c * X := ht.trans (Nat.mul_le_mul_left c hdX)
  have hwl : w.length ≤ X := by omega
  have hout : outBound A.machine w.length (A.tapeLength w.length) (A.time w) ≤ K * X := by
    unfold outBound
    have htp : A.time w * A.machine.pushBound ≤ c * X * p := Nat.mul_le_mul_right _ ht'
    have hcxp : c * X * p = c * p * X := by ring
    rw [hK]
    nlinarith
  have hq := cmpTime_quad X K hX1
  have hXX : X * X = N ^ (2 * (d + 1)) := by rw [hXdef, ← pow_add]; ring_nf
  calc cmpTC A w ≤ cmpTime X (K * X) := cmpTime_mono hwl hout
    _ ≤ (2 * K * K + 13 * K + 23) * (X * X) := hq
    _ = (2 * K * K + 13 * K + 23) * N ^ (2 * (d + 1)) := by rw [hXX]

/-! ## The median algorithm with the physical comparator (no `CmpSpec` premise) -/

/-- Lane a-median's repeat-and-median algorithm over `A`, with this lane's comparator. -/
noncomputable def medAlgC (A : PrefixAlgorithm) : PrefixAlgorithm :=
  medAlg A machine thrW (cmpTC A) (cmpSpec_holds A)

theorem medAlgC_machine (A : PrefixAlgorithm) :
    (medAlgC A).machine = medMachine 146 A.machine machine := rfl

theorem medAlgC_prob (A : PrefixAlgorithm) (w : List Bool) :
    (medAlgC A).prob w (· = [true]) =
      (uniformTape (reps * A.tapeLength w.length)).prob (fun t =>
        MajBelow Paper2.AModel.decodeDyadic
          (fun i => A.output w (List.ofFn (seg reps (A.tapeLength w.length) t i))) (thrW w)) :=
  medAlg_prob A machine thrW (cmpTC A) (cmpSpec_holds A) w

theorem medAlgC_yes (A : PrefixAlgorithm) (w : List Bool) (c : ℕ) (a : ℝ) (B k : ℕ)
    (hk : 2 * a < k) (hthr : thrW w = (B : ℝ) + (k : ℝ) / 2)
    (hE : 2 / 3 ≤ A.prob w (fun out => ∃ v, Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a))
    (hcB : c ≤ B) : 99 / 100 ≤ (medAlgC A).prob w (· = [true]) :=
  medAlg_yes A machine thrW (cmpTC A) (cmpSpec_holds A) w c a B k hk hthr hE hcB

theorem medAlgC_no (A : PrefixAlgorithm) (w : List Bool) (c : ℕ) (a : ℝ) (B k : ℕ)
    (hk : 2 * a < k) (hthr : thrW w = (B : ℝ) + (k : ℝ) / 2)
    (hE : 2 / 3 ≤ A.prob w (fun out => ∃ v, Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a))
    (hBc : B + k ≤ c) : (medAlgC A).prob w (· = [true]) ≤ 1 / 100 :=
  medAlg_no A machine thrW (cmpTC A) (cmpSpec_holds A) w c a B k hk hthr hE hBc

/-- YES side on a word that carries `2B + k` as its leading field. -/
theorem medAlgC_yes_natField (A : PrefixAlgorithm) (rest : List Bool) (c : ℕ) (a : ℝ) (B k : ℕ)
    (hk : 2 * a < k)
    (hE : 2 / 3 ≤ A.prob (natField (2 * B + k) ++ rest)
      (fun out => ∃ v, Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a))
    (hcB : c ≤ B) : 99 / 100 ≤ (medAlgC A).prob (natField (2 * B + k) ++ rest) (· = [true]) :=
  medAlgC_yes A _ c a B k hk (thrW_midpoint B k rest) hE hcB

/-- NO side on a word that carries `2B + k` as its leading field. -/
theorem medAlgC_no_natField (A : PrefixAlgorithm) (rest : List Bool) (c : ℕ) (a : ℝ) (B k : ℕ)
    (hk : 2 * a < k)
    (hE : 2 / 3 ≤ A.prob (natField (2 * B + k) ++ rest)
      (fun out => ∃ v, Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a))
    (hBc : B + k ≤ c) : (medAlgC A).prob (natField (2 * B + k) ++ rest) (· = [true]) ≤ 1 / 100 :=
  medAlgC_no A _ c a B k hk (thrW_midpoint B k rest) hE hBc

theorem medAlgC_polynomial (A : PrefixAlgorithm) (hA : A.Polynomial) : (medAlgC A).Polynomial :=
  medAlg_polynomial A machine thrW (cmpTC A) (cmpSpec_holds A) hA (cmpTC_poly A hA)

end Paper2.CmpOwner
