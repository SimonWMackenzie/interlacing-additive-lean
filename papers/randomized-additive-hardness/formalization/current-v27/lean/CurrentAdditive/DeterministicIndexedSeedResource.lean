import CurrentAdditive.IndexedActualConstruction
/-! The concrete indexed lookup seed fits a fixed public resource exponent.
This closes only the base clause of ResourceContract. The successor's full
encoding size and physical step clock still require a Code_D producer. -/

namespace CurrentAdditive.DeterministicIndexedSeedResource

open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicETHSeedStage
open CurrentAdditive.IndexedExecutableStepRecovery
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.DeterministicIteration
open Paper2.LookupSeed

set_option maxHeartbeats 1000000

theorem indexed_seed_envelope_le (L : ℕ) (hL : 2004 ≤ L) :
    N L + (indexedSeedStage L).encodingSize + 2 ≤ (N L)^133 := by
  let n := N L
  let W := width L
  have hn : 4 ≤ n := N_ge_four L (by omega)
  have hWlt : W < 128*(L+1) := width_lt L
  have hWexp : W ≤ 129*L := by omega
  have hLplus : L+1 ≤ s L := L_plus_one_le_s L (by omega)
  have h129 : 129*s L ≤ n := coefficient_mul_s_le_N 129 L (by omega)
  have hWn : W ≤ n := by
    have hh := Nat.mul_le_mul_left 129 hLplus
    omega
  have hpow : 2^W ≤ n^129 := by
    calc
      2^W ≤ 2^(129*L) := Nat.pow_le_pow_right (by decide) hWexp
      _ = n^129 := by
        dsimp [n, N]
        rw [← pow_mul]
        congr 1
        omega
  have hfactor : 2*W+4 ≤ 3*n := by omega
  have hfirst : 2^W*(2*W+4) ≤ 3*n^130 := by
    calc
      2^W*(2*W+4) ≤ n^129*(3*n) := Nat.mul_le_mul hpow hfactor
      _ = 3*n^130 := by rw [pow_succ]; ring
  have hsecond : W*(W+2) ≤ 2*n^2 := by nlinarith
  have hp2 : n^2 ≤ n^130 := Nat.pow_le_pow_right (by omega : 1 ≤ n) (by omega)
  have hp1 : n ≤ n^130 := by
    calc
      n ≤ n^2 := by nlinarith
      _ ≤ n^130 := hp2
  have hp0 : 1 ≤ n^130 := Nat.one_le_pow _ _ (by omega : 1 ≤ n)
  have hsmall : 2*n+4 ≤ n^130 := by
    have hh : 2*n+4 ≤ n^2 := by nlinarith
    exact hh.trans hp2
  have hsum : n + seedEncodingBudget L + 2 ≤ 8*n^130 := by
    change n + (2^W*(2*W+4)+W*(W+2)+n+2)+2 ≤ 8*n^130
    omega
  have hn3 : 8 ≤ n^3 := by nlinarith
  have hlast : 8*n^130 ≤ n^133 := by
    have hh := Nat.mul_le_mul_right (n^130) hn3
    calc
      8*n^130 ≤ n^3*n^130 := hh
      _ = n^133 := by rw [show 133 = 3+130 by omega, pow_add]
  simpa only [indexedSeedStage, n] using hsum.trans hlast

theorem indexed_actual_resource_base
    (v e L : ℕ) [NeZero v] [NeZero (s L)] [NeZero (s L-3)]
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L),
      StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : IndexedSemanticIteration.Graph (Fin v) (Fin e))
    (C₁ : ℕ) (hC₁ : 133 ≤ C₁) :
    envelope (indexedActualConstruction v e L T inputs) (N L)
      ((indexedActualConstruction v e L T inputs).seed G) ≤
      (N L)^C₁ := by
  have hbase := indexed_seed_envelope_le L T.large
  have hpow := Nat.pow_le_pow_right (N_pos L) hC₁
  change N L + (indexedSeedStage L).encodingSize + 2 ≤ (N L)^C₁
  exact hbase.trans hpow

#print axioms indexed_seed_envelope_le
#print axioms indexed_actual_resource_base

end CurrentAdditive.DeterministicIndexedSeedResource
