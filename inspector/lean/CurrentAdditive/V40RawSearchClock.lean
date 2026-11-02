import CurrentAdditive.V40RawFirstPassingSearch

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CurrentAdditive.V40RawFirstPassingSearch

open EthInapproximability.CurrentPaper V39GeneratedConstruction
open V40ActualPreparedSearch

noncomputable section

theorem batchCap_polynomial : ∃ C : Nat, ∀ floor n m,
    batchCap floor n m ≤ C * ((V40SearchInitialization.input floor n m).length + 1) ^ 2 := by
  obtain ⟨Cs, hCs⟩ := V40SearchInitialization.start_clock_polynomial
  refine ⟨Cs + 70, ?_⟩
  intro floor n m
  let Z := (V40SearchInitialization.input floor n m).length + 1
  have hZ : 1 ≤ Z := by dsimp [Z]; omega
  have hZ2 : Z ≤ Z ^ 2 := by nlinarith only [hZ]
  have hnm : n + m ≤ Z := by simp only [Z, V40SearchInitialization.input_length]; omega
  have hfn : floor + n ≤ Z := by simp only [Z, V40SearchInitialization.input_length]; omega
  have hstart : V40DeterministicBoundedSearch.start floor n ≤ Z :=
    (V40SearchInitialization.startExpr.eval_le_peak floor n).trans
      ((V40SearchInitialization.start_peak floor n).trans hfn)
  have hs := hCs floor n m
  change V40SearchInitialization.expressionClock V40SearchInitialization.startExpr floor n m ≤ Cs * Z ^ 2 at hs
  simp [batchCap, V40RawSearchEngine.batchCap, V22ParameterBatch.clockPrefix,
    V40RawSearchEngine.results, V40RawSearchEngine.times]
  change _ ≤ (Cs + 70) * Z ^ 2
  dsimp only [Z] at hZ2 hnm hstart hs ⊢
  nlinarith only [hs, hZ2, hnm, hstart]

theorem clock_polynomial (p : SourceConstants) : ∃ C e : Nat, ∀ floor n m, 0 < n →
    clock p floor n m ≤ C * ((V40SearchInitialization.input floor n m).length + 1) ^ e := by
  obtain ⟨Ci, hCi⟩ := batchCap_polynomial
  obtain ⟨Cl, el, hCl⟩ := loopCap_polynomial p
  refine ⟨Ci + Cl + 1, el + 2, ?_⟩
  intro floor n m hn
  let Z := (V40SearchInitialization.input floor n m).length + 1
  have hZ : 1 ≤ Z := by dsimp [Z]; omega
  have hi := hCi floor n m
  have hl := hCl floor n m hn
  have hi' : Z ^ 2 ≤ Z ^ (el + 2) := Nat.pow_le_pow_right hZ (by omega)
  have hl' : Z ^ el ≤ Z ^ (el + 2) := Nat.pow_le_pow_right hZ (by omega)
  have h1 : 1 ≤ Z ^ (el + 2) := Nat.one_le_pow _ _ hZ
  have hia := Nat.mul_le_mul_left Ci hi'
  have hla := Nat.mul_le_mul_left Cl hl'
  change _ ≤ (Ci + Cl + 1) * Z ^ (el + 2)
  dsimp only [Z] at hi' hl' h1 hia hla ⊢
  unfold clock
  nlinarith only [hi, hl, hia, hla, h1]

/-- One fixed machine computes the exact canonical first passing schedule
from original formula size and literal graph counts. Constants precede all
inputs. Every attempted candidate is paid, including rejected candidates. -/
theorem outputs_polynomial (p : SourceConstants) :
    ∃ C e : Nat, ∀ floor n m (hn : 0 < n) (hlow : n ≤ 2 * m)
      (hdegree : 2 * m ≤ p.degree * n),
      (machine p).OutputsWithin (V40SearchInitialization.input floor n m)
        (List.replicate (publicLogFrom p floor n m hn hlow hdegree) true)
        (C * ((V40SearchInitialization.input floor n m).length + 1) ^ e) := by
  obtain ⟨C, e, h⟩ := clock_polynomial p
  exact ⟨C, e, fun floor n m hn hlow hdegree => BitMachine.outputsWithin_mono _
    (raw_outputs p floor n m hn hlow hdegree) (h floor n m hn)⟩

end
end CurrentAdditive.V40RawFirstPassingSearch
