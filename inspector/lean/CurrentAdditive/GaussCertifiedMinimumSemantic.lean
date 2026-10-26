import CurrentAdditive.GaussActualCertifiedSource
import CurrentAdditive.MinimumRatioFoldSemanticJoin
import CurrentAdditive.SequentialElimination

/-! Positive minimum-ratio existence for the exact certificate physically
written by the post-Gauss program. The ratio fold here remains semantic;
its indexed physical controller is a separate obligation. -/

namespace CurrentAdditive.GaussCertifiedMinimumSemantic

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.GaussFirstFreeCandidate
open CurrentAdditive.GaussCertificateVectorABI

theorem actual_certificate_positive_minimum
    (a : Array (Array ℚ))
    (A : Matrix (Fin a.size) (Fin (SequentialCode.columnCount a)) ℤ)
    (weights : Array ℚ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hwide : a.size < SequentialCode.columnCount a)
    (hA : ∀ i j, (A i j : ℚ) = SequentialArrayBridge.matrixOfArray a i j)
    (hsize : weights.size = SequentialCode.columnCount a)
    (hpositive : ∀ i < weights.size, 0 < weights[i]?.getD 0)
    (hrow : ∃ i < a.size,
      ∀ j < SequentialCode.columnCount a, SequentialCode.cell a i j = 1) :
    let k := SequentialCode.columnCount a
    let Aq : Fin a.size → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := GaussControlTrace.after Aq k
    let S := GaussStateMatrixContext.inputBank (GaussControlTrace.statePacket s) k
    ∃ (f : Fin k) (hf : f.val ≤ a.size) (t : Nat)
      (T : GaussWideVectorInvoke.OldBank → List Bool) (lambda : ℚ),
      t ≤ GaussActualVectorFused.totalClock s f ∧
      SequentialCode.IsDependence a
        (Array.ofFn (directCandidate s.B f hf)) ∧
      SequentialCode.minimumRatio weights
        (Array.ofFn (directCandidate s.B f hf)) = some lambda ∧
      MinimumRatioFoldSemanticJoin.semanticFold
        (MinimumRatioFoldSemanticJoin.pairs weights
          (Array.ofFn (directCandidate s.B f hf))) = some lambda ∧
      0 < lambda ∧
      ((advance GaussWideVectorInvoke.program)^[t])
        (⟨some GaussWideVectorInvoke.start, GaussWideVectorInvoke.control,
          GaussWideVectorInvoke.wide S⟩ :
          TM2.Cfg (fun _ : GaussWideVectorInvoke.Bank => Bool) _ _) =
        ⟨none, GaussWideVectorInvoke.control,
          Function.update (GaussWideVectorInvoke.wide T)
            GaussWideVectorInvoke.slots.target
            (vectorPacket (Array.ofFn (directCandidate s.B f hf)))⟩ := by
  let k := SequentialCode.columnCount a
  let Aq : Fin a.size → Fin k → ℚ := fun i j => (A i j : ℚ)
  let s := GaussControlTrace.after Aq k
  obtain ⟨f, hf, t, T, ht, hcheck, hr⟩ :=
    GaussActualCertifiedSource.actual_vector_passes_check
      a A h01 hwide hA
  let coeff := Array.ofFn (directCandidate s.B f hf)
  have hdep : SequentialCode.IsDependence a coeff := hcheck
  obtain ⟨hcoeffsize, hnonzero, _⟩ :=
    (SequentialCode.dependence_spec a coeff).mp hdep
  have hsum : coeff.toList.sum = 0 :=
    SequentialElimination.zero_sum_of_constant_row a coeff hdep hrow
  obtain ⟨lambda, hmin, hpos, _, _⟩ :=
    SequentialElimination.minimumRatio_total weights coeff
      (hsize.trans hcoeffsize.symm) hpositive hsum hnonzero
  refine ⟨f, hf, t, T, lambda, ht, hdep, hmin, ?_, hpos, hr⟩
  rw [MinimumRatioFoldSemanticJoin.semanticFold_eq_minimumRatio]
  exact hmin

#print axioms actual_certificate_positive_minimum

end CurrentAdditive.GaussCertifiedMinimumSemantic
