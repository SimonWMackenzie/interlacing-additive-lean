import CurrentAdditive.GaussCertifiedMinimumSemantic
import CurrentAdditive.CodeDUpdateFullPipeline

/-! The checked physical certificate and checked update/compactor can be
stated together once the canonical request packet is provided. The missing
physical ratio fold and request producer are not supplied by this theorem. -/

namespace CurrentAdditive.GaussCertifiedUpdateStages

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.GaussFirstFreeCandidate
open CurrentAdditive.GaussCertificateVectorABI

theorem actual_certified_update_stages {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (a : Array (Array ℚ))
    (A : Matrix (Fin a.size) (Fin (SequentialCode.columnCount a)) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hwide : a.size < SequentialCode.columnCount a)
    (hA : ∀ i j, (A i j : ℚ) = SequentialArrayBridge.matrixOfArray a i j)
    (hsize : (source.map Prod.snd).size = SequentialCode.columnCount a)
    (hpositive : ∀ i < (source.map Prod.snd).size,
      0 < (source.map Prod.snd)[i]?.getD 0)
    (hrow : ∃ i < a.size,
      ∀ j < SequentialCode.columnCount a, SequentialCode.cell a i j = 1) :
    let k := SequentialCode.columnCount a
    let Aq : Fin a.size → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := GaussControlTrace.after Aq k
    let S := GaussStateMatrixContext.inputBank (GaussControlTrace.statePacket s) k
    ∃ (f : Fin k) (hf : f.val ≤ a.size) (t : Nat)
      (T : GaussWideVectorInvoke.OldBank → List Bool) (lambda : ℚ),
      let coeff := Array.ofFn (directCandidate s.B f hf)
      let candidate := CurrentAdditive.CodeDUpdatedArithmeticABI.candidateWeights
        source coeff lambda
      t ≤ GaussActualVectorFused.totalClock s f ∧
      0 < lambda ∧
      SequentialCode.minimumRatio (source.map Prod.snd) coeff = some lambda ∧
      candidate.all (fun w => decide (0 ≤ w)) = true ∧
      (SequentialCode.positiveIndices candidate).length < source.size ∧
      CurrentAdditive.CodeDUpdateFullPipeline.machine.OutputsWithin
        (CurrentAdditive.CodeDUpdateRequestABI.requestPacketList
          source coeff lambda)
        (CurrentAdditive.CodeDCanonicalSourceV2.encodedSource
          (CurrentAdditive.CodeDCompactSequentialBridge.retainedSource
            source candidate))
        (CurrentAdditive.CodeDUpdateFullPipeline.clock source coeff lambda) ∧
      ((advance GaussWideVectorInvoke.program)^[t])
        (⟨some GaussWideVectorInvoke.start, GaussWideVectorInvoke.control,
          GaussWideVectorInvoke.wide S⟩ :
          TM2.Cfg (fun _ : GaussWideVectorInvoke.Bank => Bool) _ _) =
        ⟨none, GaussWideVectorInvoke.control,
          Function.update (GaussWideVectorInvoke.wide T)
            GaussWideVectorInvoke.slots.target (vectorPacket coeff)⟩ := by
  let k := SequentialCode.columnCount a
  let Aq : Fin a.size → Fin k → ℚ := fun i j => (A i j : ℚ)
  let s := GaussControlTrace.after Aq k
  let weights := source.map Prod.snd
  obtain ⟨f, hf, t, T, lambda, ht, hdep, hmin, _, hpos, hr⟩ :=
    GaussCertifiedMinimumSemantic.actual_certificate_positive_minimum
      a A weights h01 hwide hA hsize hpositive hrow
  let coeff := Array.ofFn (directCandidate s.B f hf)
  have hsum : coeff.toList.sum = 0 :=
    SequentialElimination.zero_sum_of_constant_row a coeff hdep hrow
  obtain ⟨updated, helim, _, hnn, _, hshrink⟩ :=
    SequentialElimination.eliminateWeights_total a weights coeff
      hsize hpositive hdep hsum
  have heq : updated =
      CurrentAdditive.CodeDUpdatedArithmeticABI.candidateWeights
        source coeff lambda :=
    CurrentAdditive.CodeDUpdatedArithmeticABI.eliminateWeights_eq_candidate
      source coeff lambda updated hmin helim
  have hnn' :
      (CurrentAdditive.CodeDUpdatedArithmeticABI.candidateWeights
        source coeff lambda).all (fun w => decide (0 ≤ w)) = true := by
    simpa only [← heq] using hnn
  have hshrink' :
      (SequentialCode.positiveIndices
        (CurrentAdditive.CodeDUpdatedArithmeticABI.candidateWeights
          source coeff lambda)).length < source.size := by
    simpa only [← heq, weights, Array.size_map] using hshrink
  have houtput := CurrentAdditive.CodeDUpdateFullPipeline.outputs
    source coeff lambda hnn'
  refine ⟨f, hf, t, T, lambda, ht, hpos, hmin, hnn', hshrink',
    houtput, hr⟩

#print axioms actual_certified_update_stages

end CurrentAdditive.GaussCertifiedUpdateStages
