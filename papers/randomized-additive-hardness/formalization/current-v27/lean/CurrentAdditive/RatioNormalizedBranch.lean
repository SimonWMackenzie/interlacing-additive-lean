import CurrentAdditive.RatioBranchPolynomial
import CurrentAdditive.RatioSameOutput

set_option maxHeartbeats 800000
noncomputable section
namespace CurrentAdditive.RatioNormalizedBranch
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout RatioBranchLayout RatioBranchRun

/-- The physical branch may use the rational Gauss relation c=z/D.
It produces exactly the ordered source that the positive integer relation z
produces, including all tied zero deletions and every original retained index.
The scalar is computed by the physical branch; it is not an input word. -/
theorem uniform_run_integer_output : ∃ C d : Nat,
    ∀ {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) (lambda : ℚ)
      (hsize : coeff.size=source.size)
      (hmin : SequentialCode.minimumRatio (source.map Prod.snd) coeff = some lambda)
      (D : Nat) (hD : 0 < D) (z : Fin coeff.size → ℤ)
      (hcoeff : ∀ i : Fin coeff.size,
        coeff[i.val]?.getD 0 = (z i : ℚ)/(D : ℚ))
      (hnonneg : (CodeDUpdatedArithmeticABI.candidateWeights source
        (Array.ofFn fun i => (z i : ℚ)) (lambda / D)).all
        (fun w => decide (0 ≤ w)) = true),
    ∃ j : Fin coeff.size, j.val < source.size ∧ 0 < z j ∧
      lambda = (source.map Prod.snd)[j.val]?.getD 0 / coeff[j.val]?.getD 0 ∧
      lambda / D = (source.map Prod.snd)[j.val]?.getD 0 / (z j : ℚ) ∧
      ∃ t ≤ C*(RatioBranchPolynomial.inputSize source coeff+1)^d,
        let result := ((advance program)^[t])
          (⟨some start,control,frame (initialBank source coeff)⟩ :
            TM2.Cfg (fun _ : BigStack => Bool) _ _)
        result.l = none ∧ result.stk (core (low 24)) =
          CodeDCanonicalSourceV2.encodedSource
            (CodeDCompactSequentialBridge.retainedSource source
              (CodeDUpdatedArithmeticABI.candidateWeights source
                (Array.ofFn fun i => (z i : ℚ)) (lambda / D))) := by
  obtain ⟨C,d,hC⟩ := RatioBranchPolynomial.uniform_run
  refine ⟨C,d,?_⟩
  intro q source coeff lambda hsize hmin D hD z hcoeff hnonneg
  obtain ⟨j,hj,hpos,hratio,hinteger⟩ := RatioSameOutput.attained_integer
    (source.map Prod.snd) coeff lambda hmin D hD z hcoeff
  refine ⟨j,by simpa using hj,hpos,hratio,hinteger,?_⟩
  rw [RatioSameOutput.candidateWeights_integer source coeff lambda D hD z hcoeff] at hnonneg ⊢
  exact hC source coeff lambda hsize hmin hnonneg

#print axioms uniform_run_integer_output
end CurrentAdditive.RatioNormalizedBranch
