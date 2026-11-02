import CurrentAdditive.V40DeterministicConcreteSource

/-! Actual fixed-round polynomial reductions and fixed-additive estimator
consequences for the full literal CNF language. -/
namespace CurrentAdditive.V40DeterministicETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication EncodedComplexity
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39CurrentSourceJoin V39PermittedDeterministicExtraction V39FramedNumerical
open V40DeterministicSourcePack PhysicalProducer
open scoped Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

private theorem pointwise_comp_poly (F : Producer) (M : BitMachine.Machine)
    (target : List Bool→List Bool) (d : ℕ)
    (h : ∀ w,M.OutputsWithin (F.result w) (target w) (((F.result w).length+1)^d)) :
    BitMachine.Polytime target := by
  refine ⟨BitMachineComposition.composition F.machine M,
    F.coefficient+2*(F.coefficient*F.machine.pushBound+1)+(F.coefficient*F.machine.pushBound+1)^d,
    (F.degree+1)*(d+1),?_⟩
  intro w
  have hr:=BitMachineComposition.composition_outputsWithin F.machine M (F.outputs w) (h w)
  apply BitMachine.outputsWithin_mono _ hr
  simpa only [one_mul] using BitMachineCompositionArithmetic.composition_time_bound w.length
    F.coefficient F.degree 1 d F.machine.pushBound (F.result w).length
    (BitMachine.output_length_bound F.machine (F.outputs w))

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem rectangleSource_poly (k : ℕ) :
    BitMachine.Polytime (fun w=>encodeInstance (V40DeterministicFixedGap.instanceWord D B k w)) := by
  apply pointwise_comp_poly (fixedFront D B k)
    (V40DeterministicGraphConstructor.rectangleMachine (parameters D B)) _
    (V40DeterministicGraphConstructor.rectanglePolynomialDegree (parameters D B) k)
  intro w
  have hr:=source_rectangle_fixed_outputs D B k w
  rw [←fixed_front_result D B k w] at hr
  exact hr

theorem requestSource_poly (k : ℕ) :
    BitMachine.Polytime (fun w=>sourceRequest D B (fixedFormula w) k) := by
  apply pointwise_comp_poly (fixedFront D B k)
    (V40DeterministicGraphConstructor.requestMachine (parameters D B)) _
    (V40DeterministicGraphConstructor.requestPolynomialDegree (parameters D B) k)
  intro w
  have hr:=source_request_fixed_outputs D B k (fixedFormula w)
  rw [←fixed_front_result D B k w] at hr
  exact hr

include D B in
theorem fixed_gap_reduction (k : ℕ) (hk : 1≤k) :
    Reduces EncodedCNF.Language EncodedCommunication.Language :=
  V40DeterministicFixedGap.reduction_of_physical_polytime D B k hk (rectangleSource_poly D B k)

theorem fixed_gap_exact_no (k : ℕ) (w : List Bool) (hn : w∉EncodedCNF.Language) :
    Workspace.Types.CommComplexity.D (ProtocolVerifier.tableGame
      (V40DeterministicFixedGap.instanceWord D B k w).rows
      (V40DeterministicFixedGap.instanceWord D B k w).cols
      (V40DeterministicFixedGap.instanceWord D B k w).table)=
      (V40DeterministicFixedGap.instanceWord D B k w).threshold+k := by
  rw [V40DeterministicFixedGap.table_eq]
  exact ethRun_no D B (fixedFormula w) k
    (fun hsat=>hn ((fixed_front_sat_iff w).1 hsat))

include D B in
theorem fixed_gap_npHard (hard : NPHard EncodedCNF.Language) :
    NPHard EncodedCommunication.Language :=
  ComplexityReductionClosure.npHard_of_reduces hard (fixed_gap_reduction D B 1 (by decide))

include D B in
theorem fixed_additive_square_inP (A : PermittedDeterministicEstimator) (u : ℝ)
    (hu : 0≤u) (hA : FixedSquareAccuracy A u) : ComplexityReductionClosure.InP EncodedCNF.Language := by
  have hreq:=requestSource_poly D B (fixedRound u)
  have he : BitMachine.Polytime (extractedEstimator A).run :=
    ⟨(extractedEstimator A).machine,(extractedEstimator A).clockCoefficient,
      (extractedEstimator A).clockDegree,V39FramedNumerical.machine_outputs (extractedEstimator A)⟩
  have hpoly:=BitMachineComposition.polytime_comp hreq he
  change BitMachine.Polytime (fun w=>(extractedEstimator A).run
    (sourceRequest D B (fixedFormula w) (fixedRound u))) at hpoly
  have heq : (fun w=>(extractedEstimator A).run (sourceRequest D B (fixedFormula w) (fixedRound u)))=
      (fun w=>[decide (w∈EncodedCNF.Language)]) := by
    funext w
    exact fixed_all_input_classification D B A u hA w
  rw [heq] at hpoly
  exact ⟨fun w=>decide (w∈EncodedCNF.Language),hpoly,fun w=>by simp⟩

include D B in
theorem fixed_additive_np_subset_p (hard : NPHard EncodedCNF.Language)
    (A : PermittedDeterministicEstimator) (u : ℝ) (hu : 0≤u) (hA : FixedAccuracy A u) :
    ∀ L, InNP L → ComplexityReductionClosure.InP L :=
  ComplexityReductionClosure.npHard_inP_implies_np_subset_p hard
    (fixed_additive_square_inP D B A u hu (fixedSquareAccuracy_of_fixedAccuracy A u hA))

#print axioms rectangleSource_poly
#print axioms requestSource_poly
#print axioms fixed_gap_reduction
#print axioms fixed_gap_exact_no
#print axioms fixed_gap_npHard
#print axioms fixed_additive_square_inP
#print axioms fixed_additive_np_subset_p
end
end CurrentAdditive.V40DeterministicETHEndpoint
