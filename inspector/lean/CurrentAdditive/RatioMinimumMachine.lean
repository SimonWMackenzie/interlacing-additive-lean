import CurrentAdditive.RatioMinimumRun
import CurrentAdditive.MinimumRatioWitness

set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 100
set_option maxRecDepth 10000
set_option synthInstance.maxSize 4096
noncomputable section
namespace CurrentAdditive.RatioMinimumMachine
open Turing EthInapproximability.CurrentPaper BitMachineEncoding MinimumRatioCallbackLayout

def machine : BitMachine.Machine :=
  ofFinite (low 8) (low 9) RatioMinimumRun.start RatioMinimumRun.control RatioMinimumRun.program

theorem initial (source : List Bool) :
    rawInit (low 8) RatioMinimumRun.start RatioMinimumRun.control source =
      (⟨some RatioMinimumRun.start,RatioMinimumRun.control,
        RatioPhysicalFold.boundary source [] [] 0 0⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) := by
  unfold rawInit
  congr 1
  funext j
  simp [rawInit,RatioPhysicalFold.boundary,StatefulListScheduler.initialBank,
    RatioPhysicalFold.blank,Function.update_apply,low,Fin.ext_iff,Fin.ofNat]
  split_ifs <;> simp_all

theorem uniform_outputs : ∃ C d : Nat,∀ xs : List (List Bool),
    machine.OutputsWithin (SourceListEncoding.encode xs)
      (xs.foldl MinimumRatioStepSpec.step []) (C*((SourceListEncoding.encode xs).length+1)^d) := by
  obtain ⟨C,d,hC⟩ := RatioMinimumRun.uniform_run
  refine ⟨C,d,?_⟩
  intro xs
  obtain ⟨t,ht,v,hr⟩ := hC xs []
  apply outputsWithin_of_raw_run (low 8) (low 9)
    RatioMinimumRun.start RatioMinimumRun.control RatioMinimumRun.program
    (SourceListEncoding.encode xs) (xs.foldl MinimumRatioStepSpec.step []) t _ ht
  · rw [initial]
    exact congrArg TM2.Cfg.l hr
  · rw [initial]
    have ho := congrArg (fun c => c.stk (low 9)) hr
    simpa [RatioPhysicalFold.boundary,StatefulListScheduler.initialBank,
      Function.update_apply,low,Fin.ext_iff,Fin.ofNat] using ho

theorem canonical_fold (weights coeff : Array ℚ) :
    (RatioPhysicalFold.pairWords (MinimumRatioFoldSemanticJoin.pairs weights coeff)).foldl
      MinimumRatioStepSpec.step [] =
    MinimumRatioStepSpec.bestPacket (SequentialCode.minimumRatio weights coeff) := by
  have he := RatioPhysicalFold.fold_pairWords (MinimumRatioFoldSemanticJoin.pairs weights coeff)
    (MinimumRatioFoldSemanticJoin.pairs_valid weights coeff) none
  change _ = MinimumRatioStepSpec.bestPacket
    (MinimumRatioFoldSemanticJoin.semanticFold (MinimumRatioFoldSemanticJoin.pairs weights coeff)) at he
  rw [MinimumRatioFoldSemanticJoin.semanticFold_eq_minimumRatio] at he
  exact he

/-- A single fixed machine and one uniform polynomial compute the attained
minimum from the actual ordered pairs, including count preparation. -/
theorem attained_minimum : ∃ C d : Nat,∀ (weights coeff : Array ℚ) (lambda : ℚ),
    SequentialCode.minimumRatio weights coeff = some lambda →
    ∃ j ∈ List.range (min weights.size coeff.size),
      0 < coeff[j]?.getD 0 ∧ lambda = weights[j]?.getD 0 / coeff[j]?.getD 0 ∧
      machine.OutputsWithin
        (SourceListEncoding.encode (RatioPhysicalFold.pairWords
          (MinimumRatioFoldSemanticJoin.pairs weights coeff)))
        (MinimumRatioStepSpec.bestPacket (some lambda))
        (C*((SourceListEncoding.encode (RatioPhysicalFold.pairWords
          (MinimumRatioFoldSemanticJoin.pairs weights coeff))).length+1)^d) := by
  obtain ⟨C,d,hC⟩ := uniform_outputs
  refine ⟨C,d,?_⟩
  intro weights coeff lambda hmin
  obtain ⟨j,hj,hpos,hratio⟩ := RationalBitBounds.minimumRatio_attained weights coeff lambda hmin
  refine ⟨j,hj,hpos,hratio,?_⟩
  simpa only [canonical_fold,hmin] using hC
    (RatioPhysicalFold.pairWords (MinimumRatioFoldSemanticJoin.pairs weights coeff))

#print axioms uniform_outputs
#print axioms attained_minimum
end CurrentAdditive.RatioMinimumMachine
