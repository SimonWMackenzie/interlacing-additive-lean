import CurrentAdditive.RatioListPolynomial
import CurrentAdditive.CodeDUpdateFullPipeline

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 100
noncomputable section
namespace CurrentAdditive.RatioUpdaterItemPolynomial
open EthInapproximability.CurrentPaper EntryClockPoly

syntax "solve_update_poly" : tactic
macro_rules
  | `(tactic| solve_update_poly) => `(tactic| first
      | assumption
      | exact PolyIn.self
      | exact PolyIn.const _
      | (apply PolyIn.add <;> solve_update_poly)
      | (apply PolyIn.mul <;> solve_update_poly)
      | (apply PolyIn.pow <;> solve_update_poly))

theorem growth_poly {ι : Type*} (U : ι → Nat) (M : BitMachine.Machine)
    (input output : ι → List Bool) (clock : ι → Nat)
    (hM : ∀ i,M.OutputsWithin (input i) (output i) (clock i))
    (hinput : PolyIn U (fun i => (input i).length)) (hclock : PolyIn U clock) :
    PolyIn U (fun i => (output i).length) := by
  apply PolyIn.mono (fun i => BitMachine.output_length_bound M (hM i))
  exact hinput.add (hclock.mul (PolyIn.const M.pushBound))

theorem field_poly {ι : Type*} {U : ι → Nat} (word : ι → List Bool)
    (h : PolyIn U (fun i => (word i).length)) :
    PolyIn U (fun i => (EncodedCommunication.field (word i)).length) := by
  simp only [EncodedCommunication.field_length]
  solve_update_poly

theorem invoke_poly {ι : Type*} (U : ι → Nat) (M : BitMachine.Machine)
    (L T : ι → Nat) (hL : PolyIn U L) (hT : PolyIn U T) :
    PolyIn U (fun i => RatioListClockCaps.invokeCap M (L i) (T i)) := by
  unfold RatioListClockCaps.invokeCap
  solve_update_poly

def byteSize : List Bool → Nat := List.length

theorem old_fields_poly :
    PolyIn byteSize CodeDUpdateSourceFields.oldEntryClock ∧
    PolyIn byteSize CodeDUpdateSourceFields.oldWeightClock ∧
    PolyIn byteSize (fun x => (CodeDUpdateSourceFields.oldEntryField x).length) ∧
    PolyIn byteSize (fun x => (CodeDUpdateSourceFields.oldWeightField x).length) := by
  have ho : PolyIn byteSize (fun x => (CodeDUpdateSourceFields.oldEntryWord x).length) :=
    PolyIn.of_le (fun x => BankFieldProjection.result_length (0 : Fin 3) x)
  have hw : PolyIn byteSize (fun x => (CodeDUpdateSourceFields.oldWeightWord x).length) :=
    PolyIn.mono (fun x => BankFieldProjection.result_length (1 : Fin 2)
      (CodeDUpdateSourceFields.oldEntryWord x)) ho
  refine ⟨?_,?_,field_poly _ ho,field_poly _ hw⟩
  · unfold CodeDUpdateSourceFields.oldEntryClock
    solve_update_poly
  · unfold CodeDUpdateSourceFields.oldWeightClock
    solve_update_poly

theorem product_poly : PolyIn byteSize CodeDUpdateProductFramed.clock ∧
    PolyIn byteSize (fun x => (CodeDUpdateProductFramed.result x).length) := by
  have hclock : PolyIn byteSize
      (fun x => CodeDUpdateProductPolytime.coefficient*(x.length+1)^CodeDUpdateProductPolytime.exponent) := by
    solve_update_poly
  have hout : PolyIn byteSize (fun x => (CodeDUpdateProductFramed.productWord x).length) :=
    growth_poly byteSize CodeDUpdateProductPolytime.machine id _ _
      CodeDUpdateProductPolytime.outputs PolyIn.self hclock
  refine ⟨?_,field_poly _ hout⟩
  unfold CodeDUpdateProductFramed.clock
  solve_update_poly

theorem subtract_pair_poly : PolyIn byteSize CodeDUpdateSubtractPairJoin.clock ∧
    PolyIn byteSize (fun x => (CodeDUpdateSubtractPairJoin.output x).length) := by
  have ho := old_fields_poly
  have hp := product_poly
  have hc : PolyIn byteSize CodeDUpdateSubtractPairJoin.clock := by
    have hoClock := ho.2.1
    have hoLength := ho.2.2.2
    have hpClock := hp.1
    have hpLength := hp.2
    unfold CodeDUpdateSubtractPairJoin.clock
    solve_update_poly
  exact ⟨hc,growth_poly byteSize CodeDUpdateSubtractPairJoin.machine id _ _
    CodeDUpdateSubtractPairJoin.outputs PolyIn.self hc⟩

theorem difference_poly : PolyIn byteSize CodeDUpdateDifferenceFramed.clock ∧
    PolyIn byteSize (fun x => (CodeDUpdateDifferenceFramed.result x).length) := by
  have hpair := subtract_pair_poly
  have hpClock := hpair.1
  have hpLength := hpair.2
  have hdClock : PolyIn byteSize (fun x => RationalSubtractCanonical.coefficient*
      ((CodeDUpdateSubtractPairJoin.output x).length+1)^RationalSubtractCanonical.exponent) := by
    solve_update_poly
  have hdLength : PolyIn byteSize (fun x => (CodeDUpdateDifferenceFramed.differenceWord x).length) :=
    growth_poly byteSize RationalSubtractCanonical.machine _ _ _
      (fun x => RationalSubtractCanonical.outputsWithin (CodeDUpdateSubtractPairJoin.output x))
      hpLength hdClock
  refine ⟨?_,field_poly _ hdLength⟩
  unfold CodeDUpdateDifferenceFramed.clock
  solve_update_poly

theorem arithmetic_item_poly : PolyIn byteSize CodeDUpdateFinalPairJoin.clock := by
  have ho := old_fields_poly
  have hd := difference_poly
  have hoClock := ho.1
  have hoLength := ho.2.2.1
  have hdClock := hd.1
  have hdLength := hd.2
  unfold CodeDUpdateFinalPairJoin.clock
  solve_update_poly

theorem entry_item_poly : PolyIn byteSize CodeDUpdatedEntryJoin.clock := by
  have ho : PolyIn byteSize (fun x => (CodeDUpdatedEntryFields.outerOld x).length) :=
    PolyIn.of_le (fun x => BankFieldProjection.result_length (0 : Fin 2) x)
  have hw : PolyIn byteSize (fun x => (CodeDUpdatedEntryFields.oldWord x).length) :=
    PolyIn.mono (fun x => BankFieldProjection.result_length (0 : Fin 2)
      (CodeDUpdatedEntryFields.outerOld x)) ho
  have hr : PolyIn byteSize (fun x => (CodeDUpdatedEntryFields.weightWord x).length) :=
    PolyIn.of_le (fun x => BankFieldProjection.result_length (1 : Fin 2) x)
  have hoLength := field_poly _ hw
  have hrLength := field_poly _ hr
  have hwClock : PolyIn byteSize CodeDUpdatedEntryFields.wordClock := by
    unfold CodeDUpdatedEntryFields.wordClock
    solve_update_poly
  have hrClock : PolyIn byteSize CodeDUpdatedEntryFields.weightClock := by
    unfold CodeDUpdatedEntryFields.weightClock
    solve_update_poly
  unfold CodeDUpdatedEntryJoin.clock
  solve_update_poly

#print axioms arithmetic_item_poly
#print axioms entry_item_poly
end CurrentAdditive.RatioUpdaterItemPolynomial
