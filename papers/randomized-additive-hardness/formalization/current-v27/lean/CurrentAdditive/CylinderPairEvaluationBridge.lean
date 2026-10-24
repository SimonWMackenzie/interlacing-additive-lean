import CurrentAdditive.CylinderTupleCoordinate
import CurrentAdditive.CylinderEqualMachine
import CurrentAdditive.CylinderFeatureCodec

/-! The literal symbol-comparison program computes exactly one source
cylinder-pair predicate once the selected tuple symbol and feature symbol are
on its two input stacks. -/

namespace CurrentAdditive.CylinderPairEvaluationBridge

open EthInapproximability.CurrentPaper
open SequentialCode
open CurrentAdditive.CylinderEqualMachine

private theorem bits_injective : Function.Injective Nat.bits := by
  intro a b h
  have hv := congrArg EncodedCommunication.bitsValue h
  simpa using hv

theorem pair_value_eq (q : Nat) (v : Fin q → Nat)
    (i : Fin q) (y : Nat) :
    generatedFeatureValue v [(i.val,y)] =
      if decide ((v i).bits = y.bits) then 1 else 0 := by
  have heq : ((v i).bits = y.bits) ↔ v i = y :=
    ⟨fun h => bits_injective h, congrArg Nat.bits⟩
  simp [generatedFeatureValue, i.isLt, heq]

theorem physical_pair_value (q : Nat) (v : Fin q → Nat)
    (i : Fin q) (y : Nat) :
    ∃ t ≤ min (v i).bits.length y.bits.length + 1,
      (run t (cfg (some .scan) (true, none, none)
        (v i).bits y.bits [])).l = none ∧
      (run t (cfg (some .scan) (true, none, none)
        (v i).bits y.bits [])).stk 2 =
        [decide (generatedFeatureValue v [(i.val,y)] = 1)] := by
  obtain ⟨t, ht, hh, ho⟩ := compare_run true (v i).bits y.bits []
  refine ⟨t, ht, hh, ?_⟩
  rw [ho]
  simp [pair_value_eq]

#print axioms physical_pair_value

end CurrentAdditive.CylinderPairEvaluationBridge
