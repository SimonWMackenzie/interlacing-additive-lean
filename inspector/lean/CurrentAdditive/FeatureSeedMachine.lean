import CurrentAdditive.CylinderFeatureCodec
import CurrentAdditive.CodeDTargetV2
import CurrentAdditive.SequentialFeatureCoverage
import EthInapproximability.CurrentPaper.BitMachine

/-!
The physical seed for the ordered cylinder enumerator.  The empty feature is
emitted as a canonical V2 singleton packet.  This is a finite bit machine,
not a host-language `generatedFeatures` call.  The coordinate-extension
loop is a separate obligation.
-/

namespace CurrentAdditive.FeatureSeedMachine

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open Turing Turing.TM2.Stmt

def seedBytes : List Bool :=
  [true, true, false, true, true, false, false]

theorem seedBytes_exact :
    seedBytes =
      CurrentAdditive.CodeDCodecV2.encodeItems
        [CurrentAdditive.CylinderFeatureCodec.encodeFeature []] := by
  decide

def program : Fin 8 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 8) (Fin 1)
  | 0 => push 1 (fun _ => false) (goto (fun _ => 1))
  | 1 => push 1 (fun _ => false) (goto (fun _ => 2))
  | 2 => push 1 (fun _ => true) (goto (fun _ => 3))
  | 3 => push 1 (fun _ => true) (goto (fun _ => 4))
  | 4 => push 1 (fun _ => false) (goto (fun _ => 5))
  | 5 => push 1 (fun _ => true) (goto (fun _ => 6))
  | 6 => push 1 (fun _ => true) (goto (fun _ => 7))
  | 7 => halt

def machine : Machine where
  stackCount := 2
  labelCount := 8
  controlCount := 1
  input := 0
  output := 1
  start := 0
  initial := 0
  program := program

theorem physical_seed (input : List Bool) :
    machine.OutputsWithin input seedBytes 8 := by
  refine ⟨8, by omega, ?_, ?_⟩
  · rfl
  · rfl

theorem physical_zero_coordinates (D : Nat)
    (alphabet : Array (Nat × ℚ)) :
    machine.OutputsWithin
      (CurrentAdditive.CodeDTargetV2.alphabetBytes alphabet)
      (CurrentAdditive.CylinderFeatureCodec.generatedFeatureBits
        0 D (alphabet.map Prod.fst)) 8 := by
  simpa [CurrentAdditive.CylinderFeatureCodec.generatedFeatureBits,
    CurrentAdditive.CylinderFeatureCodec.encodeFeatures,
    SequentialCode.generatedFeatures, seedBytes_exact] using
    physical_seed (CurrentAdditive.CodeDTargetV2.alphabetBytes alphabet)

theorem empty_alphabet_features (q D : Nat) :
    SequentialCode.generatedFeatures q D (#[] : Array Nat) = #[[]] := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [CurrentAdditive.SequentialFeatureCoverage.generatedFeatures_succ,
        ih]
      simp [SequentialCode.extendFeatures]

theorem physical_empty_alphabet (q D : Nat) :
    machine.OutputsWithin
      (CurrentAdditive.CodeDTargetV2.alphabetBytes
        (#[] : Array (Nat × ℚ)))
      (CurrentAdditive.CylinderFeatureCodec.generatedFeatureBits
        q D (#[] : Array Nat)) 8 := by
  simpa [CurrentAdditive.CylinderFeatureCodec.generatedFeatureBits,
    CurrentAdditive.CylinderFeatureCodec.encodeFeatures,
    empty_alphabet_features, seedBytes_exact] using
    physical_seed
      (CurrentAdditive.CodeDTargetV2.alphabetBytes
        (#[] : Array (Nat × ℚ)))

#print axioms physical_seed
#print axioms physical_zero_coordinates
#print axioms physical_empty_alphabet

end CurrentAdditive.FeatureSeedMachine
