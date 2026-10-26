import CurrentAdditive.CylinderEmptyRowClock

/-! The source-driven empty-cylinder row is the literal first feature row. -/

namespace CurrentAdditive.CylinderEmptyRowSemanticBridge

open EthInapproximability.CurrentPaper
open CurrentAdditive.CylinderFeatureCodec
open SequentialCode
open CurrentAdditive.SequentialSourceCode

theorem first_feature_empty (q D : Nat) (alphabet : Array Nat) :
    (generatedFeatures q D alphabet)[0]? = some [] :=
  generatedFeatures_head_empty q D alphabet

theorem first_row_ones (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    (cylinders q D alphabet source)[0]? =
      some (source.map (fun _ => (1 : ℚ))) := by
  let F := generatedFeatures q D alphabet
  have hpos : 0 < F.size := generatedFeatures_pos q D alphabet
  have hfirst : F[0] = ([] : List (Nat × Nat)) := by
    have h := first_feature_empty q D alphabet
    change F[0]? = some [] at h
    rw [Array.getElem?_eq_getElem hpos] at h
    exact Option.some.inj h
  rw [Array.getElem?_eq_getElem (by simpa [cylinders, featureRows] using hpos)]
  congr 1
  simp [cylinders, featureRows, F, hfirst, generatedFeatureValue]

#print axioms first_row_ones

end CurrentAdditive.CylinderEmptyRowSemanticBridge
