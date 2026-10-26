import CurrentAdditive.CylinderSourceContractPrep
import CurrentAdditive.CylinderPairEvaluationBridge

/-! The physical one-coordinate callback's bit agrees with the corresponding
singleton cylinder entry of every actual retained source tuple. -/

namespace CurrentAdditive.CylinderSingletonSemantic

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderSourceTupleProjection
open CurrentAdditive.CylinderActualTupleRow
open SequentialCode

theorem coordinate_piece_entry {q : Nat}
    (entry : (Fin q → Nat) × ℚ) (i : Fin q) (y : Nat) :
    coordinatePiece i.val y.bits
      (SourceListEncoding.encode
        (List.ofFn (fun j : Fin q => (entry.1 j).bits))) =
      [decide (generatedFeatureValue entry.1 [(i.val, y)] ≠ 0)] := by
  have hp := CurrentAdditive.CylinderPairEvaluationBridge.pair_value_eq
    q entry.1 i y
  simp [coordinatePiece, SourceListEncoding.decode_encode, hp]

theorem singleton_row_exact {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (i : Fin q) (y : Nat) :
    (tupleWords source).flatMap (coordinatePiece i.val y.bits) =
      source.toList.map (fun entry =>
        decide (generatedFeatureValue entry.1 [(i.val, y)] ≠ 0)) := by
  simp only [tupleWords, List.flatMap_map]
  simp only [coordinate_piece_entry]
  exact List.map_eq_flatMap.symm

#print axioms coordinate_piece_entry
#print axioms singleton_row_exact

end CurrentAdditive.CylinderSingletonSemantic
