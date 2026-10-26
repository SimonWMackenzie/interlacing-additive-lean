import CurrentAdditive.CylinderEvalTypedBytes
import EthInapproximability.CurrentPaper.SourceListMachineSemantics

namespace CurrentAdditive.CylinderEvalByteBounds

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec

theorem item_le_list (xs : List (List Bool)) (w : List Bool) (hw : w∈xs) :
    w.length≤(SourceListEncoding.encode xs).length := by
  have hi := CurrentAdditive.GaussListContext.IndexedV2Clock.fields_item_length_le xs w hw
  simp only [SourceListEncoding.encode,List.length_append]
  omega

theorem count_le_list (xs : List (List Bool)) :
    xs.length≤(SourceListEncoding.encode xs).length := by
  have hc := SourceListMachineSemantics.count_le_fields_length xs
  simp only [SourceListEncoding.encode,List.length_append]
  omega

theorem bank2_length (a b : List Bool) :
    (encode ![a,b]).length=2*a.length+2*b.length+2 := by
  simp [encode_length,Fin.sum_univ_two]
  omega

theorem bank3_length (a b c : List Bool) :
    (encode ![a,b,c]).length=2*a.length+2*b.length+2*c.length+3 := by
  simp [encode_length,Fin.sum_univ_succ]
  omega

theorem packet_item_le (context : List Bool) (xs : List (List Bool))
    (w : List Bool) (hw : w∈xs) :
    (encode ![context,w]).length≤
      (encode ![context,SourceListEncoding.encode xs]).length := by
  have hi := item_le_list xs w hw
  rw [bank2_length,bank2_length]
  omega

theorem reassociated_length_le (q a b : List Bool) :
    (encode ![encode ![q,b],a]).length≤2*(encode ![encode ![q,a],b]).length := by
  simp only [bank2_length]
  omega

theorem prepared_length_le (q a b : List Bool) :
    (encode ![encode ![q,b],a]).length≤2*(encode ![q,a,b]).length := by
  simp only [bank2_length,bank3_length]
  omega

def cellCap : ℕ :=
  max (CylinderRowSerializer.encodedCell false).length (CylinderRowSerializer.encodedCell true).length

theorem cell_length_le (b : Bool) : (CylinderRowSerializer.encodedCell b).length≤cellCap := by
  cases b
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem row_length_le (bits : List Bool) :
    (CylinderRowSerializer.encodedRow bits).length≤3*bits.length*(cellCap+1)+1 :=
  SourceListEncoding.encode_map_length_le bits CylinderRowSerializer.encodedCell cellCap
    (fun b _ => cell_length_le b)

end CurrentAdditive.CylinderEvalByteBounds

#print axioms CurrentAdditive.CylinderEvalByteBounds.packet_item_le
#print axioms CurrentAdditive.CylinderEvalByteBounds.row_length_le
