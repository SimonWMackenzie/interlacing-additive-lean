import CurrentAdditive.GaussPivotInputBytes32
import CurrentAdditive.IndexedV2Clock

namespace CurrentAdditive.GaussPivotPacketLengths32

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

theorem fields_le_encode (xs : List (List Bool)) :
    (SourceListEncoding.fields xs).length ≤
      (SourceListEncoding.encode xs).length := by
  simp only [SourceListEncoding.encode,List.length_append]
  omega

theorem fields_snoc (xs : List (List Bool)) (x : List Bool) :
    SourceListEncoding.fields (xs ++ [x]) =
      SourceListEncoding.fields xs ++ natField x.length ++ x := by
  rw [CurrentAdditive.GaussListContext.IndexedV2Clock.fields_append]
  simp [SourceListEncoding.fields,List.append_assoc]

theorem appended_fields_length {m k : Nat}
    (ps : List (Fin m × Fin k)) (p : Fin m × Fin k) :
    (SourceListEncoding.fields
      ((ps ++ [p]).map GaussControlTrace.pivotPacket)).length ≤
      (GaussControlTrace.pivotsPacket ps).length +
        3*(GaussControlTrace.pivotPacket p).length+1 := by
  have h := fields_le_encode (ps.map GaussControlTrace.pivotPacket)
  have hn := EncodedGraph.natField_length_upper
    (GaussControlTrace.pivotPacket p).length
  rw [List.map_append,List.map_singleton,fields_snoc]
  simp only [List.length_append]
  change (SourceListEncoding.fields
      (ps.map GaussControlTrace.pivotPacket)).length +
      (natField (GaussControlTrace.pivotPacket p).length).length +
      (GaussControlTrace.pivotPacket p).length ≤ _
  dsimp [GaussControlTrace.pivotsPacket]
  omega

theorem appended_packet_length {m k : Nat}
    (ps : List (Fin m × Fin k)) (p : Fin m × Fin k) :
    (GaussControlTrace.pivotsPacket (ps ++ [p])).length ≤
      (GaussControlTrace.pivotsPacket ps).length +
      2*(ps.length+1)+1+
      3*(GaussControlTrace.pivotPacket p).length+1 := by
  have hbody := appended_fields_length ps p
  have hcount := EncodedGraph.natField_length_upper (ps ++ [p]).length
  simp only [List.length_append,List.length_singleton] at hcount
  simp only [GaussControlTrace.pivotsPacket,
    SourceListEncoding.encode,List.length_append,
    List.length_map] at *
  simp only [List.length_singleton] at *
  omega

#print axioms fields_snoc
#print axioms appended_packet_length

end CurrentAdditive.GaussPivotPacketLengths32
