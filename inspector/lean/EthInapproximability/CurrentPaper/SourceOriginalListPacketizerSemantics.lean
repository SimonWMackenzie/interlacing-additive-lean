import EthInapproximability.CurrentPaper.SourceOriginalBranchPackets

/-! Exact ordered bit-string target of the physical source packetizer. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalListPacketizer

open EncodedCommunication

def answer (n : ℕ) (word : List Bool) : List Bool :=
  natField (SourceOriginalBranchPackets.packet n word).length ++
    SourceOriginalBranchPackets.packet n word

def joined (n : ℕ) : List (List Bool) → List Bool
  | [] => []
  | word :: words => answer n word ++ joined n words

theorem joined_fields (n : ℕ) (words : List (List Bool)) :
    joined n words =
      SourceListEncoding.fields
        (words.map (SourceOriginalBranchPackets.packet n)) := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      change answer n word ++ joined n words =
        (natField (SourceOriginalBranchPackets.packet n word).length ++
          SourceOriginalBranchPackets.packet n word) ++
        SourceListEncoding.fields
          (words.map (SourceOriginalBranchPackets.packet n))
      rw [ih]
      rfl

theorem output_eq_packetList {η : ℚ}
    (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) :
    natField (S.branches f).length ++
      joined f.val.variables
        ((S.branches f).map fun g => EncodedCNF.encode g.val) =
      SourceOriginalBranchPackets.packetList S f := by
  unfold SourceOriginalBranchPackets.packetList SourceListEncoding.encode
  rw [joined_fields]
  simp only [List.map_map, List.length_map,
    SourceOriginalBranchPackets.sparsePacket, Function.comp_apply]
  rfl

end EthInapproximability.CurrentPaper.SourceOriginalListPacketizer
