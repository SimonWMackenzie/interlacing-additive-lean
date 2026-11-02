import EthInapproximability.CurrentPaper.SourceOriginalListPacketizerFinal
import EthInapproximability.CurrentPaper.SourceOriginalPacketWork

/-! Original-size, per-branch envelope; the branch count remains an outer multiplier. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalListPacketizer

open EncodedCommunication

noncomputable section

def packetLimit (n L : ℕ) : ℕ := 2*(n+L)+2

noncomputable def framingEnvelope (n L : ℕ) : ℕ :=
  4*n+3*L+6 + 2*packetLimit n L+2 +
    (UnaryBinaryEncoding.coefficient+7)*(packetLimit n L+1)^2

noncomputable def itemEnvelope (n width L : ℕ) : ℕ :=
  (4*width+5)+1 + 20*(L+1)*(L+1)+1 + framingEnvelope n L +
    1+(3*packetLimit n L+1)+1+(L+1) +
    (Fintype.card FrameStack *
      (n+L+framingEnvelope n L*outerPushBound) +
      Fintype.card FrameStack+1)

theorem packet_length_le (n L : ℕ) (word : List Bool)
    (hw : word.length ≤ L) :
    (SourceOriginalPacketFraming.packet n word).length ≤ packetLimit n L := by
  rw [SourceOriginalPacketFraming.packet,
    SourceOriginalBranchPackets.packet_length]
  unfold packetLimit
  omega

theorem answer_length_le (n L : ℕ) (word : List Bool)
    (hw : word.length ≤ L) :
    (SourceOriginalPacketFraming.answer n word).length ≤
      3*packetLimit n L+1 := by
  have hp := packet_length_le n L word hw
  have hh := EncodedGraph.natField_length_upper
    (SourceOriginalPacketFraming.packet n word).length
  unfold SourceOriginalPacketFraming.answer
  simp only [List.length_append]
  omega

theorem framingTime_le (n L : ℕ) (word : List Bool)
    (hw : word.length ≤ L) :
    SourceOriginalPacketFraming.framingTime n word ≤
      (UnaryBinaryEncoding.coefficient+7)*(packetLimit n L+1)^2 := by
  have hp := packet_length_le n L word hw
  have hpow : ((SourceOriginalPacketFraming.packet n word).length+1)^2 ≤
      (packetLimit n L+1)^2 := Nat.pow_le_pow_left (by omega) _
  exact Nat.mul_le_mul_left _ hpow

theorem totalTime_le (n L : ℕ) (word : List Bool)
    (hw : word.length ≤ L) :
    SourceOriginalPacketFraming.totalTime n word ≤ framingEnvelope n L := by
  have hp := packet_length_le n L word hw
  have hf := framingTime_le n L word hw
  unfold SourceOriginalPacketFraming.totalTime
    SourceOriginalPacketFraming.writerTime framingEnvelope
  omega

theorem itemTimeWidth_le (n width L : ℕ) (word : List Bool)
    (hw : word.length ≤ L) :
    itemTimeWidth n width word ≤ itemEnvelope n width L := by
  have hbits := UnaryBinaryEncoding.bits_length_le word.length
  have hparser : 20*(word.length+1)*(word.length.bits.length+1) ≤
      20*(L+1)*(L+1) := by
    have h1 : word.length+1 ≤ L+1 := by omega
    have h2 : word.length.bits.length+1 ≤ L+1 := by omega
    have hm := Nat.mul_le_mul h1 h2
    have hh := Nat.mul_le_mul_left 20 hm
    simpa [Nat.mul_assoc] using hh
  have htime := totalTime_le n L word hw
  have hout := answer_length_le n L word hw
  have hframe : outerFrameBound n word ≤
      n+L+framingEnvelope n L*outerPushBound := by
    have hm := Nat.mul_le_mul_right outerPushBound htime
    unfold outerFrameBound
    omega
  have hcleanup : outerCleanupBound n word ≤
      Fintype.card FrameStack *
        (n+L+framingEnvelope n L*outerPushBound) +
        Fintype.card FrameStack+1 := by
    have hm := Nat.mul_le_mul_left (Fintype.card FrameStack) hframe
    unfold outerCleanupBound
    omega
  unfold itemTimeWidth itemEnvelope
  omega

theorem listWork_le_count (n width L : ℕ) (words : List (List Bool))
    (hwords : ∀ word ∈ words, word.length ≤ L) :
    listWork n width words ≤ words.length * itemEnvelope n width L := by
  induction words with
  | nil => simp [listWork]
  | cons word words ih =>
      have hw := hwords word (by simp)
      have htail : ∀ x ∈ words, x.length ≤ L := by
        intro x hx
        exact hwords x (by simp [hx])
      have ht := ih htail
      have hitem := itemTimeWidth_le n width L word hw
      simp only [listWork, List.length_cons]
      calc
        itemTimeWidth n width word + listWork n width words ≤
            itemEnvelope n width L +
              words.length * itemEnvelope n width L :=
          Nat.add_le_add hitem ht
        _ = (words.length+1)*itemEnvelope n width L := by ring

def branchLimit {η : ℚ} (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) : ℕ :=
  (8*S.density+3)*f.val.variables*(f.val.variables.size+1)

theorem source_listWork_le_count {η : ℚ}
    (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables) :
    listWork f.val.variables (S.branches f).length.bits.length
      ((S.branches f).map fun g => EncodedCNF.encode g.val) ≤
    (S.branches f).length *
      itemEnvelope f.val.variables (S.branches f).length.bits.length
        (branchLimit S f) := by
  have h := listWork_le_count f.val.variables
    (S.branches f).length.bits.length (branchLimit S f)
    ((S.branches f).map fun g => EncodedCNF.encode g.val) ?_
  · simpa only [List.length_map] using h
  · intro word hw
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hw
    exact S.branch_encoded_length f hn g hg

theorem source_time_le_count {η : ℚ}
    (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables) :
    canonicalTime f.val.variables
        ((S.branches f).map fun g => EncodedCNF.encode g.val) ≤
      (5*(S.branches f).length.bits.length+7) +
      (S.branches f).length *
        itemEnvelope f.val.variables (S.branches f).length.bits.length
          (branchLimit S f) +
      ((4*(S.branches f).length.bits.length+5)+1+1+
        (3*(S.branches f).length*(2*(f.val.variables+branchLimit S f)+3)+2)+1) := by
  have hw := source_listWork_le_count S f hn
  have hp := SourceOriginalBranchPackets.packetList_length S f hn
  have he := output_eq_packetList S f
  unfold canonicalTime
  simp only [List.length_map]
  rw [← he] at hp
  dsimp [branchLimit] at hw hp ⊢
  omega

end

end EthInapproximability.CurrentPaper.SourceOriginalListPacketizer
