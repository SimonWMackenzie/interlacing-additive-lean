import EthInapproximability.CurrentPaper.SourceOriginalVariableCapture
import EthInapproximability.CurrentPaper.EncodedETHSource
import EthInapproximability.CurrentPaper.BitMachineBankCodec

/-!
# Original-size-bearing sparse branch packets

This is the intermediate word that the outer source-list producer must write
after the cited sparsification machine runs. The first bank is the original
CNF variable count in unary. The second is one sparse CNF word. Later one-item
machines may replace the second bank with a graph word, but must not replace
the first bank with a branch-local or graph-local size.

These codec and size lemmas do not assert that a packet-list machine exists.
-/

namespace EthInapproximability.CurrentPaper.SourceOriginalBranchPackets

def bank (n : ℕ) (word : List Bool) : Fin 2 → List Bool :=
  ![List.replicate n true, word]

def packet (n : ℕ) (word : List Bool) : List Bool :=
  BitMachineBankCodec.encode (bank n word)

def sparsePacket (n : ℕ) (g : EncodedETHSource.ValidFormula) : List Bool :=
  packet n (EncodedCNF.encode g.val)

def packetList {η : ℚ} (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) : List Bool :=
  SourceListEncoding.encode
    ((S.branches f).map (sparsePacket f.val.variables))

theorem packet_decode (n : ℕ) (word : List Bool) :
    BitMachineBankCodec.decode 2 (packet n word) = some (bank n word) :=
  BitMachineBankCodec.decode_encode _

theorem packet_length (n : ℕ) (word : List Bool) :
    (packet n word).length = 2*(n+word.length)+2 := by
  rw [packet, BitMachineBankCodec.encode_length]
  simp [bank, Fin.sum_univ_two]

theorem sparsePacket_length {η : ℚ}
    (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables)
    (g : EncodedETHSource.ValidFormula) (hg : g ∈ S.branches f) :
    (sparsePacket f.val.variables g).length ≤
      2*(f.val.variables +
        (8*S.density+3)*f.val.variables*(f.val.variables.size+1))+2 := by
  rw [sparsePacket, packet_length]
  have h := S.branch_encoded_length f hn g hg
  omega

theorem packetList_length {η : ℚ}
    (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables) :
    (packetList S f).length ≤
      3*(S.branches f).length *
        (2*(f.val.variables +
          (8*S.density+3)*f.val.variables*(f.val.variables.size+1))+3)+1 := by
  exact SourceListEncoding.encode_map_length_le (S.branches f)
    (sparsePacket f.val.variables) _
    (fun g hg => sparsePacket_length S f hn g hg)

/-- The cited sparsifier's *actual* machine produces the canonical sparse
list on this original CNF. The clock uses the original `f.val.variables`.
It does not yet attach the retained unary word to each item. -/
theorem sparse_list_outputs {η : ℚ}
    (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) :
    S.machine.OutputsWithin (EncodedCNF.encode f.val)
      (EncodedETHSource.formulaListBits (S.branches f))
      (S.timeConstant *
        ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ *
        ((EncodedCNF.encode f.val).length + 1) ^ S.timeExponent) := by
  have h := S.runtime (EncodedCNF.encode f.val)
  have hdec := EncodedCNF.decode_encode f.val f.property
  have hbits : EncodedETHSource.sparsificationBits S.branches
      (EncodedCNF.encode f.val) =
      EncodedETHSource.formulaListBits (S.branches f) := by
    unfold EncodedETHSource.sparsificationBits
    split
    · rename_i hd
      rw [hdec] at hd
      cases hd
    · rename_i g hd
      have hg : g = f.val := by
        have hh := hd.symm.trans hdec
        exact Option.some.inj hh
      subst g
      rfl
  rw [hbits] at h
  simpa only [hdec] using h

theorem sparse_list_count {η : ℚ}
    (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) :
    ((S.branches f).length : ℝ) ≤
      (2 : ℝ) ^ ((η : ℝ) * f.val.variables) := S.count f

end EthInapproximability.CurrentPaper.SourceOriginalBranchPackets
