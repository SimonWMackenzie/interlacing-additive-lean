import EthInapproximability.CurrentPaper.SourceGenericPairVertexMass
import EthInapproximability.CurrentPaper.SourceClauseCounting

/-! Generic source-chain byte bound for one ordered pair, including the
diagonal. All bounds are deliberately coarse and valid at every alphabet. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPairEnumeration

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF SourceGenericPrefix

def ordinalBound (n a : Nat) : Nat :=
  n + a*a*n + a*a + a

def variableBound (n a q : Nat) : Nat :=
  n*a + (ordinalBound n a + 1)*(width a q + 1) + 4

def wordBound (n a q : Nat) : Nat :=
  8*(6*variableBound n a q+6)

theorem pairOrdinal_le {n a : Nat} (v : Fin n) (s t : Fin a) :
    pairOrdinal v s t ≤ ordinalBound n a := by
  have hv := Nat.mul_le_mul_left (a*a) (Nat.le_of_lt v.isLt)
  have hs := Nat.mul_le_mul_left a (Nat.le_of_lt s.isLt)
  have ht := Nat.le_of_lt t.isLt
  dsimp [pairOrdinal, ordinalBound]
  omega

theorem pair_word_length_le {n a : Nat} (q : Nat)
    (v : Fin n) (s t : Fin a) :
    (payload q v (s,t)).length ≤ wordBound n a q := by
  let b := base n a q (pairOrdinal v s t)
  let M := variableBound n a q
  have ho := pairOrdinal_le v s t
  have hmul := Nat.mul_le_mul_right (width a q+1) ho
  have hbase : b + (pairPayload v s t).length < M := by
    rw [SourceGenericPrefix.pair_length]
    change n*a + pairOrdinal v s t * (width a q + 1) + 2 <
      n*a + (ordinalBound n a + 1)*(width a q + 1)+4
    rw [Nat.add_mul]
    omega
  have hlit : ∀ l ∈ pairPayload v s t, l.variable < M := by
    intro l hl
    rw [SourceGenericPrefix.pair_payload_signs] at hl
    simp at hl
    rcases hl with rfl | rfl
    · have hv := (bitIndex v s).isLt
      change (bitIndex v s).val < M
      dsimp [M, variableBound]
      omega
    · have hv := (bitIndex v t).isLt
      change (bitIndex v t).val < M
      dsimp [M, variableBound]
      omega
  have hv := chain_valid b M (pairPayload v s t) hbase hlit
  have hlen := EncodedCNF.clauseFields_length_upper M
    (chain b (pairPayload v s t)) hv
  simpa only [payload, pairChain, List.length_reverse, b, M,
    wordBound, SourceGenericPrefix.pair_chain_length] using hlen

#print axioms pairOrdinal_le
#print axioms pair_word_length_le

end EthInapproximability.CurrentPaper.SourceGenericPairEnumeration
