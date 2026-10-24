import CurrentAdditive.CylinderEvalPairMachine
import CurrentAdditive.CylinderActualTupleRow
import CurrentAdditive.CylinderGeneralFeatureSemanticBare

/-! The concrete pair tester has one cubic clock in its actual contextual
input bytes. In particular, its binary coordinate expansion is paid by the
literal unary q field, not by an unbounded binary value. -/

namespace CurrentAdditive.CylinderEvalPairMachine

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec

theorem input_lengths {q : ℕ} (v : Fin q → ℕ) (i : Fin q) (y : ℕ) :
    q≤(input v i y).length ∧ (tupleWord v).length≤(input v i y).length ∧
      i.val.bits.length≤(input v i y).length ∧ y.bits.length≤(input v i y).length := by
  let context := encode ![List.replicate q true,tupleWord v]
  let pair := encode ![i.val.bits,y.bits]
  have hctx := word_length_le_encode (![context,pair]) (0 : Fin 2)
  have hpair := word_length_le_encode (![context,pair]) (1 : Fin 2)
  change context.length≤(input v i y).length at hctx
  change pair.length≤(input v i y).length at hpair
  have hq := word_length_le_encode (![List.replicate q true,tupleWord v]) (0 : Fin 2)
  have ht := word_length_le_encode (![List.replicate q true,tupleWord v]) (1 : Fin 2)
  have hi := word_length_le_encode (![i.val.bits,y.bits]) (0 : Fin 2)
  have hy := word_length_le_encode (![i.val.bits,y.bits]) (1 : Fin 2)
  change (List.replicate q true).length≤context.length at hq
  change (tupleWord v).length≤context.length at ht
  change i.val.bits.length≤pair.length at hi
  change y.bits.length≤pair.length at hy
  simpa only [List.length_replicate] using
    And.intro (hq.trans hctx) (And.intro (ht.trans hctx) (And.intro (hi.trans hpair) (hy.trans hpair)))

theorem pairBound_polynomial {q : ℕ} (v : Fin q → ℕ) (i : Fin q) (y : ℕ) :
    pairBound v i y≤64*((input v i y).length+1)^3 := by
  let xs := List.ofFn (fun j : Fin q => (v j).bits)
  obtain ⟨hsplit,_⟩ := CylinderActualTupleRow.canonical_tuple_split (v,(0 : ℚ)) i
  have hjoin : (xs.take i.val++[(v i).bits])++xs.drop (i.val+1)=xs := by
    simpa only [List.append_assoc,List.singleton_append] using hsplit.symm
  have hf := GaussListContext.IndexedV2Clock.fieldCost_prefix_le
    (xs.take i.val++[(v i).bits]) (xs.drop (i.val+1))
  rw [hjoin] at hf
  change GaussListContext.IndexedFieldProgram.fieldCost (xs.take i.val++[(v i).bits])≤
    25*((tupleWord v).length+1)^3 at hf
  obtain ⟨hq,ht,hi,hy⟩ := input_lengths v i y
  have hf' := hf.trans (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.add_le_add_right ht 1) 3))
  have hbits := UnaryBinaryEncoding.bits_length_le q
  have hindex := i.isLt
  have hmin : min (v i).bits.length y.bits.length≤y.bits.length := min_le_right _ _
  have hlinear : (input v i y).length+1≤((input v i y).length+1)^3 :=
    le_self_pow (by omega) (by decide)
  unfold pairBound
  simp only [List.length_ofFn] at *
  change 2*i.val+5+(2*(tupleWord v).length+5+
    (4*q.bits.length+6+GaussListContext.IndexedFieldProgram.fieldCost (xs.take i.val++[(v i).bits])))+
    1+(min (v i).bits.length y.bits.length+1)+1≤_
  nlinarith

theorem clock_polynomial {q : ℕ} (v : Fin q → ℕ) (i : Fin q) (y : ℕ) :
    clock v i y≤128*((input v i y).length+1)^3 := by
  obtain ⟨hq,ht,hi,hy⟩ := input_lengths v i y
  have hp := pairBound_polynomial v i y
  let N := (input v i y).length+1
  have hN : 1≤N := by dsimp [N]; omega
  have hconv := Nat.mul_le_mul (Nat.add_le_add_right hq 1)
    (show 4*i.val.bits.length+5≤5*N by dsimp [N]; omega)
  have hpow : N^2≤N^3 := by nlinarith
  have hlin : N≤N^3 := le_self_pow hN (by decide)
  change (q+1)*(4*i.val.bits.length+5)≤N*(5*N) at hconv
  dsimp [clock]
  change 18*N+1+(q+1)*(4*i.val.bits.length+5)+1+pairBound v i y≤128*N^3
  change pairBound v i y≤64*N^3 at hp
  nlinarith

theorem outputs_polynomial {q : ℕ} (v : Fin q → ℕ) (i : Fin q) (y : ℕ) :
    machine.OutputsWithin (input v i y) [decide (v i=y)]
      (128*((input v i y).length+1)^3) :=
  BitMachine.outputsWithin_mono machine (outputs v i y) (clock_polynomial v i y)

def context {q : ℕ} (v : Fin q → ℕ) : List Bool :=
  encode ![List.replicate q true,tupleWord v]

theorem pair_bytes (p : ℕ × ℕ) :
    CylinderFeatureCodec.encodePair p=encode ![p.1.bits,p.2.bits] := by
  unfold CylinderFeatureCodec.encodePair
  congr 1
  funext k
  fin_cases k <;> rfl

theorem input_context_pair {q : ℕ} (v : Fin q → ℕ) (p : ℕ × ℕ) (hp : p.1<q) :
    input v ⟨p.1,hp⟩ p.2=encode ![context v,CylinderFeatureCodec.encodePair p] := by
  rw [pair_bytes]
  rfl

theorem contextual_outputs {q : ℕ} (v : Fin q → ℕ) (p : ℕ × ℕ) (hp : p.1<q) :
    machine.OutputsWithin (encode ![context v,CylinderFeatureCodec.encodePair p])
      [CylinderGeneralFeatureSemanticBare.pairMatches v p]
      (128*((encode ![context v,CylinderFeatureCodec.encodePair p]).length+1)^3) := by
  have h := outputs_polynomial v ⟨p.1,hp⟩ p.2
  rw [input_context_pair] at h
  simpa only [CylinderGeneralFeatureSemanticBare.pairMatches,dif_pos hp] using h

end CurrentAdditive.CylinderEvalPairMachine

#print axioms CurrentAdditive.CylinderEvalPairMachine.outputs_polynomial
