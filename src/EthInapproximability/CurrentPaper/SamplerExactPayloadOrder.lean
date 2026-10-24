import EthInapproximability.CurrentPaper.SamplerMachineFieldTable
import EthInapproximability.CurrentPaper.MatrixMaterialization

/-!
# Exact NP sampler bit order in the stored payload

The binary-field word uses low-bit-first coordinates. The exact-NP matrix
serializer's word code is most-significant-bit first. The second payload
therefore reverses the bits inside every fixed-width alphabet symbol but
does not reverse seed or symbol order.

Source: locked v8 Appendix E, `lem:exact-families`, and Appendix B's
row-major exact-data materialization.
-/

namespace EthInapproximability.CurrentPaper.SamplerExactPayloadOrder

open ExecutableSmallBiasSampler SamplerMachine

private theorem finTwo_encodeBit (b : ZMod 2) :
    finTwoEquiv.symm (encodeBit b) = (ZMod.finEquiv 2).toEquiv.symm b := by
  fin_cases b <;> decide

private theorem first_symbol (b : ZMod 2) :
    finTwoEquiv (blockAlphabetEquiv 1 (fun _ => b)) = encodeBit b := by
  fin_cases b <;> decide

theorem wordCode_block (a : ℕ) (f : Fin a → ZMod 2) (j : Fin a) :
    (MatrixMaterialization.wordCode a).symm (blockAlphabetEquiv a f) j =
      encodeBit (f j.rev) := by
  suffices h : MatrixMaterialization.wordCode a (fun j : Fin a => encodeBit (f j.rev)) =
      blockAlphabetEquiv a f by
    rw [← h, Equiv.symm_apply_apply]
  unfold MatrixMaterialization.wordCode MatrixMaterialization.tupleCode blockAlphabetEquiv
  simp only [Equiv.trans_apply]
  congr 1
  funext k
  simp [Equiv.arrowCongr, finTwo_encodeBit]

theorem second_payload_entry (a t₁ t₂ d n : ℕ)
    (v : Fin n → Fin d → Bool)
    (z : Fin (SmallBiasSampler.exactSecondSize a t₂ d))
    (α : Fin d) (j : Fin a) :
    ((MatrixMaterialization.storeBits
      (exactFirstFamily a t₁ d) (exactSecondFamily a t₂ d) v).second)[(z.val * d + α.val) * a + j.val]? =
    some (encodeBit (indexedTraceBits (d * a)
      (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t₂) z
        (finProdFinEquiv (α, j.rev)))) := by
  rw [MatrixMaterialization.storeBits_second_entry]
  exact congrArg some (wordCode_block a
    (fun r => indexedTraceBits (d * a)
      (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t₂) z
      (finProdFinEquiv (α, r))) j)

theorem first_family_bit (a t d : ℕ)
    (z : Fin (SmallBiasSampler.exactFirstSize a t d))
    (i : Fin (ExactConstruction.prefixLength a + 3)) :
    exactFirstFamily a t d z i =
      encodeBit (indexedTraceBits
        ((ExactConstruction.prefixLength a + 3) * 1)
        (SmallBiasSampler.exactDenominator d * (2 ^ 1) ^ t) z
        (finProdFinEquiv (i, (0 : Fin 1)))) := by
  change finTwoEquiv (blockAlphabetEquiv 1
    (fun r : Fin 1 => indexedTraceBits
      ((ExactConstruction.prefixLength a + 3) * 1)
      (SmallBiasSampler.exactDenominator d * (2 ^ 1) ^ t) z
      (finProdFinEquiv (i, r)))) = _
  have hf : (fun r : Fin 1 => indexedTraceBits
      ((ExactConstruction.prefixLength a + 3) * 1)
      (SmallBiasSampler.exactDenominator d * (2 ^ 1) ^ t) z
      (finProdFinEquiv (i, r))) =
      fun _ => indexedTraceBits
        ((ExactConstruction.prefixLength a + 3) * 1)
        (SmallBiasSampler.exactDenominator d * (2 ^ 1) ^ t) z
        (finProdFinEquiv (i, (0 : Fin 1))) := by
    funext r
    have hr : r = 0 := Subsingleton.elim _ _
    rw [hr]
  rw [hf]
  exact first_symbol _

theorem first_payload_entry (a t₁ t₂ d n : ℕ)
    (v : Fin n → Fin d → Bool)
    (z : Fin (SmallBiasSampler.exactFirstSize a t₁ d))
    (i : Fin (ExactConstruction.prefixLength a + 3)) :
    ((MatrixMaterialization.storeBits
      (exactFirstFamily a t₁ d) (exactSecondFamily a t₂ d) v).first)[z.val * (ExactConstruction.prefixLength a + 3) + i.val]? =
    some (encodeBit (indexedTraceBits
      ((ExactConstruction.prefixLength a + 3) * 1)
      (SmallBiasSampler.exactDenominator d * (2 ^ 1) ^ t₁) z
      (finProdFinEquiv (i, (0 : Fin 1))))) := by
  have hrow := MatrixMaterialization.rowMajor_entry
    (exactFirstFamily a t₁ d) z i
  change (MatrixMaterialization.rowMajor (exactFirstFamily a t₁ d))[z.val * (ExactConstruction.prefixLength a + 3) + i.val]? = _
  rw [hrow, first_family_bit]

end EthInapproximability.CurrentPaper.SamplerExactPayloadOrder
