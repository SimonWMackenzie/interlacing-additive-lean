import CurrentAdditive.GenericBitvectorPaddedLookup
import Paper2.RecursiveLabelCodec

/-! A supplied base table for the graph-loop carrier. Rows use the exact
big-endian address computed by `MatrixBinaryAddress`; column zero is padding
because `finCodec` appends its false terminator. This is a different order
from the inherited indexed seed printer's little-endian `seedRow` order. -/

namespace Paper2.GenericBitvectorPaddedTable

open EthInapproximability.CurrentPaper
open Paper2.RecursiveLabelCodecScratch

def paddedMatrix (p : ℕ) (F : (Fin p → Bool) → Fin p → Bool) :
    Fin (2 ^ p) → Fin (p + 1) → Bool :=
  fun i c => if h : c.val = 0 then false
    else F ((MatrixMaterialization.wordCode p).symm i)
      ⟨c.val - 1, by have := c.isLt; omega⟩

def paddedBits (p : ℕ) (F : (Fin p → Bool) → Fin p → Bool) :
    List Bool := MatrixMaterialization.rowMajor (paddedMatrix p F)

theorem paddedBits_length (p : ℕ)
    (F : (Fin p → Bool) → Fin p → Bool) :
    (paddedBits p F).length = 2 ^ p * (p + 1) := by
  exact MatrixMaterialization.rowMajor_length _

theorem paddedBits_entry (p : ℕ)
    (F : (Fin p → Bool) → Fin p → Bool)
    (x : Fin p → Bool) (j : Fin p) :
    (paddedBits p F)[
      MatrixBinaryAddress.valueFrom 0 (List.ofFn x) * (p + 1) +
        ((finCodec p).encode j).length]?.getD false = F x j := by
  have hrow := MatrixBinaryAddress.valueFrom_wordCode p x
  have hcol : ((finCodec p).encode j).length = j.val + 1 := by
    simp [finCodec]
  rw [hrow, hcol]
  let c : Fin (p + 1) := ⟨j.val + 1, by omega⟩
  have he := MatrixMaterialization.rowMajor_entry (paddedMatrix p F)
    (MatrixMaterialization.wordCode p x) c
  change (paddedBits p F)[(MatrixMaterialization.wordCode p x).val * (p + 1) +
    (j.val + 1)]? = some (paddedMatrix p F (MatrixMaterialization.wordCode p x) c) at he
  rw [he]
  simp [paddedMatrix, c]

#print axioms paddedBits_entry

end Paper2.GenericBitvectorPaddedTable
