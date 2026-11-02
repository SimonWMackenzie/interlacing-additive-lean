import CurrentAdditive.V40RawRequestPacket
import CurrentAdditive.V40BlockTapeLaw
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CurrentAdditive.V40SourceBlockView
noncomputable section
open Paper2 EthInapproximability.CurrentPaper

/-- Total finite prefixBits view, agreeing with the physical ticket order. -/
def prefixBits (word : List Bool) (r : ℕ) : Fin r → Bool := fun i => word.getD i.val false

theorem prefix_eq (word : List Bool) (r : ℕ) (hr : r ≤ word.length) :
    prefixBits word r = V40ClassifierTail.prefixFn word r hr := by
  funext i
  unfold prefixBits V40ClassifierTail.prefixFn
  have hi : i.val < word.length := lt_of_lt_of_le i.isLt hr
  rw [List.getD_eq_getElem word false hi]
  simp

theorem prefix_word (word : List Bool) (r : ℕ) (hr : r ≤ word.length) :
    List.ofFn (prefixBits word r) = word.take r := by
  rw [prefix_eq word r hr]
  exact V40ClassifierTail.prefix_word word r hr

def bits (b N : ℕ) (word : List Bool) : RoundedDraw.BitBlocks b N :=
  (V40BlockTapeLaw.blocksEquiv b N).symm (prefixBits word (b*N))

theorem bits_word (b N : ℕ) (word : List Bool) (h : b*N ≤ word.length) :
    RoundedCodeLoop.tapeWord b N (bits b N word) = word.take (b*N) := by
  rw [bits,V40BlockTapeLaw.blocksEquiv_symm_word,prefix_word word (b*N) h]

theorem word_view (b N : ℕ) (word : List Bool) (h : b*N ≤ word.length) :
    RoundedCodeLoop.tapeWord b N (bits b N word) ++ word.drop (b*N) = word := by
  rw [bits_word b N word h,List.take_append_drop]

theorem bits_eq_prefixFn (b N : ℕ) (word : List Bool) (h : b*N ≤ word.length) :
    bits b N word = (V40BlockTapeLaw.blocksEquiv b N).symm
      (V40ClassifierTail.prefixFn word (b*N) h) := by
  rw [bits,prefix_eq word (b*N) h]

end
end CurrentAdditive.V40SourceBlockView
#print axioms CurrentAdditive.V40SourceBlockView.word_view
