import CurrentAdditive.QuarticFixedBankLength

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open EthInapproximability.CurrentPaper

theorem squareEncodedLength_le27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) :
    squareEncodedLength27 hn edge Δ γ k ≤
      headerLength27 hn edge Δ γ k +
        (outputBits27 hn edge Δ γ k t).length + 1 := by
  have houtput := outputBits27_length hn edge Δ γ k t
  unfold squareEncodedLength27 headerLength27
  simp only [EncodedCommunication.natField,
    EncodedCommunication.field_length]
  omega

#print axioms squareEncodedLength_le27

end Paper2.CurrentAdditive.QuarticClassEndpoint
