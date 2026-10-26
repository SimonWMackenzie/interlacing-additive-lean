import CurrentAdditive.QuarticOutputSize
import CurrentAdditive.QuarticSquareMachine

/-! A fixed polynomial clock for the v27 printer followed by square padding. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.CurrentAdditive.QuarticMachineWrapper

private theorem output_plus_one_bound (N k w : ℕ) (hN : 2 ≤ N)
    (hw : w ≤ N ^ (164 * (k + 1))) :
    w + 1 ≤ N ^ (165 * (k + 1)) := by
  have hP : 1 ≤ N ^ (164 * (k + 1)) := Nat.one_le_pow _ _ (by omega)
  have h2 : 2 * N ^ (164 * (k + 1)) ≤
      N * N ^ (164 * (k + 1)) := Nat.mul_le_mul_right _ hN
  have hE : N * N ^ (164 * (k + 1)) =
      N ^ (164 * (k + 1) + 1) := by rw [pow_succ]; ring
  calc
    w + 1 ≤ 2 * N ^ (164 * (k + 1)) := by omega
    _ ≤ N * N ^ (164 * (k + 1)) := h2
    _ = N ^ (164 * (k + 1) + 1) := hE
    _ ≤ N ^ (165 * (k + 1)) :=
      Nat.pow_le_pow_right (by omega) (by omega)

theorem H_square_poly_27_of_H_A3 (Δ : ℕ) (γ : ℚ)
    (hA : H_A3_27 Δ γ) :
    ∃ (MA : BitMachine.Machine) (CA EA : ℕ),
      ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ),
        QuarticDispatchSpec.Hyp Δ g hg k →
        ∀ t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape,
          MA.OutputsWithin
            (BitMachineBankCodec.encode
              (QuarticDispatchSpec.inputBank27 Δ γ g hg hn k t))
            (EncodedCommunication.encodeInstance
              (Paper2.ASquare.squareInstance
                (selectedInstance27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k t)))
            (CA * (g.vertices + 2) ^ (EA * (k + 1))) := by
  obtain ⟨M, C, E, hM⟩ := H_square_27_of_H_A3 Δ γ hA
  let E' := max E (165 * (Paper2.ASquare.Post.squareEP + 1))
  refine ⟨M, C + 4 + Paper2.ASquare.Post.squareCP, E', ?_⟩
  intro g hg hn k hH t
  let N := g.vertices + 2
  let w := outputBits27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k t
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hlen : w.length ≤ N ^ (164 * (k + 1)) :=
    outputBits27_length_le_poly hn _ Δ γ k hH.1 t
  have hlen1 := output_plus_one_bound N k w.length hN hlen
  have hbase : 1 ≤ N := by omega
  have he : E * (k + 1) ≤ E' * (k + 1) :=
    Nat.mul_le_mul_right _ (le_max_left _ _)
  have h164 : 164 * (k + 1) ≤ E' * (k + 1) := by
    have h := le_max_right E (165 * (Paper2.ASquare.Post.squareEP + 1))
    exact Nat.mul_le_mul_right _ (by dsimp [E']; omega)
  have hpostE : 165 * (k + 1) * Paper2.ASquare.Post.squareEP ≤
      E' * (k + 1) := by
    have h := le_max_right E (165 * (Paper2.ASquare.Post.squareEP + 1))
    have h' : 165 * Paper2.ASquare.Post.squareEP ≤ E' := by
      dsimp [E']
      omega
    have hm := Nat.mul_le_mul_right (k + 1) h'
    nlinarith only [hm]
  have h1 : C * N ^ (E * (k + 1)) ≤ C * N ^ (E' * (k + 1)) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hbase he)
  have h2 : 2 * w.length ≤ 2 * N ^ (E' * (k + 1)) :=
    Nat.mul_le_mul_left _ (hlen.trans (Nat.pow_le_pow_right hbase h164))
  have h3 : 2 ≤ 2 * N ^ (E' * (k + 1)) := by
    have hh : 1 ≤ N ^ (E' * (k + 1)) := Nat.one_le_pow _ _ hbase
    omega
  have h4 : Paper2.ASquare.Post.squareCP * (w.length + 1) ^
      Paper2.ASquare.Post.squareEP ≤
      Paper2.ASquare.Post.squareCP * N ^ (E' * (k + 1)) := by
    have hp := Nat.pow_le_pow_left hlen1 Paper2.ASquare.Post.squareEP
    rw [← pow_mul] at hp
    exact Nat.mul_le_mul_left _
      (hp.trans (Nat.pow_le_pow_right hbase hpostE))
  have hrun := hM g hg hn k hH t
  apply BitMachine.outputsWithin_mono _ hrun
  change C * N ^ (E * (k + 1)) + 2 * w.length + 2 +
    Paper2.ASquare.Post.squareCP * (w.length + 1) ^ Paper2.ASquare.Post.squareEP ≤
      (C + 4 + Paper2.ASquare.Post.squareCP) * N ^ (E' * (k + 1))
  nlinarith only [h1, h2, h3, h4]

#print axioms H_square_poly_27_of_H_A3

end Paper2.CurrentAdditive.QuarticClassEndpoint
