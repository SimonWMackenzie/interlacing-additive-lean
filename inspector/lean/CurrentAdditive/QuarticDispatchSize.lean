import CurrentAdditive.QuarticDispatchSpec
import Paper2.A3H3Size

/-! The actual v27 selected input packet has fixed-polynomial encoded length. -/

namespace Paper2.CurrentAdditive.QuarticDispatchSize

open EthInapproximability.CurrentPaper
open Paper2
open Paper2.CurrentAdditive.QuarticDispatchSpec

private theorem k_le_pow (n k : ℕ) : k ≤ (n + 2) ^ (160 * (k + 1)) := by
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : 2 ^ k ≤ (n + 2) ^ k := Nat.pow_le_pow_left (by omega) k
  have h3 : (n + 2) ^ k ≤ (n + 2) ^ (160 * (k + 1)) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

private theorem sq_le_pow (n k : ℕ) : (n + 2) ^ 2 ≤ (n + 2) ^ (160 * (k + 1)) :=
  Nat.pow_le_pow_right (by omega) (by omega)

private theorem size_arith (n m Δ k G W X : ℕ)
    (hG : G ≤ n + 2 + m * (4 * n + 4)) (hm : 2 * m ≤ Δ * n)
    (hW : W ≤ X) (hk : k ≤ X) (hY : (n + 2) ^ 2 ≤ X) :
    2 * (G + k + W) + 3 ≤ (4 * Δ + 9) * X := by
  have hY' : (n + 2) * (n + 2) ≤ X := by simpa only [pow_two] using hY
  have hmn : m * (4 * n + 4) ≤ 2 * Δ * ((n + 2) * (n + 2)) := by
    have : m * (4 * n + 4) = (2 * m) * (2 * n + 2) := by ring
    rw [this]
    calc (2 * m) * (2 * n + 2) ≤ (Δ * n) * (2 * n + 2) := Nat.mul_le_mul_right _ hm
      _ ≤ 2 * Δ * ((n + 2) * (n + 2)) := by nlinarith
  have hmX : m * (4 * n + 4) ≤ 2 * Δ * X :=
    hmn.trans (Nat.mul_le_mul_left _ hY')
  have hn2 : n + 2 ≤ X := by nlinarith
  have hX1 : 1 ≤ X := by omega
  nlinarith

/-- The v27 selected input bank, including graph, parameter and the actual selected tape,
fits the fixed polynomial used by the source machine model. -/
theorem inputSize27 (Δ : ℕ) (γ : ℚ) : InputSize27 Δ γ (4 * Δ + 9) 160 := by
  intro g hg hn k hH t
  obtain ⟨hk, _, hdeg⟩ := hH
  rw [BitMachineBankCodec.encode_length]
  simp only [inputBank27, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, List.length_replicate]
  have hG := EncodedGraph.encode_length_upper g hg
  have hm := Paper2.A3Assembly.Size.twice_edges_le g hg hn Δ hdeg
  have hW :
      ((QuarticConstructor.select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t).length ≤
        (g.vertices + 2) ^ (160 * (k + 1)) := by
    rw [QuarticInputSize.tapeBits_length27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k t]
    exact (QuarticInputSize.selected_announced_counts_le27 hn
      (CanonicalEdgeTape.graphEdge g hg) Δ γ k hk).2
  exact size_arith g.vertices g.edges.length Δ k _ _ _ hG hm hW
    (k_le_pow g.vertices k) (sq_le_pow g.vertices k)

#print axioms inputSize27

end Paper2.CurrentAdditive.QuarticDispatchSize
