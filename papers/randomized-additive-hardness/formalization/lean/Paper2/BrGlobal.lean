import Paper2.BrPoly

/-! Lane a-bridge-owner-1, segment 4 (assembly): ONE fixed polynomial clock for the whole
graph stage (cut machine + admitted H_A3 machine), in `|encode g| + |word|`, for fixed
`Δ, γ, k`. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.ABridge

noncomputable section

open EthInapproximability.CurrentPaper

theorem bank3_length (g : EncodedGraph.Graph) (k : ℕ) (word : List Bool) :
    (BitMachineBankCodec.encode ![EncodedGraph.encode g, List.replicate k true, word]).length =
      2 * ((EncodedGraph.encode g).length + k + word.length) + 3 := by
  rw [BitMachineBankCodec.encode_length]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, List.length_replicate]

/-- The global exponent. -/
def gE (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) (k : ℕ) : ℕ :=
  ePk Δ γ * (k + 1) + stageEA Δ γ hΔ hγ * (k + 1) + 1

/-- The global constant (all factors fixed before the input). -/
def gC (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) (k : ℕ) : ℕ :=
  let K := nJ + 3
  let S := packetPerStep γ.num.toNat γ.den Δ
  let cn := 2 * k + 7
  let cP := 2 + prepConst + 35 + 2 * cutPS
  (K + 1) + 2 * (K + cn) + 2 + (2 * (nJ + 3 + 3) + 1) * (K + cn + 1) +
    ((6 * cn + 10) + cP + (6 * cn + 10) + (K * (cn + S * cP + 1) + 1) + 3) +
    2 * (cn + K) + 4 + 2 * (cn + K) + 2 + (2 * cn + 2 * K + 3) + 2 * cn + 2 +
    stageCA Δ γ hΔ hγ

/-- **Segment 4: one fixed polynomial clock.** -/
theorem stageClock_le (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (hm : 0 < g.edges.length)
    (k : ℕ) (hH : A3Assembly.Run.Hyp Δ g hg k)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) Δ γ)
    (word : List Bool) :
    stageClock Δ γ hΔ hγ g k word ≤
      gC Δ γ hΔ hγ k * ((EncodedGraph.encode g).length + word.length + 1) ^ gE Δ γ hΔ hγ k := by
  have hP := packetBd_graph_le Δ γ hγ hΔ g hg hn hm k hH hc word
  set X := (EncodedGraph.encode g).length + word.length + 1 with hX
  set Q := X ^ gE Δ γ hΔ hγ k with hQ
  have hX1 : 1 ≤ X := by omega
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ hX1
  have hXQ : X ≤ Q := by
    have : X ^ 1 ≤ X ^ gE Δ γ hΔ hγ k := Nat.pow_le_pow_right hX1 (by unfold gE; omega)
    simpa using this
  have hYE : ((EncodedGraph.encode g).length + 1) ^ (ePk Δ γ * (k + 1)) ≤ Q :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right hX1 (by unfold gE; omega))
  have hVA : (g.vertices + 2) ^ (stageEA Δ γ hΔ hγ * (k + 1)) ≤ Q := by
    have hY : g.vertices + 2 ≤ X := by have := EncodedGraph.encode_length_lower g; omega
    exact (Nat.pow_le_pow_left hY _).trans (Nat.pow_le_pow_right hX1 (by unfold gE; omega))
  -- abbreviations
  set K := nJ + 3 with hK
  set S := packetPerStep γ.num.toNat γ.den Δ with hS
  set cn := 2 * k + 7 with hcn
  set cP := 2 + prepConst + 35 + 2 * cutPS with hcP
  set n0 := (BitMachineBankCodec.encode
    ![EncodedGraph.encode g, List.replicate k true, word]).length with hn0def
  set P := packetBd γ.num.toNat γ.den Δ g k word with hPdef
  have hn0 : n0 = 2 * ((EncodedGraph.encode g).length + k + word.length) + 3 := bank3_length g k word
  -- n0 ≤ cn * Q
  have hkQ : k ≤ k * Q := Nat.le_mul_of_pos_right k hQ1
  have hcnQ : cn * Q = 2 * (k * Q) + 7 * Q := by rw [hcn]; ring
  have hn0Q : n0 ≤ cn * Q := by rw [hcnQ]; omega
  -- P ≤ cP * Q
  have h1 : (2 + prepConst) * ((EncodedGraph.encode g).length + 1) ^ (ePk Δ γ * (k + 1)) ≤
      (2 + prepConst) * Q := Nat.mul_le_mul_left _ hYE
  have h2 : word.length * cutPS ≤ cutPS * Q := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have hcPQ : cP * Q = (2 + prepConst) * Q + 35 * Q + 2 * (cutPS * Q) := by rw [hcP]; ring
  have hPQ : P ≤ cP * Q := by rw [hcPQ]; omega
  -- products
  have hSP : S * P ≤ S * (cP * Q) := Nat.mul_le_mul_left _ hPQ
  have hKin : K * (n0 + S * P + 1) ≤ K * ((cn + S * cP + 1) * Q) := by
    apply Nat.mul_le_mul_left
    have e : (cn + S * cP + 1) * Q = cn * Q + S * (cP * Q) + Q := by ring
    rw [e]; omega
  have hWin : (2 * (nJ + 3 + 3) + 1) * (nJ + 3 + n0 + 1) ≤
      (2 * (nJ + 3 + 3) + 1) * ((K + cn + 1) * Q) := by
    apply Nat.mul_le_mul_left
    have e : (K + cn + 1) * Q = K * Q + cn * Q + Q := by ring
    have hKQ : K ≤ K * Q := Nat.le_mul_of_pos_right K hQ1
    rw [e]; omega
  have hCA : stageCA Δ γ hΔ hγ * (g.vertices + 2) ^ (stageEA Δ γ hΔ hγ * (k + 1)) ≤
      stageCA Δ γ hΔ hγ * Q := Nat.mul_le_mul_left _ hVA
  have hKQ : K ≤ K * Q := Nat.le_mul_of_pos_right K hQ1
  -- the clock, unfolded
  have hclk : stageClock Δ γ hΔ hγ g k word =
      ((nJ + 3 + 1) + 2 * (nJ + 3 + n0) + 2 +
        (((2 * (nJ + 3 + 3) + 1) * ((nJ + 3 + n0) + 1) +
          ((6 * n0 + 10) + P + (6 * n0 + 10) + (K * (n0 + S * P + 1) + 1) + 3) +
          2 * (n0 + (nJ + 3)) + 4) +
         2 * (n0 + (nJ + 3)) + 2 + (2 * n0 + 2 * (nJ + 3) + 3))) +
      2 * n0 + 2 + stageCA Δ γ hΔ hγ * (g.vertices + 2) ^ (stageEA Δ γ hΔ hγ * (k + 1)) := rfl
  have hC : gC Δ γ hΔ hγ k * Q =
      (K + 1) * Q + 2 * (K * Q + cn * Q) + 2 * Q +
        (2 * (nJ + 3 + 3) + 1) * ((K + cn + 1) * Q) +
        ((6 * (cn * Q) + 10 * Q) + cP * Q + (6 * (cn * Q) + 10 * Q) +
          (K * ((cn + S * cP + 1) * Q) + Q) + 3 * Q) +
        2 * (cn * Q + K * Q) + 4 * Q + 2 * (cn * Q + K * Q) + 2 * Q +
        (2 * (cn * Q) + 2 * (K * Q) + 3 * Q) + 2 * (cn * Q) + 2 * Q +
        stageCA Δ γ hΔ hγ * Q := by
    unfold gC; ring
  rw [hclk, hC]
  have hK1 : (K + 1) * Q = K * Q + Q := by ring
  rw [hK1]
  omega

#print axioms stageClock_le

end

end Paper2.ABridge
