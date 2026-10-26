import CurrentAdditive.GraphUnaryPrinter

namespace Paper2.CurrentAdditive.GraphUnaryPrinter

open EthInapproximability.CurrentPaper

theorem fieldCost_le (u n : ℕ) (hu : u ≤ n) :
    SourceNormalizationMachineEndpointWriter.fieldCost u ≤
      (UnaryBinaryEncoding.coefficient + 3) * (n + 1)^2 := by
  have hb := UnaryBinaryEncoding.bits_length_le u
  have hs : (u + 1)^2 ≤ (n + 1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hc := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hs
  have hn : n + 1 ≤ (n + 1)^2 := by nlinarith
  unfold SourceNormalizationMachineEndpointWriter.fieldCost
  nlinarith

theorem edgesCost_le (ps : List (ℕ × ℕ)) (n : ℕ)
    (h : ∀ p ∈ ps, p.1 ≤ n ∧ p.2 ≤ n) :
    SourceNormalizationMachineEndpointWriter.edgesCost ps ≤
      ps.length * (2 * (UnaryBinaryEncoding.coefficient + 4) * (n + 1)^2) := by
  induction ps with
  | nil => simp [SourceNormalizationMachineEndpointWriter.edgesCost]
  | cons p ps ih =>
      obtain ⟨hu, hv⟩ := h p (by simp)
      have ha := fieldCost_le p.1 n hu
      have hb := fieldCost_le p.2 n hv
      have hc := ih (fun q hq => h q (by simp [hq]))
      have hone : 1 ≤ (n + 1)^2 := by nlinarith
      simp only [SourceNormalizationMachineEndpointWriter.edgesCost,
        SourceNormalizationMachineEndpointWriter.edgeCost, List.length_cons]
      nlinarith

theorem totalBound_polynomial (g : EncodedGraph.Graph) (hg : g.Valid) :
    totalBound g ≤ (4 * UnaryBinaryEncoding.coefficient + 30) *
      (g.vertices + g.edges.length + 1)^3 := by
  let s := g.vertices + g.edges.length + 1
  have hn : g.vertices + 1 ≤ s := by omega
  have hm : g.edges.length + 1 ≤ s := by omega
  have hs : 1 ≤ s := by omega
  have he := edgesCost_le g.edges g.vertices (by
    intro p hp
    obtain ⟨hu, hv, _⟩ := hg p hp
    exact ⟨hu.le, hv.le⟩)
  have hp := EncodedGraph.edgeFields_length_upper g.vertices g.edges (by
    intro p hp
    obtain ⟨hu, hv, _⟩ := hg p hp
    exact ⟨hu, hv⟩)
  have hb := UnaryBinaryEncoding.bits_length_le g.edges.length
  have hm2 : (g.edges.length + 1)^2 ≤ s^2 := Nat.pow_le_pow_left hm 2
  have hn2 : (g.vertices + 1)^2 ≤ s^2 := Nat.pow_le_pow_left hn 2
  have he' : SourceNormalizationMachineEndpointWriter.edgesCost g.edges ≤
      2 * (UnaryBinaryEncoding.coefficient + 4) * s^3 := by
    calc
      _ ≤ g.edges.length * (2 * (UnaryBinaryEncoding.coefficient + 4) * (g.vertices + 1)^2) := he
      _ ≤ s * (2 * (UnaryBinaryEncoding.coefficient + 4) * s^2) := by gcongr <;> omega
      _ = _ := by ring
  have hp' : (EncodedGraph.edgeFields g.edges).length ≤ 6 * s^2 := by
    calc
      _ ≤ g.edges.length * (4 * g.vertices + 2) := hp
      _ ≤ s * (6 * s) := by gcongr <;> omega
      _ = _ := by ring
  have hc := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hm2
  have hss : s^2 ≤ s^3 := by nlinarith
  have hs2 : s ≤ s^2 := by nlinarith
  have hs3 : s ≤ s^3 := hs2.trans hss
  have hc' := hc.trans (Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hss)
  have hp'' := hp'.trans (Nat.mul_le_mul_left 6 hss)
  have hlo : 3 * g.edges.length.bits.length + g.vertices + 6 ≤ 10 * s^3 := by omega
  unfold totalBound finalizerTime
  change _ ≤ (4 * UnaryBinaryEncoding.coefficient + 30) * s^3
  nlinarith

#print axioms totalBound_polynomial

end Paper2.CurrentAdditive.GraphUnaryPrinter
