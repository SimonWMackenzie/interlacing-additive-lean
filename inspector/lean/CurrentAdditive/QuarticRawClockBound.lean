import CurrentAdditive.QuarticRawTailClock
import CurrentAdditive.QuarticNumericRaw

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticTMClockRepair

open EthInapproximability.CurrentPaper
open Paper2.CurrentAdditive.QuarticNumericFront

noncomputable def rawCoefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  packetCoefficient Δ γ + 500 * growthCoefficient + 1

/-- Uniform clock for the literal v27 physical numeric front, including an
arbitrary raw word whose length is charged explicitly. -/
theorem raw_clock_poly27 (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ k : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hmpos : 0 < g.edges.length)
    (hm : g.edges.length ≤ Δ * g.vertices) (word : List Bool) :
    Paper2.CurrentAdditive.QuarticNumericFront.Raw27.clock g Δ γ k word ≤
      rawCoefficient Δ γ *
        ((g.vertices + 2) ^ (rawExponent Δ γ * (k + 1)) + word.length) := by
  let N := g.vertices + 2
  let B := N ^ (rawExponent Δ γ * (k + 1))
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hB1 : 1 ≤ B := Nat.one_le_pow _ _ hN
  have hEpacket :
      Paper2.CurrentAdditive.QuarticPacketClockBound.exponent Δ γ ≤
        rawExponent Δ γ := by
    dsimp only [rawExponent]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (Nat.le_succ _))
  have hEk : rawExponent Δ γ ≤ rawExponent Δ γ * (k + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hPacketPow : N ^
      (Paper2.CurrentAdditive.QuarticPacketClockBound.exponent Δ γ) ≤ B :=
    Nat.pow_le_pow_right hN (hEpacket.trans hEk)
  have hPacket : Packet27.clock g Δ γ ≤ packetCoefficient Δ γ * B :=
    (packet_clock_density27 Δ γ g hg hn hm).trans
      (Nat.mul_le_mul_left _ hPacketPow)
  have hTail : TailSource27.cost g k Δ γ word ≤
      500 * (growthCoefficient * B + word.length) := by
    simpa only [B, N] using
      tail_cost_poly27 g Δ k γ hγ hΔ hn hmpos hm word
  have hSum : Paper2.CurrentAdditive.QuarticNumericFront.Raw27.clock g Δ γ k word ≤
      packetCoefficient Δ γ * B +
        500 * (growthCoefficient * B + word.length) + 1 := by
    unfold Paper2.CurrentAdditive.QuarticNumericFront.Raw27.clock
    exact Nat.add_le_add_right (Nat.add_le_add hPacket hTail) 1
  have hCoeff : 500 ≤ rawCoefficient Δ γ := by
    have hGrow : 1 ≤ growthCoefficient := by
      dsimp [growthCoefficient]
      omega
    change 500 ≤ packetCoefficient Δ γ + 500 * growthCoefficient + 1
    omega
  calc
    Paper2.CurrentAdditive.QuarticNumericFront.Raw27.clock g Δ γ k word ≤
        packetCoefficient Δ γ * B +
          500 * (growthCoefficient * B + word.length) + 1 := hSum
    _ ≤ packetCoefficient Δ γ * B +
          500 * (growthCoefficient * B + word.length) + B := by omega
    _ = rawCoefficient Δ γ * B + 500 * word.length := by
      dsimp [rawCoefficient]
      ring
    _ ≤ rawCoefficient Δ γ * B +
          rawCoefficient Δ γ * word.length :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hCoeff) _
    _ = rawCoefficient Δ γ * (B + word.length) := by ring

#print axioms raw_clock_poly27

end Paper2.CurrentAdditive.QuarticTMClockRepair
