import CurrentAdditive.QuarticTMClockBound
import CurrentAdditive.QuarticPacketClockBound

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticTMClockRepair
open EthInapproximability.CurrentPaper
open Paper2.CurrentAdditive.QuarticNumericFront
open Paper2.CurrentAdditive.QuarticPacketClockBound

noncomputable def packetCoefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  20 * (4 * Δ + 2) ^ (FrontClock13.cF Δ γ * 45) +
    QuarticLQClockClosed.coefficient Δ γ

theorem packet_clock_density27 (Δ : ℕ) (γ : ℚ)
    (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0 < g.vertices)
    (hmass : g.edges.length ≤ Δ * g.vertices) :
    Packet27.clock g Δ γ ≤
      packetCoefficient Δ γ * (g.vertices + 2) ^ (exponent Δ γ) := by
  let n := g.vertices
  let m := g.edges.length
  let G := (EncodedGraph.encode g).length
  let N := n + 2
  let F := FrontClock13.cF Δ γ * 45
  let X := (G + 2) ^ F
  let Y := N ^ exponent Δ γ
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hF : 1 ≤ F := by
    dsimp [F, FrontClock13.cF]
    omega
  have hGbd : FullFront.gBd γ.num.toNat γ.den Δ g + (n + m + 2) + 1 ≤ X := by
    simpa only [n, m, G, X, F] using SSSchedClock.sched_clock Δ γ g
  have hOld : Packet27.clock g Δ γ ≤ 20 * X + LQ27.clock n m Δ γ := by
    dsimp [Packet27.clock, Graph27.clock, FullFront.gBd, X, G, n, m] at *
    omega
  have hmL : m ≤ Δ * n := hmass
  have hEnc := EncodedGraph.encode_length_upper g hg
  have hEnc' : G ≤ n + 2 + m * (4 * n + 4) := by
    simpa only [G, n, m] using hEnc
  have hEdge : m * (4 * n + 4) ≤ 4 * Δ * N ^ 2 := by
    have h1 := Nat.mul_le_mul_right (4 * n + 4) hmL
    have h2 : n * (4 * n + 4) ≤ 4 * N ^ 2 := by
      dsimp [N]
      nlinarith
    have h3 := Nat.mul_le_mul_left Δ h2
    calc
      m * (4 * n + 4) ≤ (Δ * n) * (4 * n + 4) := h1
      _ = Δ * (n * (4 * n + 4)) := by ring
      _ ≤ Δ * (4 * N ^ 2) := h3
      _ = 4 * Δ * N ^ 2 := by ring
  have hEncN : G + 2 ≤ (4 * Δ + 2) * N ^ 2 := by
    have hn4 : n + 4 ≤ 2 * N ^ 2 := by
      dsimp [N]
      nlinarith
    calc
      G + 2 ≤ n + 4 + m * (4 * n + 4) := by omega
      _ ≤ 2 * N ^ 2 + 4 * Δ * N ^ 2 := Nat.add_le_add hn4 hEdge
      _ = (4 * Δ + 2) * N ^ 2 := by ring
  have hXF : X ≤ (4 * Δ + 2) ^ F * N ^ (2 * F) := by
    dsimp [X]
    calc
      (G + 2) ^ F ≤ ((4 * Δ + 2) * N ^ 2) ^ F := Nat.pow_le_pow_left hEncN F
      _ = (4 * Δ + 2) ^ F * N ^ (2 * F) := by rw [mul_pow, ← pow_mul]
  have hFpow : N ^ (2 * F) ≤ Y := by
    dsimp [Y, exponent]
    exact Nat.pow_le_pow_right hN (le_max_left _ _)
  have hLpow : N ^ 336 ≤ Y := by
    dsimp [Y, exponent]
    exact Nat.pow_le_pow_right hN (le_max_right _ _)
  have hLQ : LQ27.clock n m Δ γ ≤ QuarticLQClockClosed.coefficient Δ γ * Y :=
    (QuarticLQClockClosed.lq_clock_poly27 Δ n m γ hmL).trans
      (Nat.mul_le_mul_left _ hLpow)
  calc
    Packet27.clock g Δ γ ≤ 20 * X + LQ27.clock n m Δ γ := hOld
    _ ≤ 20 * ((4 * Δ + 2) ^ F * Y) + QuarticLQClockClosed.coefficient Δ γ * Y := by
      exact Nat.add_le_add (Nat.mul_le_mul_left 20
        (hXF.trans (Nat.mul_le_mul_left _ hFpow))) hLQ
    _ = packetCoefficient Δ γ * (g.vertices + 2) ^ (exponent Δ γ) := by
      dsimp [packetCoefficient, Y, N, F]
      ring

#print axioms packet_clock_density27

end Paper2.CurrentAdditive.QuarticTMClockRepair
