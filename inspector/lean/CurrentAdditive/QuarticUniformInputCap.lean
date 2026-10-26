import CurrentAdditive.QuarticPairUniform
import CurrentAdditive.QuarticRawClockBound

/-! One tape-independent cap for the encoded numeric input and its raw clock. -/

namespace Paper2.CurrentAdditive.QuarticUniformInputCap

open EthInapproximability.CurrentPaper
open Paper2.CurrentAdditive.QuarticNumericFront
open Paper2.CurrentAdditive.QuarticTMClockRepair

noncomputable section
set_option maxHeartbeats 8000000

def inputCap (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k L : ℕ) : ℕ :=
  4 + 2 * ((EncodedGraph.encode g).length + k + L) +
    rawCoefficient Δ γ *
      ((g.vertices + 2) ^ (rawExponent Δ γ * (k + 1)) + L)

theorem encoded_input_le (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k L : ℕ) (raw : List Bool) (hraw : raw.length ≤ L) :
    (BitMachineBankCodec.encode (FullFront.X0 g k raw)).length ≤
      inputCap g Δ γ k L := by
  rw [BitMachineBankCodec.encode_length]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp [FullFront.X0, inputCap] at *
  omega

theorem raw_clock_le (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hmpos : 0 < g.edges.length)
    (hm : g.edges.length ≤ Δ * g.vertices)
    (k L : ℕ) (raw : List Bool) (hraw : raw.length ≤ L) :
    Raw27.clock g Δ γ k raw ≤ inputCap g Δ γ k L := by
  have h := raw_clock_poly27 g hg Δ k γ hγ hΔ hn hmpos hm raw
  dsimp [inputCap]
  nlinarith [Nat.mul_le_mul_left (rawCoefficient Δ γ)
    (Nat.add_le_add_left hraw
      ((g.vertices + 2) ^ (rawExponent Δ γ * (k + 1))))]

theorem inputCap_pos (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k L : ℕ) : 1 ≤ inputCap g Δ γ k L := by
  dsimp [inputCap]
  omega

#print axioms encoded_input_le
#print axioms raw_clock_le
#print axioms inputCap_pos

end
end Paper2.CurrentAdditive.QuarticUniformInputCap
