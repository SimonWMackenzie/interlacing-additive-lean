import CurrentAdditive.QuarticCutterClockBound
import CurrentAdditive.QuarticOuterClockLinear
import CurrentAdditive.QuarticClockArithmetic
import CurrentAdditive.QuarticInputCapAtoms

/-! A two-term source-size clock for the exact v27 physical cut. -/

namespace Paper2.CurrentAdditive.QuarticSourceCutClock

open EthInapproximability.CurrentPaper
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticTMClockRepair
open Paper2.CurrentAdditive.QuarticCutterClockBound
open Paper2.CurrentAdditive.QuarticOuterClockLinear

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def cutNumericCoefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  outerClockCoefficient Δ γ *
    (2 * (rawCoefficient Δ γ + 10) + cutCoefficient + 2)

theorem cut_clock_of_numeric_atoms
    (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (raw : List Bool) (Y : Fin 3 → List Bool) (Z Praw Pcut : ℕ)
    (hZ : Z = 4 + 2 * ((EncodedGraph.encode g).length + k + raw.length) +
      rawCoefficient Δ γ * (Praw + raw.length))
    (hPcut : QuarticRawPrefixCutter.clock g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ k raw ≤
      cutCoefficient * (Pcut + raw.length + 1)) :
    let O := (BitMachineBankCodec.encode Y).length
    let S := Praw + Pcut + (EncodedGraph.encode g).length + k +
      raw.length + O + 1
    QuarticOuterMachine.cutClock (FullFront.X0 g k raw) Y
      (QuarticOuterUniform.localCap g Δ γ k raw Z) ≤
      cutNumericCoefficient Δ γ * S := by
  intro O S
  let I := (BitMachineBankCodec.encode (FullFront.X0 g k raw)).length
  let R := QuarticRawPrefixCutter.clock g.vertices g.edges.length
    (Nat.clog 2 g.vertices) Δ γ k raw
  let W := Z + R + I + O + 1
  have hI : I ≤ Z := by
    dsimp only [I]
    rw [hZ]
    rw [BitMachineBankCodec.encode_length]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp [FullFront.X0]
    omega
  have hW : W ≤
      (2 * (rawCoefficient Δ γ + 10) + cutCoefficient + 2) * S :=
    QuarticClockArithmetic.affine_combine
      (rawCoefficient Δ γ) cutCoefficient Z R I O Praw Pcut
      (EncodedGraph.encode g).length k raw.length S rfl hZ hI hPcut
  have hclock := cut_clock_linear g Δ γ k raw Y Z
  have hclock' : QuarticOuterMachine.cutClock (FullFront.X0 g k raw) Y
      (QuarticOuterUniform.localCap g Δ γ k raw Z) ≤
      outerClockCoefficient Δ γ * W := by
    change QuarticOuterMachine.cutClock (FullFront.X0 g k raw) Y
        (QuarticOuterUniform.localCap g Δ γ k raw Z) ≤
      outerClockCoefficient Δ γ * (Z + R + I + O + 1) at hclock
    exact hclock
  calc
    _ ≤ outerClockCoefficient Δ γ * W := hclock'
    _ ≤ outerClockCoefficient Δ γ *
          ((2 * (rawCoefficient Δ γ + 10) + cutCoefficient + 2) * S) :=
      Nat.mul_le_mul_left _ hW
    _ = cutNumericCoefficient Δ γ * S := by
      rw [cutNumericCoefficient]
      ring

#print axioms cut_clock_of_numeric_atoms

end
end Paper2.CurrentAdditive.QuarticSourceCutClock
