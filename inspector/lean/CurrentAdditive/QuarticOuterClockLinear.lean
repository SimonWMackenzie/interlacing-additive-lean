import CurrentAdditive.QuarticOuterUniform

/-! Literal affine dependence of the physical outer cut on its charged words. -/

namespace Paper2.CurrentAdditive.QuarticOuterClockLinear

open EthInapproximability.CurrentPaper
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticFrontLift
open Paper2.CurrentAdditive.QuarticOuterOutput
open Paper2.CurrentAdditive.QuarticOuterEncodedCap

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 65536
set_option synthInstance.maxHeartbeats 4000000

def outerLinearCoefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  let a := Lift.a FS + 3
  let v := growthFactor
  let r := BitMachineStackGrowth.perStep (QuarticOuterRun.lifted Δ γ)
  let c := BitMachineStackGrowth.perStep (CopyAll.prog copies)
  let f := QuarticFrontCapTransfer.timeCoefficient Δ γ + 2
  let s := a + 1 + v * r * f
  f + (6 * s + 10) + a * (s + v * c * (6 * s + 10) + 1) + 3

theorem local_cap_linear
    (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (raw : List Bool) (Z : ℕ) :
    let I := (BitMachineBankCodec.encode (FullFront.X0 g k raw)).length
    let R := QuarticRawPrefixCutter.clock g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ k raw
    let W := Z + R + I + 1
    QuarticOuterUniform.localCap g Δ γ k raw Z ≤
      outerLinearCoefficient Δ γ * W := by
  intro I R W
  let a := Lift.a FS + 3
  let v := growthFactor
  let r := BitMachineStackGrowth.perStep (QuarticOuterRun.lifted Δ γ)
  let c := BitMachineStackGrowth.perStep (CopyAll.prog copies)
  let f := QuarticFrontCapTransfer.timeCoefficient Δ γ + 2
  let s := a + 1 + v * r * f
  let F := QuarticOuterUniform.frontCutCap g Δ γ k raw Z
  let J := QuarticOuterUniform.outerInputSize g k raw
  let S := QuarticOuterUniform.outerSizeCap g Δ γ k raw Z
  have hW : 1 ≤ W := by dsimp [W]; omega
  have hF : F ≤ f * W := by
    dsimp [F, f, W, QuarticOuterUniform.frontCutCap, R]
    nlinarith
  have hJ : J ≤ (a + 1) * W := by
    dsimp [J, a, W, QuarticOuterUniform.outerInputSize, I]
    rw [Wrap.encode_widen, List.length_append, List.length_replicate]
    nlinarith
  have hS : S ≤ s * W := by
    have hh := Nat.mul_le_mul_left (v * r) hF
    dsimp [S, QuarticOuterUniform.outerSizeCap, frontSizeCap, J, F,
      s, v, r] at *
    nlinarith only [hJ, hh]
  have hC : copyTimeCap S ≤ (6 * s + 10) * W := by
    dsimp [copyTimeCap]
    nlinarith only [hS, hW]
  have hCS : copySizeCap S ≤
      (s + v * c * (6 * s + 10)) * W := by
    have hh := Nat.mul_le_mul_left (v * c) hC
    dsimp [copySizeCap, v, c] at *
    nlinarith only [hS, hh]
  have hA := Nat.mul_le_mul_left a hCS
  dsimp [QuarticOuterUniform.localCap, outerLinearCoefficient, a, v, r,
    c, f, s, F, S] at *
  nlinarith only [hF, hC, hA, hW]

#print axioms local_cap_linear

def outerClockCoefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  outerLinearCoefficient Δ γ + 100 * (Lift.a FS + 4) ^ 2

theorem cut_clock_linear
    (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (raw : List Bool) (Y : Fin 3 → List Bool) (Z : ℕ) :
    let X := FullFront.X0 g k raw
    let I := (BitMachineBankCodec.encode X).length
    let O := (BitMachineBankCodec.encode Y).length
    let R := QuarticRawPrefixCutter.clock g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ k raw
    let W := Z + R + I + O + 1
    QuarticOuterMachine.cutClock X Y
      (QuarticOuterUniform.localCap g Δ γ k raw Z) ≤
        outerClockCoefficient Δ γ * W := by
  intro X I O R W
  have hcap0 := local_cap_linear g Δ γ k raw Z
  dsimp only at hcap0
  have hcap : QuarticOuterUniform.localCap g Δ γ k raw Z ≤
      outerLinearCoefficient Δ γ * W := by
    have hW0 : Z + R + I + 1 ≤ W := by dsimp [W]; omega
    exact hcap0.trans (Nat.mul_le_mul_left _ hW0)
  have hW : 1 ≤ W := by dsimp [W]; omega
  have hI : I ≤ W := by dsimp [W]; omega
  have hO : O ≤ W := by dsimp [W]; omega
  let a := Lift.a FS + 3
  have hinner : a + I + 1 ≤ (a + 2) * W := by
    nlinarith only [hI, hW]
  have hprod := Nat.mul_le_mul_left (2 * (a + 3) + 1) hinner
  dsimp [QuarticOuterMachine.cutClock, outerClockCoefficient,
    X, I, O, a] at *
  nlinarith only [hcap, hW, hI, hO, hprod]

#print axioms cut_clock_linear

end
end Paper2.CurrentAdditive.QuarticOuterClockLinear
