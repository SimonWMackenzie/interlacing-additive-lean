import CurrentAdditive.QuarticUniformInputCap

/-! Clock expressions depend on tape words only through their lengths. -/

namespace Paper2.CurrentAdditive.QuarticClockShape

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.CurrentAdditive.QuarticNumericFront
open Paper2.CurrentAdditive.QuarticFrontLift
open Paper2.CurrentAdditive.QuarticOuterOutput
open Paper2.A3Assembly
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics

noncomputable section
set_option maxHeartbeats 8000000

theorem x0_encoded_length_eq (g : EncodedGraph.Graph) (k : ℕ)
    (raw₁ raw₂ : List Bool) (hlen : raw₁.length = raw₂.length) :
    (BitMachineBankCodec.encode (FullFront.X0 g k raw₁)).length =
      (BitMachineBankCodec.encode (FullFront.X0 g k raw₂)).length := by
  simp [BitMachineBankCodec.encode_length, FullFront.X0,
    Fin.sum_univ_succ, hlen]

theorem cutter_clock_eq (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (raw₁ raw₂ : List Bool) (hlen : raw₁.length = raw₂.length) :
    QuarticRawPrefixCutter.clock g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ k raw₁ =
    QuarticRawPrefixCutter.clock g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ k raw₂ := by
  simp only [QuarticRawPrefixCutter.clock, QuarticPreparedCut.clock, hlen]

theorem outer_input_size_eq (g : EncodedGraph.Graph) (k : ℕ)
    (raw₁ raw₂ : List Bool) (hlen : raw₁.length = raw₂.length) :
    QuarticOuterUniform.outerInputSize g k raw₁ =
      QuarticOuterUniform.outerInputSize g k raw₂ := by
  simp only [QuarticOuterUniform.outerInputSize, Wrap.encode_widen,
    List.length_append, List.length_replicate]
  rw [x0_encoded_length_eq g k raw₁ raw₂ hlen]

theorem local_cap_eq (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k Z : ℕ) (raw₁ raw₂ : List Bool) (hlen : raw₁.length = raw₂.length) :
    QuarticOuterUniform.localCap g Δ γ k raw₁ Z =
      QuarticOuterUniform.localCap g Δ γ k raw₂ Z := by
  have hc := cutter_clock_eq g Δ γ k raw₁ raw₂ hlen
  have ho := outer_input_size_eq g k raw₁ raw₂ hlen
  simp only [QuarticOuterUniform.localCap, QuarticOuterUniform.outerSizeCap,
    QuarticOuterUniform.frontCutCap, hc, ho]

theorem cut_clock_eq (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k Z : ℕ) (raw₁ raw₂ : List Bool) (Y₁ Y₂ : Fin 3 → List Bool)
    (hlen : raw₁.length = raw₂.length)
    (hY : (BitMachineBankCodec.encode Y₁).length =
      (BitMachineBankCodec.encode Y₂).length) :
    QuarticOuterMachine.cutClock (FullFront.X0 g k raw₁) Y₁
      (QuarticOuterUniform.localCap g Δ γ k raw₁ Z) =
    QuarticOuterMachine.cutClock (FullFront.X0 g k raw₂) Y₂
      (QuarticOuterUniform.localCap g Δ γ k raw₂ Z) := by
  have hx := x0_encoded_length_eq g k raw₁ raw₂ hlen
  have hc := local_cap_eq g Δ γ k Z raw₁ raw₂ hlen
  simp only [QuarticOuterMachine.cutClock, hx, hY, hc]

theorem pair_front_clock_eq (D : DinurReduction)
    (B : BOTReduction (booleanOccurrence D)) (Φ : ValidFormula)
    (raw₁ raw₂ : List Bool) (Y₁ Y₂ : Fin 3 → List Bool) (Z : ℕ)
    (hlen : raw₁.length = raw₂.length)
    (hY : (BitMachineBankCodec.encode Y₁).length =
      (BitMachineBankCodec.encode Y₂).length) :
    let g := t10Graph D B Φ
    let k := kOf Φ.val.variables
    QuarticPairFront.pairFrontClock D B Φ raw₁
      (BitMachineBankCodec.encode Y₁)
      (QuarticOuterMachine.cutClock (FullFront.X0 g k raw₁) Y₁
        (QuarticOuterUniform.localCap g B.degreeBound
          (sourceGap D B) k raw₁ Z)) =
    QuarticPairFront.pairFrontClock D B Φ raw₂
      (BitMachineBankCodec.encode Y₂)
      (QuarticOuterMachine.cutClock (FullFront.X0 g k raw₂) Y₂
        (QuarticOuterUniform.localCap g B.degreeBound
          (sourceGap D B) k raw₂ Z)) := by
  intro g k
  have hc := cut_clock_eq g B.degreeBound (sourceGap D B) k Z
    raw₁ raw₂ Y₁ Y₂ hlen hY
  have hx := x0_encoded_length_eq g k raw₁ raw₂ hlen
  dsimp only [g, k] at hc hx
  dsimp only [g, k]
  simp only [QuarticPairFront.pairFrontClock,
    EncodedComplexity.pair_length, hlen, hY, hx, hc]

#print axioms x0_encoded_length_eq
#print axioms cutter_clock_eq
#print axioms outer_input_size_eq
#print axioms local_cap_eq
#print axioms cut_clock_eq
#print axioms pair_front_clock_eq

end
end Paper2.CurrentAdditive.QuarticClockShape
