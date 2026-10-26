import CurrentAdditive.QuarticSourceCutClock

/-! Instantiate the abstract numeric cut clock with the literal source schedule. -/

namespace Paper2.CurrentAdditive.QuarticSourceCutInst

open EthInapproximability.CurrentPaper
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticTMClockRepair
open Paper2.CurrentAdditive.QuarticCutterClockBound
open Paper2.CurrentAdditive.QuarticSourceCutClock

noncomputable section
set_option maxHeartbeats 8000000

theorem source_cut_clock
    (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hn : 0 < g.vertices)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ)
    (raw : List Bool) (Y : Fin 3 → List Bool) :
    let Praw := (g.vertices + 2) ^ (rawExponent Δ γ * (k + 1))
    let Pcut := (g.vertices + 2) ^ (360 * (k + 1))
    let S := Praw + Pcut + (EncodedGraph.encode g).length + k +
      raw.length + (BitMachineBankCodec.encode Y).length + 1
    QuarticOuterMachine.cutClock (FullFront.X0 g k raw) Y
      (QuarticOuterUniform.localCap g Δ γ k raw
        (QuarticUniformInputCap.inputCap g Δ γ k raw.length)) ≤
      cutNumericCoefficient Δ γ * S := by
  intro Praw Pcut S
  let Z := QuarticUniformInputCap.inputCap g Δ γ k raw.length
  have hZ : Z = 4 + 2 * ((EncodedGraph.encode g).length + k + raw.length) +
      rawCoefficient Δ γ * (Praw + raw.length) :=
    QuarticInputCapAtoms.input_cap_formula g Δ γ k raw.length
  have hR : QuarticRawPrefixCutter.clock g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ k raw ≤
      cutCoefficient * (Pcut + raw.length + 1) :=
    raw_prefix_clock_scheduled hn Δ γ hc k raw
  exact cut_clock_of_numeric_atoms g Δ γ k raw Y Z Praw Pcut hZ hR

#print axioms source_cut_clock

end
end Paper2.CurrentAdditive.QuarticSourceCutInst
