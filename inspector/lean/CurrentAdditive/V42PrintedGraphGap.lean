import CurrentAdditive.V42GraphLiteralBounds

/-! The replacement manuscript's finite randomized reduction on the exact
actual printed matrix and its actual fixed fair-bit tape law. The source
graph promise supplies the NO lower bound; the rank catalogue, sampling
event and sampler-error bound are proved, not hypotheses of this theorem. -/

namespace CurrentAdditive.V42PrintedGraphGap
noncomputable section

open Paper2 Workspace.Types.CommComplexity EthInapproximability.CurrentPaper
open V42RuntimeSchedule V42PrintedCompression

variable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
variable (K : ℕ) (cc δv ζ : ℚ)
variable (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)

theorem runtimeCutoff_le_semanticCutoff (γ : ℚ) (Δ : ℕ) :
    V42RuntimeSchedule.sourceCutoff γ Δ ≤ V42FullCutoff.sourceCutoff γ Δ := by
  unfold V42RuntimeSchedule.sourceCutoff V42FullCutoff.sourceCutoff
  apply max_le_max le_rfl
  apply Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ))
  unfold V42PublicCutoff.fullLengthCutoff
  apply Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ))
  omega

theorem public_runtime_tests (γ : ℚ) (Δ : ℕ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hnm : g.vertices ≤ 2*g.edges.length) (hdeg : 2*g.edges.length ≤ Δ*g.vertices)
    (hlarge : V42FullCutoff.sourceCutoff γ Δ ≤ g.vertices) :
    FullTests (V38Schedule.fullConstant γ Δ g.vertices g.edges.length)
      (Nat.clog 2 g.vertices) g.edges.length
      (V38Schedule.sourceDeltaV γ Δ g.vertices g.edges.length) (V38Schedule.sourceZeta γ) :=
  V42RuntimeSchedule.tests_all_large γ Δ g.vertices g.edges.length hγ hΔ
    (NeZero.pos g.vertices) hnm hdeg
    ((runtimeCutoff_le_semanticCutoff γ Δ).trans hlarge)

theorem every_tape_yes (colour : Fin g.vertices → Fin 3)
    (proper : ∀ e, colour (LiteralEdgeEncoder.edge g hg e false) ≠
      colour (LiteralEdgeEncoder.edge g hg e true)) (bits : Bits g K) :
    D (V42RawRequestPacket.matrix g hg K cc δv ζ ht bits) ≤
      B (Nat.clog 2 g.vertices) K :=
  every_tape_upper g hg K cc δv ζ ht _
    ((V42GraphLiteralBounds.source_upper g hg K cc δv ζ ht).2 colour proper) bits

private theorem cast_le {a b:ℚ} (h:a ≤ b) : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast h

theorem no_probability (Δ : ℕ) (hΔ : 0 < Δ)
    (hdegree : ∀ v, SourceItems.degree (LiteralEdgeEncoder.edge g hg) v ≤ Δ)
    (γ : ℚ) (hγ : 0 < γ) (hnm : g.vertices ≤ 2*g.edges.length)
    (hdeg : 2*g.edges.length ≤ Δ*g.vertices)
    (hlarge : V42FullCutoff.sourceCutoff γ Δ ≤ g.vertices)
    (gap : ∀ colour : Fin g.vertices → Fin 3, (γ:ℝ)*g.edges.length ≤
      ((Finset.univ.filter (fun e => colour (LiteralEdgeEncoder.edge g hg e false)=
        colour (LiteralEdgeEncoder.edge g hg e true))).card:ℝ)) :
    (49/50:ℝ) ≤ (bitLaw g K).prob
      (fun bits => D (V42RawRequestPacket.matrix g hg K cc δv ζ ht bits)=
        H (Nat.clog 2 g.vertices) K) := by
  have hno:=V42GraphLiteralBounds.source_no_bounds g hg K cc δv ζ ht
    Δ hΔ hdegree γ hγ hnm hdeg hlarge gap
  have hbounds:=V42FullCutoff.bounds γ Δ g.vertices g.edges.length hγ hΔ
    (NeZero.pos g.vertices) hnm hlarge
  have hL : 1 ≤ Nat.clog 2 g.vertices := by omega
  have hρQ : V42Schedule.rho (Nat.clog 2 g.vertices) ≤ (1:ℚ)/2 :=
    V42Schedule.reciprocal_le _ 1 hL
  have hρR : (V42Schedule.rho (Nat.clog 2 g.vertices):ℝ) ≤ 1/2 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using cast_le hρQ
  have hp0 := hno.2 ⟨0,by decide⟩
  simp only [V38RestrictionProfiles.TwoThresholdProfile,Fin.val_zero,Nat.cast_zero,
    pow_zero,mul_one,sub_zero] at hp0
  apply printed_exact g hg K cc δv ζ ht
    (V42GraphLiteralBounds.source_rank g hg K cc δv ζ ht) hno.1.le
  intro U V hU hV
  have hh:=hp0 U V (hρR.trans (by linarith)) hV
  exact_mod_cast hh

#print axioms every_tape_yes
#print axioms no_probability

end
end CurrentAdditive.V42PrintedGraphGap

