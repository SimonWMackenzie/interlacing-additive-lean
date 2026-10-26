import CurrentAdditive.V42GraphNoBounds
import CurrentAdditive.V42PrintedCompression
import CurrentAdditive.V39SelectorGraph

/-! Instantiate the proved selector permutation at the replacement widths.
The NO profile and rank belong to the actual literal source queried by the
raw graph printer, with its original laws. Owner activity is never identified
with literal activity without the checked conjugacy. -/

namespace CurrentAdditive.V42GraphLiteralBounds
noncomputable section

open Paper2 Workspace.Types.CommComplexity EthInapproximability.CurrentPaper
open V42RuntimeSchedule V39RecursiveGenerator V42PrintedCompression

variable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
variable (K : ℕ) (cc δv ζ : ℚ)
variable (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)

theorem source_upper :
    D (sourceMatrix g hg K cc δv ζ ht) ≤ H (Nat.clog 2 g.vertices) K ∧
    (∀ colour : Fin g.vertices → Fin 3,
      (∀ e, colour (LiteralEdgeEncoder.edge g hg e false) ≠
        colour (LiteralEdgeEncoder.edge g hg e true)) →
      D (sourceMatrix g hg K cc δv ζ ht) ≤ B (Nat.clog 2 g.vertices) K) := by
  let L:=Nat.clog 2 g.vertices
  let r:=V42RawPublicRepeat.repetitions g
  have hq:=V42RawPublicRepeat.width_eq g cc δv ζ ht
  have ho:=V42GraphOwnerBounds.upper g hg L r hq K
  have he:=V39SelectorTransport.graph_D (p:=seedWidth L) (q₁:=fullQ₁ L)
    (w:=fullW L) (Q:=fullQ L) g hg
    (by change 3 ≤ fullS L; have hh:=fullS_ge_256 L; omega) r hq K
  change D (sourceMatrix g hg K cc δv ζ ht)=
    D (V42GraphOwnerBounds.matrix g hg L r hq K) at he
  rw [he]
  exact ho

theorem source_rank :
    (RankLeaves.realMatrix (sourceMatrix g hg K cc δv ζ ht)).rank ≤
      rankBound (Nat.clog 2 g.vertices) K := by
  let L:=Nat.clog 2 g.vertices
  let r:=V42RawPublicRepeat.repetitions g
  have hq:=V42RawPublicRepeat.width_eq g cc δv ζ ht
  have ho:=V42GraphOwnerBounds.rank_bound g hg L r hq
    (Nat.le_pow_clog (by decide) g.vertices) K
  have he:=V39SelectorTransport.graph_rank (p:=seedWidth L) (q₁:=fullQ₁ L)
    (w:=fullW L) (Q:=fullQ L) g hg
    (by change 3 ≤ fullS L; have hh:=fullS_ge_256 L; omega) r hq K
  change (RankLeaves.realMatrix (sourceMatrix g hg K cc δv ζ ht)).rank=
    (RankLeaves.realMatrix (V42GraphOwnerBounds.matrix g hg L r hq K)).rank at he
  rw [he]
  exact ho

theorem source_no_bounds (Δ : ℕ) (hΔ : 0 < Δ)
    (hdegree : ∀ v, SourceItems.degree (LiteralEdgeEncoder.edge g hg) v ≤ Δ)
    (γ : ℚ) (hγ : 0 < γ) (hnm : g.vertices ≤ 2*g.edges.length)
    (hdeg : 2*g.edges.length ≤ Δ*g.vertices)
    (hlarge : V42FullCutoff.sourceCutoff γ Δ ≤ g.vertices)
    (gap : ∀ colour : Fin g.vertices → Fin 3, (γ:ℝ)*g.edges.length ≤
      ((Finset.univ.filter (fun e => colour (LiteralEdgeEncoder.edge g hg e false)=
        colour (LiteralEdgeEncoder.edge g hg e true))).card:ℝ)) :
    D (sourceMatrix g hg K cc δv ζ ht)=H (Nat.clog 2 g.vertices) K ∧
    V38RestrictionProfiles.TwoThresholdProfile (sourceMatrix g hg K cc δv ζ ht)
      (laws g.vertices (seedWidth (Nat.clog 2 g.vertices)) (fullQ₁ (Nat.clog 2 g.vertices))
        (fullQ₂ (Nat.clog 2 g.vertices)) (fullS (Nat.clog 2 g.vertices))
        (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices)) K).1.toFiniteLaw
      (laws g.vertices (seedWidth (Nat.clog 2 g.vertices)) (fullQ₁ (Nat.clog 2 g.vertices))
        (fullQ₂ (Nat.clog 2 g.vertices)) (fullS (Nat.clog 2 g.vertices))
        (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices)) K).2.toFiniteLaw
      (V42Schedule.rho (Nat.clog 2 g.vertices):ℝ) (H (Nat.clog 2 g.vertices) K:ℤ) := by
  let L:=Nat.clog 2 g.vertices
  let r:=V42RawPublicRepeat.repetitions g
  have hq:=V42RawPublicRepeat.width_eq g cc δv ζ ht
  have ho:=V42GraphOwnerBounds.no_bounds g hg L r hq rfl Δ hΔ hdegree γ hγ hnm hdeg hlarge gap K
  have he:=V39SelectorTransport.graph_D (p:=seedWidth L) (q₁:=fullQ₁ L)
    (w:=fullW L) (Q:=fullQ L) g hg
    (by change 3 ≤ fullS L; have hh:=fullS_ge_256 L; omega) r hq K
  change D (sourceMatrix g hg K cc δv ζ ht)=
    D (V42GraphOwnerBounds.matrix g hg L r hq K) at he
  refine ⟨he.trans ho.1,?_⟩
  have hpiff:=V39SelectorTransport.graph_profile_iff (p:=seedWidth L) (q₁:=fullQ₁ L)
    (w:=fullW L) (Q:=fullQ L) g hg
    (by change 3 ≤ fullS L; have hh:=fullS_ge_256 L; omega) r hq K (V42Schedule.rho L:ℝ) (H L K:ℤ)
  apply hpiff.mpr
  exact ho.2

#print axioms source_upper
#print axioms source_rank
#print axioms source_no_bounds

end
end CurrentAdditive.V42GraphLiteralBounds

