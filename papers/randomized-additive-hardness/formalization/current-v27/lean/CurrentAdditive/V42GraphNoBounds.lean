import CurrentAdditive.V42GraphOwnerBounds
import CurrentAdditive.V42FullNoIteration
namespace CurrentAdditive.V42GraphOwnerBounds
noncomputable section
open Paper2 V42FullSuccessor V42PublicSchedule V39RecursiveGenerator
open Workspace.Types.CommComplexity EthInapproximability.CurrentPaper
local instance seedNZ_no (L : ℕ) : NeZero (seedWidth L) := ⟨by rw [seedWidth_exact]; positivity⟩
local instance fourSNZ_no (L : ℕ) : NeZero (4*fullS L) := ⟨by have hs:=fullS_ge_256 L; omega⟩
local instance sMinusNZ_no (L : ℕ) : NeZero (fullS L-3) := ⟨by have hs:=fullS_ge_256 L; omega⟩
variable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
variable (L r : ℕ) (hq : fullQ₂ L=LiteralEdgeEncoder.Width (fullS L) g.edges.length r)
theorem no_bounds (hL : L=Nat.clog 2 g.vertices) (Δ : ℕ) (hΔ : 0<Δ)
    (hdegree : ∀ v, SourceItems.degree (LiteralEdgeEncoder.edge g hg) v≤Δ)
    (γ : ℚ) (hγ : 0<γ) (hnm : g.vertices≤2*g.edges.length)
    (hdeg : 2*g.edges.length≤Δ*g.vertices)
    (hlarge : V42FullCutoff.sourceCutoff γ Δ≤g.vertices)
    (gap : ∀ colour : Fin g.vertices → Fin 3, (γ:ℝ)*g.edges.length≤
      ((Finset.univ.filter (fun e => colour (LiteralEdgeEncoder.edge g hg e false)=
        colour (LiteralEdgeEncoder.edge g hg e true))).card:ℝ)) (k : ℕ) :
    D (matrix g hg L r hq k)=H L k ∧
    V38RestrictionProfiles.TwoThresholdProfile (matrix g hg L r hq k)
      (rowLaw g L k).toFiniteLaw (columnLaw g L k).toFiniteLaw
      (V42Schedule.rho L:ℝ) (H L k:ℤ) := by
  have hn:=NeZero.pos g.vertices
  have hE:0<g.edges.length := by omega
  have h:=V42FullIteration.no_iteration L (by simpa only [Fintype.card_fin] using hL)
    (LiteralEdgeEncoder.itemOrder (fullS L) g.vertices) (LiteralEdgeEncoder.edge g hg)
    (LiteralEdgeEncoder.edge_loopless g hg) r Δ hΔ hq hdegree γ hγ
    (by simpa only [Fintype.card_fin] using hE)
    (by simpa only [Fintype.card_fin] using hnm)
    (by simpa only [Fintype.card_fin] using hdeg)
    (by simpa only [Fintype.card_fin] using hlarge)
    (by simpa only [Fintype.card_fin] using gap) k
  rw [V42FullActualLabels.iterate_eq_actualState g.vertices (NeZero.pos g.vertices) L _ _ r hq k] at h
  exact h


#print axioms no_bounds
end
end CurrentAdditive.V42GraphOwnerBounds

