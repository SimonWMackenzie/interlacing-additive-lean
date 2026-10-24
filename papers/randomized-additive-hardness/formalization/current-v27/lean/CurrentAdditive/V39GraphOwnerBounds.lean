import CurrentAdditive.V39ActualIterationBridge
import CurrentAdditive.EdgeMatrixProductionConjugacy

set_option autoImplicit false

/-! Instantiate the proved full iteration on the actual encoded graph and
the current complete sampler labels. Coordinate numbering is still the
owner numbering here; the literal-numbered printer transport is separate. -/

namespace CurrentAdditive.V39GraphOwnerBounds
noncomputable section
open Paper2 V38Schedule V39PublicSchedule V39RecursiveGenerator
open V39ActualIterationBridge Workspace.Types.CommComplexity
open EthInapproximability.CurrentPaper
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384

variable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
variable (L r : ℕ) (hq : fullQ₂ L=LiteralEdgeEncoder.Width (fullS L) g.edges.length r)

def activity := V39ActualIterationBridge.ownerActivity g.vertices L
  (LiteralEdgeEncoder.itemOrder (fullS L) g.vertices) (LiteralEdgeEncoder.edge g hg) r hq

def matrix (k : ℕ) :
    Row g.vertices (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) k →
      Column g.vertices (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) k → Bool :=
  V39RecursiveTable.matrix (activity g hg L r hq) k

def rowLaw (k : ℕ) :=
  (laws g.vertices (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) k).1

def columnLaw (k : ℕ) :=
  (laws g.vertices (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) k).2

theorem upper (k : ℕ) :
    D (matrix g hg L r hq k)≤H L k ∧
    (∀ colour : Fin g.vertices → Fin 3,
      (∀ e, colour (LiteralEdgeEncoder.edge g hg e false)≠colour (LiteralEdgeEncoder.edge g hg e true)) →
      D (matrix g hg L r hq k)≤B L k) := by
  have h:=V39FullIteration.upper_iteration L
    (LiteralEdgeEncoder.itemOrder (fullS L) g.vertices) (LiteralEdgeEncoder.edge g hg) r hq k
  rw [V39ActualIterationBridge.iterate_eq_actualState g.vertices L _ _ r hq k] at h
  exact h

theorem rank_bound (hn : g.vertices≤2^L) (k : ℕ) :
    (RankLeaves.realMatrix (matrix g hg L r hq k)).rank≤rankBound L k := by
  have h:=V39FullIteration.rank_iteration L (by simpa only [Fintype.card_fin] using hn)
    (LiteralEdgeEncoder.itemOrder (fullS L) g.vertices) (LiteralEdgeEncoder.edge g hg) r hq k
  rw [V39ActualIterationBridge.iterate_eq_actualState g.vertices L _ _ r hq k] at h
  exact h

theorem no_bounds (hL : L=Nat.clog 2 g.vertices) (Δ : ℕ) (hΔ : 0<Δ)
    (hdegree : ∀ v, SourceItems.degree (LiteralEdgeEncoder.edge g hg) v≤Δ)
    (γ : ℚ) (hγ : 0<γ) (hnm : g.vertices≤2*g.edges.length)
    (hdeg : 2*g.edges.length≤Δ*g.vertices)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ≤g.vertices)
    (gap : ∀ colour : Fin g.vertices → Fin 3, (γ:ℝ)*g.edges.length≤
      ((Finset.univ.filter (fun e => colour (LiteralEdgeEncoder.edge g hg e false)=
        colour (LiteralEdgeEncoder.edge g hg e true))).card:ℝ)) (k : ℕ) :
    D (matrix g hg L r hq k)=H L k ∧
    V38RestrictionProfiles.TwoThresholdProfile (matrix g hg L r hq k)
      (rowLaw g L k).toFiniteLaw (columnLaw g L k).toFiniteLaw
      ((fullRho L:ℚ):ℝ) (H L k:ℤ) := by
  have hn:=NeZero.pos g.vertices
  have hE:0<g.edges.length := by omega
  have h:=V39FullIteration.no_iteration L (by simpa only [Fintype.card_fin] using hL)
    (LiteralEdgeEncoder.itemOrder (fullS L) g.vertices) (LiteralEdgeEncoder.edge g hg)
    (LiteralEdgeEncoder.edge_loopless g hg) r Δ hΔ hq hdegree γ hγ
    (by simpa only [Fintype.card_fin] using hE)
    (by simpa only [Fintype.card_fin] using hnm)
    (by simpa only [Fintype.card_fin] using hdeg)
    (by simpa only [Fintype.card_fin] using hlarge)
    (by simpa only [Fintype.card_fin] using gap) k
  rw [V39ActualIterationBridge.iterate_eq_actualState g.vertices L _ _ r hq k] at h
  exact h

#print axioms upper
#print axioms rank_bound
#print axioms no_bounds
end
end CurrentAdditive.V39GraphOwnerBounds
