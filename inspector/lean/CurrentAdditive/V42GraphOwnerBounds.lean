import CurrentAdditive.V42FullActualLabels
import CurrentAdditive.EdgeMatrixProductionConjugacy

set_option autoImplicit false

/-! Instantiate the proved full iteration on the actual encoded graph and
the current complete sampler labels. Coordinate numbering is still the
owner numbering here; the literal-numbered printer transport is separate. -/

namespace CurrentAdditive.V42GraphOwnerBounds
noncomputable section
open Paper2 V42FullSuccessor V42PublicSchedule V39RecursiveGenerator
open V42FullActualLabels Workspace.Types.CommComplexity
open EthInapproximability.CurrentPaper
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384

local instance seedNZ (L : ℕ) : NeZero (seedWidth L) := ⟨by
  rw [seedWidth_exact]; positivity⟩
local instance fourSNZ (L : ℕ) : NeZero (4*fullS L) := ⟨by
  have hs:=fullS_ge_256 L; omega⟩
local instance sMinusNZ (L : ℕ) : NeZero (fullS L-3) := ⟨by
  have hs:=fullS_ge_256 L; omega⟩

variable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
variable (L r : ℕ) (hq : fullQ₂ L=LiteralEdgeEncoder.Width (fullS L) g.edges.length r)

def activity := V42FullActualLabels.ownerActivity g.vertices L
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
  have h:=V42FullIteration.upper_iteration L
    (LiteralEdgeEncoder.itemOrder (fullS L) g.vertices) (LiteralEdgeEncoder.edge g hg) r hq k
  rw [V42FullActualLabels.iterate_eq_actualState g.vertices (NeZero.pos g.vertices) L _ _ r hq k] at h
  exact h

theorem rank_bound (hn : g.vertices≤2^L) (k : ℕ) :
    (RankLeaves.realMatrix (matrix g hg L r hq k)).rank≤rankBound L k := by
  have h:=V42FullIteration.rank_iteration L (by simpa only [Fintype.card_fin] using hn)
    (LiteralEdgeEncoder.itemOrder (fullS L) g.vertices) (LiteralEdgeEncoder.edge g hg) r hq k
  rw [V42FullActualLabels.iterate_eq_actualState g.vertices (NeZero.pos g.vertices) L _ _ r hq k] at h
  exact h

#print axioms upper
#print axioms rank_bound

end
end CurrentAdditive.V42GraphOwnerBounds

