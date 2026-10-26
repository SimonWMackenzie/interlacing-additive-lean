import CurrentAdditive.V40SourceBlockView
import CurrentAdditive.V42RawRequestPacket
import CurrentAdditive.V42RandomizedTapeFits
import CurrentAdditive.V39SourceCutClock
import CurrentAdditive.V42SourceGeometry

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
namespace CurrentAdditive.V42SourceClassifier
noncomputable section
open Paper2 Turing EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V42RuntimeSchedule
local instance : DecidableEq V42RawMidpointRequest.Raw := Classical.decEq _

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The density slack makes the fixed finite NO replacement sparse even
when the original promised clause density is zero. -/
def routed (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) : ValidFormula :=
  ⟨AEth4.routed4 (density+2) cutoff w,AEth4.routed4_valid _ hcutoff w⟩

theorem routed_sparse (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) :
    (routed density cutoff hcutoff w).val.clauses.length ≤
      (density+2)*(routed density cutoff hcutoff w).val.variables := by
  exact AEth4.routed4_sparse (density+2) cutoff (by nlinarith) w

def graph (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) :=
  t10Graph D B (routed density cutoff hcutoff w)

def gap (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) :=
  kOf (routed density cutoff hcutoff w).val.variables

theorem graph_valid (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) :
    (graph D B density cutoff hcutoff w).Valid := t10Graph_valid D B _

instance graph_nonzero (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) :
    NeZero (graph D B density cutoff hcutoff w).vertices :=
  ⟨(t10_vertices_pos D B _).ne'⟩

def minimum (C : SelectedTape.Algorithm) (density : ℕ) : ℕ :=
  max (V42SourceGeometry.originalCutoff D B (density+2))
    (Classical.choose (V42RandomizedETHEndpoint.current_two_blocks_fit C (D.sizeExponent+2)))

theorem minimum_pos (C : SelectedTape.Algorithm) (density : ℕ) : 0 < minimum D B C density :=
  (V42SourceGeometry.originalCutoff_pos D B (density+2)).trans_le (le_max_left _ _)

def coefficient (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) : ℚ :=
  V38Schedule.fullConstant (sourceGap D B) B.degreeBound
    (graph D B density cutoff hcutoff w).vertices (graph D B density cutoff hcutoff w).edges.length

def deltaV (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) : ℚ :=
  V38Schedule.sourceDeltaV (sourceGap D B) B.degreeBound
    (graph D B density cutoff hcutoff w).vertices (graph D B density cutoff hcutoff w).edges.length

theorem tests (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hmin : minimum D B C density ≤ cutoff) (w : List Bool) :
    FullTests (coefficient D B density cutoff hcutoff w)
      (Nat.clog 2 (graph D B density cutoff hcutoff w).vertices)
      (graph D B density cutoff hcutoff w).edges.length
      (deltaV D B density cutoff hcutoff w) (V38Schedule.sourceZeta (sourceGap D B)) := by
  have hN : V42SourceGeometry.originalCutoff D B (density+2) ≤
      (routed density cutoff hcutoff w).val.variables :=
    ((le_max_left _ _).trans hmin).trans (AEth4.routed4_variables _ _ w)
  exact (V42SourceGeometry.source_all_large D B (density+2) _
    (routed_sparse density cutoff hcutoff w) hN).2.1

def blockLength (density cutoff : ℕ) (w : List Bool) := AEth5.L1 (density+2) cutoff w

def precision (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) :=
  V42RawSamplerJoin.precision (graph D B density cutoff hcutoff w).vertices
    (gap density cutoff hcutoff w)

def reservation (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) :=
  V42RawSamplerJoin.reservation (graph D B density cutoff hcutoff w).vertices
    (gap density cutoff hcutoff w)

def request (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hmin : minimum D B C density ≤ cutoff) (w : List Bool)
    (bits : RoundedDraw.BitBlocks (precision D B density cutoff hcutoff w)
      (reservation D B density cutoff hcutoff w)) :=
  V42RawRequestPacket.request (graph D B density cutoff hcutoff w)
    (graph_valid D B density cutoff hcutoff w) (gap density cutoff hcutoff w)
    (coefficient D B density cutoff hcutoff w) (deltaV D B density cutoff hcutoff w)
    (V38Schedule.sourceZeta (sourceGap D B)) (tests D B C density cutoff hcutoff hmin w) bits

/-- Every raw formula routes to a source satisfying the actual full bit
reservation and independent classifier-block fit. The cutoff is fixed and
may be increased to include later semantic thresholds. -/
theorem resources (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hmin : minimum D B C density ≤ cutoff) (w : List Bool) :
    precision D B density cutoff hcutoff w * reservation D B density cutoff hcutoff w ≤
      blockLength density cutoff w ∧
    ∀ bits, blockLength density cutoff w +
      C.tapeLength (request D B C density cutoff hcutoff hmin w bits) ≤
        2^(V42RandomizedETHEndpoint.classifierBlockExponent C)*blockLength density cutoff w := by
  let Φ := routed density cutoff hcutoff w
  have hvars : cutoff ≤ Φ.val.variables := AEth4.routed4_variables _ _ w
  have hfitN : Classical.choose
      (V42RandomizedETHEndpoint.current_two_blocks_fit C (D.sizeExponent+2)) ≤ Φ.val.variables :=
    ((le_max_right _ _).trans hmin).trans hvars
  have hsourceN : V42SourceGeometry.originalCutoff D B (density+2) ≤ Φ.val.variables :=
    ((le_max_left _ _).trans hmin).trans hvars
  have hsource := V42SourceGeometry.source_all_large D B (density+2) Φ
    (routed_sparse density cutoff hcutoff w) hsourceN
  have hL : AEth.expLen Φ.val.variables ≤ blockLength density cutoff w := by
    have h := AEth3.cutLen_ge Φ.val
    change AEth.expLen Φ.val.variables ≤ AEth3.cutLen Φ.val
    omega
  have hf := Classical.choose_spec
    (V42RandomizedETHEndpoint.current_two_blocks_fit C (D.sizeExponent+2))
    Φ.val.variables hfitN (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
    (blockLength density cutoff w) (t10_vertices_pos D B Φ) hsource.2.2 hL
    (coefficient D B density cutoff hcutoff w) (deltaV D B density cutoff hcutoff w)
    (V38Schedule.sourceZeta (sourceGap D B)) (tests D B C density cutoff hcutoff hmin w)
  refine ⟨hf.1,?_⟩
  intro bits
  exact hf.2 (V42RawRequestPacket.matrix (graph D B density cutoff hcutoff w)
    (graph_valid D B density cutoff hcutoff w) (gap density cutoff hcutoff w)
    (coefficient D B density cutoff hcutoff w) (deltaV D B density cutoff hcutoff w)
    (V38Schedule.sourceZeta (sourceGap D B)) (tests D B C density cutoff hcutoff hmin w) bits)

end
end CurrentAdditive.V42SourceClassifier
#print axioms CurrentAdditive.V42SourceClassifier.resources

