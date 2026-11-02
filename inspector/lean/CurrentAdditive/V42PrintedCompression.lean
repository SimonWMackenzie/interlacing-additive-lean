import CurrentAdditive.V42Compression
import CurrentAdditive.V42EncodedCostEvent
import CurrentAdditive.V42PrintedLaw
import CurrentAdditive.V42RawRequestPacket

/-! Exact current printed-table probability from ideal compression and the
implemented fixed-bit sampler's whole-output event bound. The matrix here
is definitionally the payload of the physical raw-input request program. -/

namespace CurrentAdditive.V42PrintedCompression
noncomputable section

open Paper2 Workspace.Types.CommComplexity
open EthInapproximability.CurrentPaper EncodedCommunication
open V42RuntimeSchedule V39RecursiveGenerator

variable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
variable (K : ℕ) (cc δv ζ : ℚ)
variable (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)

def sourceMatrix :
    Row g.vertices (seedWidth (Nat.clog 2 g.vertices)) (fullQ₁ (Nat.clog 2 g.vertices))
      (fullQ₂ (Nat.clog 2 g.vertices)) (fullS (Nat.clog 2 g.vertices))
      (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices)) K →
    Column g.vertices (seedWidth (Nat.clog 2 g.vertices)) (fullQ₁ (Nat.clog 2 g.vertices))
      (fullQ₂ (Nat.clog 2 g.vertices)) (fullS (Nat.clog 2 g.vertices))
      (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices)) K → Bool :=
  V39RecursiveTable.matrix (V39EdgeSourceFront.edgeActivity g hg
    (by have hh:=fullS_ge_256 (Nat.clog 2 g.vertices); omega)
    (V42RawPublicRepeat.repetitions g) (V42RawPublicRepeat.width_eq g cc δv ζ ht)) K

def sampled (z : V42WRaw.Sample g K) :
    Fin (sampleSide (Nat.clog 2 g.vertices) K) →
      Fin (sampleSide (Nat.clog 2 g.vertices) K) → Bool :=
  sampleMatrix (sourceMatrix g hg K cc δv ζ ht) z.1 z.2

abbrev Bits := RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
  (V42RawSamplerJoin.reservation g.vertices K)
abbrev bitLaw := RoundedDraw.bitBlocksLaw (V42RawSamplerJoin.precision g.vertices K)
  (V42RawSamplerJoin.reservation g.vertices K)
abbrev idealLaw := sampleLaw g.vertices (seedWidth (Nat.clog 2 g.vertices))
  (fullQ₁ (Nat.clog 2 g.vertices)) (fullQ₂ (Nat.clog 2 g.vertices))
  (fullS (Nat.clog 2 g.vertices)) (fullW (Nat.clog 2 g.vertices))
  (fullQ (Nat.clog 2 g.vertices)) K (sampleSide (Nat.clog 2 g.vertices) K)

theorem matrix_eq_sampled (bits : Bits g K) :
    V42RawRequestPacket.matrix g hg K cc δv ζ ht bits=
      sampled g hg K cc δv ζ ht (V42WRaw.labels g K cc δv ζ ht bits) := rfl

theorem wordFromLabels_hasCost (C : ℕ) (z : V42WRaw.Sample g K) :
    V42EncodedCostEvent.HasCost C (V42WRaw.wordFromLabels g hg K cc δv ζ ht z) ↔
      D (sampled g hg K cc δv ζ ht z)=C :=
  V42EncodedCostEvent.hasCost_encode (V42Compression.sampleSide_pos _ _) _ _ _

theorem output_hasCost (C : ℕ) (bits : Bits g K) :
    V42EncodedCostEvent.HasCost C (V42WRaw.outputWord g hg K cc δv ζ ht bits) ↔
      D (V42RawRequestPacket.matrix g hg K cc δv ζ ht bits)=C := by
  rw [V42WRaw.outputWord_eq_fromLabels,matrix_eq_sampled]
  exact wordFromLabels_hasCost g hg K cc δv ζ ht C _

theorem every_tape_upper (C : ℕ)
    (hupper : D (sourceMatrix g hg K cc δv ζ ht) ≤ C) (bits : Bits g K) :
    D (V42RawRequestPacket.matrix g hg K cc δv ζ ht bits) ≤ C := by
  rw [matrix_eq_sampled]
  exact (V42Compression.sample_upper _ _ _ _ _).trans hupper

theorem ideal_exact
    (hrank : (RankLeaves.realMatrix (sourceMatrix g hg K cc δv ζ ht)).rank ≤
      rankBound (Nat.clog 2 g.vertices) K)
    (hupper : D (sourceMatrix g hg K cc δv ζ ht) ≤ H (Nat.clog 2 g.vertices) K)
    (hrobust : ∀ U V, (3/5:ℝ) ≤
      (laws g.vertices (seedWidth (Nat.clog 2 g.vertices)) (fullQ₁ (Nat.clog 2 g.vertices))
        (fullQ₂ (Nat.clog 2 g.vertices)) (fullS (Nat.clog 2 g.vertices))
        (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices)) K).1.toFiniteLaw.prob (· ∈ U) →
      (3/5:ℝ) ≤
      (laws g.vertices (seedWidth (Nat.clog 2 g.vertices)) (fullQ₁ (Nat.clog 2 g.vertices))
        (fullQ₂ (Nat.clog 2 g.vertices)) (fullS (Nat.clog 2 g.vertices))
        (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices)) K).2.toFiniteLaw.prob (· ∈ V) →
      H (Nat.clog 2 g.vertices) K ≤ Compression.restrictionD (sourceMatrix g hg K cc δv ζ ht) U V) :
    (99/100:ℝ) < (idealLaw g K).toFiniteLaw.prob
      (fun z => D (sampled g hg K cc δv ζ ht z)=H (Nat.clog 2 g.vertices) K) := by
  exact V42Compression.ideal_exact _ _ _ _ _ hrank hupper hrobust

theorem printed_exact
    (hrank : (RankLeaves.realMatrix (sourceMatrix g hg K cc δv ζ ht)).rank ≤
      rankBound (Nat.clog 2 g.vertices) K)
    (hupper : D (sourceMatrix g hg K cc δv ζ ht) ≤ H (Nat.clog 2 g.vertices) K)
    (hrobust : ∀ U V, (3/5:ℝ) ≤
      (laws g.vertices (seedWidth (Nat.clog 2 g.vertices)) (fullQ₁ (Nat.clog 2 g.vertices))
        (fullQ₂ (Nat.clog 2 g.vertices)) (fullS (Nat.clog 2 g.vertices))
        (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices)) K).1.toFiniteLaw.prob (· ∈ U) →
      (3/5:ℝ) ≤
      (laws g.vertices (seedWidth (Nat.clog 2 g.vertices)) (fullQ₁ (Nat.clog 2 g.vertices))
        (fullQ₂ (Nat.clog 2 g.vertices)) (fullS (Nat.clog 2 g.vertices))
        (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices)) K).2.toFiniteLaw.prob (· ∈ V) →
      H (Nat.clog 2 g.vertices) K ≤ Compression.restrictionD (sourceMatrix g hg K cc δv ζ ht) U V) :
    (49/50:ℝ) ≤ (bitLaw g K).prob
      (fun bits => D (V42RawRequestPacket.matrix g hg K cc δv ζ ht bits)=
        H (Nat.clog 2 g.vertices) K) := by
  let C:=H (Nat.clog 2 g.vertices) K
  have hideal:=ideal_exact g hg K cc δv ζ ht hrank hupper hrobust
  have herror:=V42WRaw.output_event_error_200 g hg K cc δv ζ ht
    (V42EncodedCostEvent.HasCost C)
  have hbad := (abs_le.mp herror).1
  have heIdeal :
      (fun z => V42EncodedCostEvent.HasCost C (V42WRaw.wordFromLabels g hg K cc δv ζ ht z))=
      (fun z => D (sampled g hg K cc δv ζ ht z)=C) := by
    funext z
    exact propext (wordFromLabels_hasCost g hg K cc δv ζ ht C z)
  have heOutput :
      (fun bits => V42EncodedCostEvent.HasCost C (V42WRaw.outputWord g hg K cc δv ζ ht bits))=
      (fun bits => D (V42RawRequestPacket.matrix g hg K cc δv ζ ht bits)=C) := by
    funext bits
    exact propext (output_hasCost g hg K cc δv ζ ht C bits)
  rw [heIdeal,heOutput] at hbad
  change -(1/200:ℝ) ≤ (bitLaw g K).prob _-(idealLaw g K).toFiniteLaw.prob _ at hbad
  dsimp only [C] at hbad
  linarith

#print axioms matrix_eq_sampled
#print axioms every_tape_upper
#print axioms ideal_exact
#print axioms printed_exact

end
end CurrentAdditive.V42PrintedCompression
