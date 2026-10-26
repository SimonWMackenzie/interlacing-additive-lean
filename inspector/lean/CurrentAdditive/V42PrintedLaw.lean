import CurrentAdditive.V42WRawPacket

/-! The probability event and valid instance refer to the exact output
word of the new raw-input physical machine, on every fair-bit tape. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
namespace CurrentAdditive.V42WRaw
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open V42RuntimeSchedule V39RecursiveGenerator

variable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
variable (K : ℕ) (cc δv ζ : ℚ)
variable (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)

abbrev Sample :=
  (Fin (sampleSide (Nat.clog 2 g.vertices) K) → Row g.vertices
    (seedWidth (Nat.clog 2 g.vertices)) (fullQ₁ (Nat.clog 2 g.vertices))
    (fullQ₂ (Nat.clog 2 g.vertices)) (fullS (Nat.clog 2 g.vertices))
    (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices)) K) ×
  (Fin (sampleSide (Nat.clog 2 g.vertices) K) → Column g.vertices
    (seedWidth (Nat.clog 2 g.vertices)) (fullQ₁ (Nat.clog 2 g.vertices))
    (fullQ₂ (Nat.clog 2 g.vertices)) (fullS (Nat.clog 2 g.vertices))
    (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices)) K)

def wordFromLabels (z : Sample g K) : List Bool :=
  let L := Nat.clog 2 g.vertices
  let m := sampleSide L K
  encodeInstance ⟨m,m,B L K,MatrixMaterialization.rowMajor (fun i j : Fin m =>
    V39RecursiveTable.matrix (V39EdgeSourceFront.edgeActivity g hg
      (by have h := fullS_ge_256 (Nat.clog 2 g.vertices); omega) (V42RawPublicRepeat.repetitions g)
      (V42RawPublicRepeat.width_eq g cc δv ζ ht)) K (z.1 i) (z.2 j))⟩

theorem outputWord_eq_fromLabels
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) :
    outputWord g hg K cc δv ζ ht bits =
      wordFromLabels g hg K cc δv ζ ht (labels g K cc δv ζ ht bits) := rfl

theorem output_event_error_200 (P : List Bool → Prop) :
    |(RoundedDraw.bitBlocksLaw (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)).prob
      (fun bits => P (outputWord g hg K cc δv ζ ht bits)) -
      (sampleLaw g.vertices (seedWidth (Nat.clog 2 g.vertices))
        (fullQ₁ (Nat.clog 2 g.vertices)) (fullQ₂ (Nat.clog 2 g.vertices))
        (fullS (Nat.clog 2 g.vertices)) (fullW (Nat.clog 2 g.vertices))
        (fullQ (Nat.clog 2 g.vertices)) K (sampleSide (Nat.clog 2 g.vertices) K)).toFiniteLaw.prob
          (fun z => P (wordFromLabels g hg K cc δv ζ ht z))| ≤ (1:ℝ)/200 := by
  simp_rw [outputWord_eq_fromLabels]
  exact V39PhysicalSample.budget_labels_event_error_200 g.vertices
    (seedWidth (Nat.clog 2 g.vertices)) (fullQ₁ (Nat.clog 2 g.vertices))
    (fullQ₂ (Nat.clog 2 g.vertices)) (fullS (Nat.clog 2 g.vertices))
    (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices))
    (by have h := fullS_ge_256 (Nat.clog 2 g.vertices); omega) rfl K
    (sampleSide (Nat.clog 2 g.vertices) K) (V42RawSamplerJoin.reservation g.vertices K)
    (fullDrawCap_le cc (Nat.clog 2 g.vertices) g.edges.length K δv ζ ht)
    (fun z => P (wordFromLabels g hg K cc δv ζ ht z))

theorem every_output_valid
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) :
    decodeInstance (outputWord g hg K cc δv ζ ht bits) =
      some ⟨sampleSide (Nat.clog 2 g.vertices) K,sampleSide (Nat.clog 2 g.vertices) K,
        B (Nat.clog 2 g.vertices) K,payload g hg K cc δv ζ ht bits⟩ := by
  apply decode_encode
  have hm : 0<sampleSide (Nat.clog 2 g.vertices) K :=
    (by positivity : 0<2^(V42RuntimeSchedule.H (Nat.clog 2 g.vertices) K)).trans_le
      (V42PublicSchedule.sampleSide_lower _ _)
  exact ⟨hm,hm,by simp [payload]⟩

#print axioms output_event_error_200
#print axioms every_output_valid
end
end CurrentAdditive.V42WRaw

