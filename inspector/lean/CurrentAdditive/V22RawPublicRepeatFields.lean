import CurrentAdditive.V22RawPublicRepeat

namespace V22RawPublicRepeat
noncomputable section
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open V38Schedule V39PublicSchedule V39FullSampleResources CurrentAdditive
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
local instance : DecidableEq Raw := rawDecEq
local instance : DecidableEq Stack := Classical.decEq _

def repetitions (g : EncodedGraph.Graph) := V22RepeatArithmetic.repetitions
  (fullQ₂ (Nat.clog 2 g.vertices)) (fullS (Nat.clog 2 g.vertices)) g.edges.length

def final (g : EncodedGraph.Graph) (k : ℕ) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V22RawSamplerJoin.precision g.vertices k) (V22RawSamplerJoin.reservation g.vertices k))
    (suffix : List Bool) : Stack → List Bool :=
  V22PublicRepeat.final
    (V22RawSamplerJoin.final (EncodedGraph.encode g) g.vertices k g.edges.length cc δv ζ ht bits suffix)
    graphPort g (fullS (Nat.clog 2 g.vertices)) (fullQ₂ (Nat.clog 2 g.vertices))

theorem final_original (g : EncodedGraph.Graph) (k : ℕ) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V22RawSamplerJoin.precision g.vertices k) (V22RawSamplerJoin.reservation g.vertices k))
    (suffix : List Bool) (j : Raw) :
    final g k cc δv ζ ht bits suffix (.inl j)=
      V22RawSamplerJoin.final (EncodedGraph.encode g) g.vertices k g.edges.length cc δv ζ ht bits suffix j :=
  V22PublicRepeat.raw_preserved _ _ _ _ _ _

theorem final_edgeCount (g : EncodedGraph.Graph) (k : ℕ) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V22RawSamplerJoin.precision g.vertices k) (V22RawSamplerJoin.reservation g.vertices k))
    (suffix : List Bool) :
    final g k cc δv ζ ht bits suffix (.inr (.inl 0))=List.replicate g.edges.length true :=
  V22PublicRepeat.edge_exact _ _ _ _ _

theorem final_repetition (g : EncodedGraph.Graph) (k : ℕ) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V22RawSamplerJoin.precision g.vertices k) (V22RawSamplerJoin.reservation g.vertices k))
    (suffix : List Bool) :
    final g k cc δv ζ ht bits suffix (.inr (.inl 3))=List.replicate (repetitions g) true :=
  V22PublicRepeat.repetition_exact _ _ _ _ _

theorem width_eq (g : EncodedGraph.Graph) (cc δv ζ : ℚ)
    (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ) :
    fullQ₂ (Nat.clog 2 g.vertices)=LiteralEdgeEncoder.Width
      (fullS (Nat.clog 2 g.vertices)) g.edges.length (repetitions g) :=
  V22RepeatArithmetic.full_width_of_tests cc δv ζ _ _ ht

theorem repetition_pos (g : EncodedGraph.Graph) (cc δv ζ : ℚ)
    (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ) : 0 < repetitions g :=
  V22RepeatArithmetic.full_repeat_pos _ _ ht.1.2.2.1

theorem run_final (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V22RawSamplerJoin.precision g.vertices k) (V22RawSamplerJoin.reservation g.vertices k))
    (suffix : List Bool) :
    let tape := RoundedCodeLoop.tapeWord (V22RawSamplerJoin.precision g.vertices k)
      (V22RawSamplerJoin.reservation g.vertices k) bits ++ suffix
    ∃ t ≤ clock g k, ((advance program)^[t])
      (⟨some start,control,V22PublicRepeat.initial (V22RawSamplerJoin.initial (EncodedGraph.encode g) k tape)⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label _) =
      ⟨none,control,final g k cc δv ζ ht bits suffix⟩ :=
  run g hg k cc δv ζ ht bits suffix

theorem additional_clock_polynomial (g : EncodedGraph.Graph) (cc δv ζ : ℚ)
    (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ) :
    V22PublicRepeat.clock g (fullS (Nat.clog 2 g.vertices)) (fullQ₂ (Nat.clog 2 g.vertices)) ≤
      V22PublicRepeat.clockCoefficient*((EncodedGraph.encode g).length+
        fullS (Nat.clog 2 g.vertices)+g.edges.length+fullQ₂ (Nat.clog 2 g.vertices)+1)^3 :=
  V22PublicRepeat.clock_polynomial _ _ _ ht.1.2.2.1

end
#print axioms V22RawPublicRepeat.run_final
#print axioms V22RawPublicRepeat.width_eq
end V22RawPublicRepeat
