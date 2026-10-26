import CurrentAdditive.V42PacketClock
import CurrentAdditive.V42PrintedGraphGap
import CurrentAdditive.V42RandomizedTapeFits

namespace CurrentAdditive.V42UniformReduction
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open V42RuntimeSchedule Workspace.Types.CommComplexity
open V42WRaw V42PrintedCompression
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

/-- Convert a literal binary resource clock into a source-size polynomial.
The exponent is an absolute constant times `K+1`. -/
theorem binary_resource_source_power (E n K : ℕ) (hn : 1 ≤ n) :
    2^(E*((K+1)*Nat.clog 2 n)) ≤ (n+2)^((2*E)*(K+1)) := by
  have hc : 2^(Nat.clog 2 n) ≤ (n+2)^2 := by
    have h := V39PublicSchedule.pow2Ceil_lt_twice n (by omega)
    change 2^(Nat.clog 2 n) < 2*n at h
    nlinarith
  calc
    _ = (2^(Nat.clog 2 n))^(E*(K+1)) := by rw [←pow_mul]; congr 1; ring
    _ ≤ ((n+2)^2)^(E*(K+1)) := Nat.pow_le_pow_left hc _
    _ = _ := by rw [←pow_mul]; congr 1; ring

/-- V42 `thm:uniform-reduction`, with the concrete fixed machine, actual
output word and fair-bit tape law. Every execution and resource conclusion
is proved; the only promises concern the source graph. -/
theorem uniform_reduction (g : EncodedGraph.Graph) (hg : g.Valid) (K Δ : ℕ)
    [NeZero g.vertices] (γ : ℚ) (hK : 1 ≤ K) (hγ : 0<γ) (hΔ : 0<Δ)
    (hdegree : ∀ v, SourceItems.degree (LiteralEdgeEncoder.edge g hg) v ≤ Δ)
    (hnm : g.vertices ≤ 2*g.edges.length) (hdeg : 2*g.edges.length ≤ Δ*g.vertices)
    (hlarge : V42FullCutoff.sourceCutoff γ Δ ≤ g.vertices) :
    let L := Nat.clog 2 g.vertices
    let cc := V38Schedule.fullConstant γ Δ g.vertices g.edges.length
    let δv := V38Schedule.sourceDeltaV γ Δ g.vertices g.edges.length
    let ζ := V38Schedule.sourceZeta γ
    let ht := V42PrintedGraphGap.public_runtime_tests g γ Δ hγ hΔ hnm hdeg hlarge
    (∃ e, sampleSide L K=2^e) ∧
    (∀ bits : Bits g K,
      finiteMachine.OutputsWithin (packedInput g K bits) (outputWord g hg K cc δv ζ ht bits)
        ((g.vertices+2)^((2*packetExponent)*(K+1))) ∧
      (RoundedCodeLoop.tapeWord (V42RawSamplerJoin.precision g.vertices K)
        (V42RawSamplerJoin.reservation g.vertices K) bits).length ≤
          (g.vertices+2)^(544*(K+1)) ∧
      decodeInstance (outputWord g hg K cc δv ζ ht bits)=
        some ⟨sampleSide L K,sampleSide L K,B L K,payload g hg K cc δv ζ ht bits⟩) ∧
    (∀ colour : Fin g.vertices → Fin 3,
      (∀ e, colour (LiteralEdgeEncoder.edge g hg e false)≠colour (LiteralEdgeEncoder.edge g hg e true)) →
      ∀ bits : Bits g K, D (V42RawRequestPacket.matrix g hg K cc δv ζ ht bits) ≤ B L K) ∧
    ((∀ colour : Fin g.vertices → Fin 3, (γ:ℝ)*g.edges.length ≤
      ((Finset.univ.filter (fun e => colour (LiteralEdgeEncoder.edge g hg e false)=
        colour (LiteralEdgeEncoder.edge g hg e true))).card:ℝ)) →
      (49/50:ℝ) ≤ (bitLaw g K).prob
        (fun bits => D (V42RawRequestPacket.matrix g hg K cc δv ζ ht bits)=B L K+K)) := by
  intro L cc δv ζ ht
  refine ⟨⟨_,rfl⟩,?_,?_,?_⟩
  · intro bits
    refine ⟨BitMachine.outputsWithin_mono _ (packed_outputs_exponential g hg K cc δv ζ hK ht bits)
      (binary_resource_source_power packetExponent g.vertices K (NeZero.pos g.vertices)),?_,?_⟩
    · rw [RoundedCodeLoop.tapeWord_length]
      exact V42RandomizedETHEndpoint.construction_bits_source_power g.vertices g.edges.length K
        (NeZero.pos g.vertices) cc δv ζ ht
    · exact every_output_valid g hg K cc δv ζ ht bits
  · intro colour proper bits
    exact V42PrintedGraphGap.every_tape_yes g hg K cc δv ζ ht colour proper bits
  · intro gap
    exact V42PrintedGraphGap.no_probability g hg K cc δv ζ ht Δ hΔ hdegree γ hγ hnm hdeg hlarge gap

#print axioms uniform_reduction
end
end CurrentAdditive.V42UniformReduction


