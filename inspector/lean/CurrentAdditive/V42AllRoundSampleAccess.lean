import CurrentAdditive.V42AllRoundPacketClock
import CurrentAdditive.V42PrintedLaw

/-! Source-facing sample access for every natural round count. The entire
joint label law is controlled, not merely the pushed-forward table word. -/
namespace CurrentAdditive.V42ZeroAccess
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open V42RuntimeSchedule V42FullTableClock V42WRaw V39RecursiveGenerator
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

variable (g : EncodedGraph.Graph) [NeZero g.vertices]
variable (K : ℕ) (cc δv ζ : ℚ)
variable (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)

/-- Every event in the actual joint row/column label tuple has error at most
1/200, uniformly including K=0. This is before mapping labels to a table. -/
theorem labels_event_error_all (P : V42WRaw.Sample g K → Prop) :
    |(RoundedDraw.bitBlocksLaw (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)).prob
        (fun bits => P (labels g K cc δv ζ ht bits)) -
      (sampleLaw g.vertices (seedWidth (Nat.clog 2 g.vertices))
        (fullQ₁ (Nat.clog 2 g.vertices)) (fullQ₂ (Nat.clog 2 g.vertices))
        (fullS (Nat.clog 2 g.vertices)) (fullW (Nat.clog 2 g.vertices))
        (fullQ (Nat.clog 2 g.vertices)) K (sampleSide (Nat.clog 2 g.vertices) K)).toFiniteLaw.prob P| ≤
      (1:ℝ)/200 := by
  exact V39PhysicalSample.budget_labels_event_error_200 g.vertices
    (seedWidth (Nat.clog 2 g.vertices)) (fullQ₁ (Nat.clog 2 g.vertices))
    (fullQ₂ (Nat.clog 2 g.vertices)) (fullS (Nat.clog 2 g.vertices))
    (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices))
    (by have h := fullS_ge_256 (Nat.clog 2 g.vertices); omega) rfl K
    (sampleSide (Nat.clog 2 g.vertices) K) (V42RawSamplerJoin.reservation g.vertices K)
    (fullDrawCap_le cc (Nat.clog 2 g.vertices) g.edges.length K δv ζ ht) P

omit [NeZero g.vertices] in
theorem binary_resource_source_power (E n k : ℕ) (hn : 1 ≤ n) :
    2^(E*((k+1)*Nat.clog 2 n)) ≤ (n+2)^((2*E)*(k+1)) := by
  have hc : 2^(Nat.clog 2 n) ≤ (n+2)^2 := by
    have h := V39PublicSchedule.pow2Ceil_lt_twice n (by omega)
    change 2^(Nat.clog 2 n) < 2*n at h
    nlinarith
  calc
    _ = (2^(Nat.clog 2 n))^(E*(k+1)) := by rw [←pow_mul]; congr 1; ring
    _ ≤ ((n+2)^2)^(E*(k+1)) := Nat.pow_le_pow_left hc _
    _ = _ := by rw [←pow_mul]; congr 1; ring

def sampledMatrix (hg : g.Valid)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) :
    Fin (sampleSide (Nat.clog 2 g.vertices) K) →
      Fin (sampleSide (Nat.clog 2 g.vertices) K) → Bool := fun i j =>
  V39RecursiveTable.matrix (V39EdgeSourceFront.edgeActivity g hg
    (by have h := fullS_ge_256 (Nat.clog 2 g.vertices); omega)
    (V42RawPublicRepeat.repetitions g) (V42RawPublicRepeat.width_eq g cc δv ζ ht))
    K ((labels g K cc δv ζ ht bits).1 i) ((labels g K cc δv ζ ht bits).2 j)

/-- Literal source `lem:sample-access`, including zero rounds. The fixed
machine prints every exact entry for the actual sampled legal input labels.
Both random-bit count and paid every-tape clock have absolute exponents. -/
theorem sample_access_all (hg : g.Valid) :
    (∀ bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K),
      finiteMachine.OutputsWithin (packedInput g K bits) (outputWord g hg K cc δv ζ ht bits)
        ((g.vertices+2)^((2*packetExponentAll)*(K+1))) ∧
      (RoundedCodeLoop.tapeWord (V42RawSamplerJoin.precision g.vertices K)
        (V42RawSamplerJoin.reservation g.vertices K) bits).length ≤
          (g.vertices+2)^(544*(K+1)) ∧
      decodeInstance (outputWord g hg K cc δv ζ ht bits)=
        some ⟨sampleSide (Nat.clog 2 g.vertices) K,sampleSide (Nat.clog 2 g.vertices) K,
          B (Nat.clog 2 g.vertices) K,
          MatrixMaterialization.rowMajor (sampledMatrix g K cc δv ζ ht hg bits)⟩) ∧
    (∀ P : V42WRaw.Sample g K → Prop,
      |(RoundedDraw.bitBlocksLaw (V42RawSamplerJoin.precision g.vertices K)
        (V42RawSamplerJoin.reservation g.vertices K)).prob
          (fun bits => P (labels g K cc δv ζ ht bits)) -
        (sampleLaw g.vertices (seedWidth (Nat.clog 2 g.vertices))
          (fullQ₁ (Nat.clog 2 g.vertices)) (fullQ₂ (Nat.clog 2 g.vertices))
          (fullS (Nat.clog 2 g.vertices)) (fullW (Nat.clog 2 g.vertices))
          (fullQ (Nat.clog 2 g.vertices)) K (sampleSide (Nat.clog 2 g.vertices) K)).toFiniteLaw.prob P| <
        (1:ℝ)/100) := by
  constructor
  · intro bits
    refine ⟨BitMachine.outputsWithin_mono _ (packed_outputs_all g hg K cc δv ζ ht bits)
      (binary_resource_source_power packetExponentAll g.vertices K (NeZero.pos g.vertices)),?_,?_⟩
    · rw [RoundedCodeLoop.tapeWord_length]
      have hb := V42RuntimeSchedule.reserved_bits_le g.vertices (Nat.clog 2 g.vertices) K
        (Nat.le_pow_clog (by decide) _) ht.2
      apply hb.trans
      have hp := binary_resource_source_power 272 g.vertices K (NeZero.pos g.vertices)
      simpa only [T,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hp
    · exact every_output_valid g hg K cc δv ζ ht bits
  · intro P
    have h := labels_event_error_all g K cc δv ζ ht P
    linarith

/-- The source graph above its fixed effective cutoff discharges every
numerical runtime premise, uniformly over all natural K, including zero. -/
theorem promised_sample_access_all (g : EncodedGraph.Graph) (hg : g.Valid) (K Δ : ℕ)
    [NeZero g.vertices] (γ : ℚ) (hγ : 0<γ) (hΔ : 0<Δ)
    (hnm : g.vertices ≤ 2*g.edges.length) (hdeg : 2*g.edges.length ≤ Δ*g.vertices)
    (hlarge : V42RuntimeSchedule.sourceCutoff γ Δ ≤ g.vertices) :
    let cc := V38Schedule.fullConstant γ Δ g.vertices g.edges.length
    let δv := V38Schedule.sourceDeltaV γ Δ g.vertices g.edges.length
    let ζ := V38Schedule.sourceZeta γ
    let ht := V42RuntimeSchedule.tests_all_large γ Δ g.vertices g.edges.length
      hγ hΔ (NeZero.pos g.vertices) hnm hdeg hlarge
    (∀ bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K),
      finiteMachine.OutputsWithin (packedInput g K bits) (outputWord g hg K cc δv ζ ht bits)
        ((g.vertices+2)^((2*packetExponentAll)*(K+1))) ∧
      (RoundedCodeLoop.tapeWord (V42RawSamplerJoin.precision g.vertices K)
        (V42RawSamplerJoin.reservation g.vertices K) bits).length ≤
          (g.vertices+2)^(544*(K+1)) ∧
      decodeInstance (outputWord g hg K cc δv ζ ht bits)=
        some ⟨sampleSide (Nat.clog 2 g.vertices) K,sampleSide (Nat.clog 2 g.vertices) K,
          B (Nat.clog 2 g.vertices) K,
          MatrixMaterialization.rowMajor (sampledMatrix g K cc δv ζ ht hg bits)⟩) ∧
    (∀ P : V42WRaw.Sample g K → Prop,
      |(RoundedDraw.bitBlocksLaw (V42RawSamplerJoin.precision g.vertices K)
        (V42RawSamplerJoin.reservation g.vertices K)).prob
          (fun bits => P (labels g K cc δv ζ ht bits)) -
        (sampleLaw g.vertices (seedWidth (Nat.clog 2 g.vertices))
          (fullQ₁ (Nat.clog 2 g.vertices)) (fullQ₂ (Nat.clog 2 g.vertices))
          (fullS (Nat.clog 2 g.vertices)) (fullW (Nat.clog 2 g.vertices))
          (fullQ (Nat.clog 2 g.vertices)) K (sampleSide (Nat.clog 2 g.vertices) K)).toFiniteLaw.prob P| <
        (1:ℝ)/100) := by
  intro cc δv ζ ht
  exact sample_access_all g K cc δv ζ ht hg

#print axioms labels_event_error_all
#print axioms sample_access_all
#print axioms promised_sample_access_all
end
end CurrentAdditive.V42ZeroAccess
