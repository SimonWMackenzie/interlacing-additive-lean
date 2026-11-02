import CurrentAdditive.V42UniversalPrefix
import CurrentAdditive.V42UniversalFormatter
import CurrentAdditive.V42GraphRuntime
import CurrentAdditive.V42ActualLower

/-! One physical deterministic constructor for every caller-supplied
admissible dyadic public size. Its program and amplification constant are
fixed before that size, the graph and the number of rounds. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option synthInstance.maxSize 32768

namespace CurrentAdditive.V42UniversalRuntime
noncomputable section
open Paper2 EthInapproximability.CurrentPaper V42Schedule

@[irreducible] def amplification := V40PipelineRuntime.amplification V42UniversalPrefix.machine
  StoredMatrixEnvelopeStep.machine 2 1 V42UniversalPrefix.baseCoefficient V42UniversalPrefix.degree
  StoredMatrixEnvelopeStep.coefficient StoredMatrixEnvelopeStep.degree
@[irreducible] def exponent := V40PipelineRuntime.exponentCoefficient V42UniversalPrefix.machine
  StoredMatrixEnvelopeStep.machine V42UniversalFormatter.machine 2 1
  V42UniversalPrefix.baseCoefficient V42UniversalPrefix.degree
  StoredMatrixEnvelopeStep.coefficient StoredMatrixEnvelopeStep.degree
  V42UniversalFormatter.coefficient V42UniversalFormatter.degree
def machine := V40PipelineRuntime.pipeline V42UniversalPrefix.machine
  StoredMatrixEnvelopeStep.machine V42UniversalFormatter.machine
def C (Δ : ℕ) := (8*Δ+8)*exponent+1040

theorem amplification_ge : 2^64 ≤ amplification := by
  unfold amplification
  exact V40PipelineRuntime.amplification_ge _ _ _ _ _ _ _ _
theorem amplification_power : ∃ a, amplification=2^a := by
  unfold amplification
  exact ⟨V40PipelineRuntime.amplificationLog V42UniversalPrefix.machine StoredMatrixEnvelopeStep.machine 2 1
    V42UniversalPrefix.baseCoefficient V42UniversalPrefix.degree
    StoredMatrixEnvelopeStep.coefficient StoredMatrixEnvelopeStep.degree,rfl⟩

theorem requested_selected (g : EncodedGraph.Graph) (p : ℕ) (hn : g.vertices ≤ 2^(4*p)) :
    V42RuntimePrefix.selected p g=p := by
  have hc : Nat.clog 2 g.vertices ≤ 4*p :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hn
  unfold V42RuntimePrefix.selected V42PublicCutoff.generatedExponent
  omega

theorem width (Δ : ℕ) (g : EncodedGraph.Graph) (p : ℕ)
    (hn : g.vertices ≤ 2^(4*p)) (hdeg : 2*g.edges.length ≤ Δ*g.vertices) (hΔ : 2*Δ ≤ p) :
    q₂ p (4*p)=LiteralEdgeEncoder.Width (s p) g.edges.length
      (V42RuntimePacket.repetition p g.edges.length) := by
  have h:=V42GraphRuntime.selected_width Δ p g hdeg hΔ
  simpa only [requested_selected g p hn] using h

theorem base_bound (Δ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) (p : ℕ)
    (hp : 2 ≤ p) (hn : g.vertices ≤ 2^(4*p)) (hdeg : 2*g.edges.length ≤ Δ*g.vertices) :
    V42UniversalPrefix.base g p ≤ (8*Δ+6)*(V42UniversalPrefix.N p)^2 := by
  let N:=V42UniversalPrefix.N p
  have hN : 2 ≤ N := by
    change 2^1 ≤ 2^(4*p)
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega)
  have hnN : g.vertices ≤ N := hn
  have hm : g.edges.length ≤ Δ*N := by have h:=Nat.mul_le_mul_left Δ hnN; omega
  have ht : g.edges.length*(4*g.vertices+4) ≤ (Δ*N)*(8*N) := Nat.mul_le_mul hm (by omega)
  have hbytes:=EncodedGraph.encode_length_upper g hg
  change N+(EncodedGraph.encode g).length+2 ≤ (8*Δ+6)*N^2
  nlinarith

theorem outputs_base (g : EncodedGraph.Graph) (hg : g.Valid) (p K : ℕ)
    (hp : 2 ≤ p) (hn : 0 < g.vertices)
    (hq : q₂ p (4*p)=LiteralEdgeEncoder.Width (s p) g.edges.length
      (V42RuntimePacket.repetition p g.edges.length)) :
    let R:=V42RuntimeWords.run g hg p hp hn hq K
    machine.OutputsWithin (V42UniversalPrefix.input (EncodedGraph.encode g) p K)
      (V42UniversalFormatter.word (4*p) K R)
      ((V42UniversalPrefix.base g p)^(exponent*amplification^K)) ∧
    (V42UniversalFormatter.word (4*p) K R).length ≤
      (V42UniversalPrefix.base g p)^(exponent*amplification^K) := by
  let R:=V42RuntimeWords.run g hg p hp hn hq K
  have hb : 2 ≤ V42UniversalPrefix.base g p := by unfold V42UniversalPrefix.base; omega
  have hpN : p ≤ V42UniversalPrefix.N p := (V38Cutoff.coefficient_le_power p).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (by omega))
  have hx : (V42UniversalPrefix.input (EncodedGraph.encode g) p K).length ≤
      2*(V42UniversalPrefix.base g p+K+1)^1 := by
    rw [pow_one,V42UniversalPrefix.input_length]
    unfold V42UniversalPrefix.base
    omega
  unfold machine exponent amplification
  exact V40PipelineRuntime.outputs V42UniversalPrefix.machine StoredMatrixEnvelopeStep.machine
    V42UniversalFormatter.machine 2 1 V42UniversalPrefix.baseCoefficient V42UniversalPrefix.degree
    StoredMatrixEnvelopeStep.coefficient StoredMatrixEnvelopeStep.degree
    V42UniversalFormatter.coefficient V42UniversalFormatter.degree
    (V42UniversalPrefix.base g p) K (V42UniversalPrefix.input (EncodedGraph.encode g) p K)
    (V42RuntimeWords.word g hg p K hp hn hq) (V42UniversalFormatter.word (4*p) K R)
    hb hx (V42UniversalPrefix.outputs_base g hg p K hp hn hq)
    (V42RuntimeWords.round_outputs g hg p K hp hn hq)
    (V42UniversalFormatter.outputs (4*p) K (V42RuntimeWords.context g hg p hp hn hq) R)

theorem outputs (Δ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) (p K : ℕ)
    (hp : 2 ≤ p) (hn : 0 < g.vertices) (hnN : g.vertices ≤ 2^(4*p))
    (hdeg : 2*g.edges.length ≤ Δ*g.vertices) (hΔ : 2*Δ ≤ p) :
    let R:=V42RuntimeWords.run g hg p hp hn (width Δ g p hnN hdeg hΔ) K
    machine.OutputsWithin (V42UniversalPrefix.input (EncodedGraph.encode g) p K)
      (V42UniversalFormatter.word (4*p) K R)
      ((V42UniversalPrefix.N p)^(C Δ*amplification^K)) ∧
    (V42UniversalFormatter.word (4*p) K R).length ≤
      (V42UniversalPrefix.N p)^(C Δ*amplification^K) := by
  have hN : 2 ≤ V42UniversalPrefix.N p := by
    change 2^1 ≤ 2^(4*p)
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega)
  have h:=outputs_base g hg p K hp hn (width Δ g p hnN hdeg hΔ)
  have hb:=V40GraphConstructorInputBounds.dyadic_clock_bound
    (V42UniversalPrefix.base g p) (V42UniversalPrefix.N p)
    ((V42UniversalPrefix.base g p)^(exponent*amplification^K)) (8*Δ+6)
    exponent amplification K hN (base_bound Δ g hg p hp hnN hdeg) le_rfl
  exact ⟨BitMachine.outputsWithin_mono _ h.1 hb,h.2.trans hb⟩

#print axioms outputs
#print axioms amplification_power

end
end CurrentAdditive.V42UniversalRuntime
