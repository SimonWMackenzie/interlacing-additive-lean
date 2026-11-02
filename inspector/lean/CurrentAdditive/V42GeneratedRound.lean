import CurrentAdditive.V42RuntimeWords
import CurrentAdditive.StoredMatrixPhysicalStep
import CurrentAdditive.GaussCellPolynomialClock

/-! Per-round polynomiality for every explicit stored rational base matrix.
The fixed graph context is computed by the actual public source producer;
the base matrix and its complete rational encoding are universally quantified. -/
namespace CurrentAdditive.V42GeneratedRound
noncomputable section

open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction V42Schedule
open GaussCellPolynomialClock

def rawCap (Δ N : ℕ) := (32*(Δ+1)+32)*(N+1)^2
def scalarCap (Δ N : ℕ) := V42RuntimePacket.sizeCoefficient*
  (N+rawCap Δ N+1)^V42RuntimePacket.sizeDegree
def sourceCap (Δ N : ℕ) := V42RuntimeSource.coefficient*
  (scalarCap Δ N+1)^V42RuntimeSource.degree
def inputCap (Δ N len : ℕ) := 2*sourceCap Δ N+2*len+2
def clockCap (Δ N len : ℕ) := StoredMatrixPhysicalStep.coefficient*
  (inputCap Δ N len+1)^StoredMatrixPhysicalStep.degree

theorem clockCap_polynomial (Δ : ℕ) : PolynomialBound (clockCap Δ) := by
  have hr : PolynomialBound (fun N _ => rawCap Δ N) :=
    mul (constant _) (power (add first (constant 1)) 2)
  have hs : PolynomialBound (fun N _ => scalarCap Δ N) :=
    mul (constant _) (power (add (add first hr) (constant 1)) _)
  have hsrc : PolynomialBound (fun N _ => sourceCap Δ N) :=
    mul (constant _) (power (add hs (constant 1)) _)
  have hi : PolynomialBound (inputCap Δ) :=
    add (add (mul (constant 2) hsrc) (mul (constant 2) second)) (constant 2)
  exact mul (constant _) (power (add hi (constant 1)) _)

theorem raw_length (g : EncodedGraph.Graph) (hg : g.Valid) (k Δ : ℕ)
    (hnN : g.vertices ≤ V42PublicSchedule.generatedN k)
    (hdeg : 2*g.edges.length ≤ Δ*g.vertices) :
    (V42RuntimePacket.input (EncodedGraph.encode g) g.vertices g.edges.length k 0).length ≤
      rawCap Δ (V42PublicSchedule.generatedN k) := by
  let N:=V42PublicSchedule.generatedN k
  change g.vertices ≤ N at hnN
  have hsk : 2^k ≤ N := by
    dsimp only [N]
    rw [V42PublicSchedule.generatedN_exact]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hkN : k ≤ N := (V38Cutoff.coefficient_le_power k).trans hsk
  have hm : g.edges.length ≤ Δ*N := by
    have h := hdeg.trans (Nat.mul_le_mul_left Δ hnN)
    omega
  have henc := EncodedGraph.encode_length_upper g hg
  have hprod := Nat.mul_le_mul hm (by omega : 4*g.vertices+4 ≤ 4*N+4)
  simp only [V42RuntimePacket.input,V42RuntimePacket.rawWords,BitMachineBankCodec.encode_length,
    Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,
    Fin.sum_univ_zero,List.length_replicate,List.length_nil,Nat.add_zero]
  change _ ≤ rawCap Δ N
  unfold rawCap
  nlinarith only [hnN,hkN,hm,henc,hprod]

theorem scalar_length (g : EncodedGraph.Graph) (hg : g.Valid) (k Δ : ℕ)
    (hnN : g.vertices ≤ V42PublicSchedule.generatedN k)
    (hdeg : 2*g.edges.length ≤ Δ*g.vertices) :
    (V42RuntimeSource.input g k 0).length ≤ scalarCap Δ (V42PublicSchedule.generatedN k) := by
  have h := V42RuntimePacket.output_length (EncodedGraph.encode g) g.vertices g.edges.length k 0
  have hraw := raw_length g hg k Δ hnN hdeg
  have hs : 2^k ≤ V42PublicSchedule.generatedN k := by
    rw [V42PublicSchedule.generatedN_exact]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

theorem context_length_le (graph : List Bool) (n m k : ℕ) (law activity : List Bool) :
    (V42RuntimePacket.context k law activity).length ≤
      (V42RuntimePacket.withSource graph n m k 0 law activity).length := by
  simp only [V42RuntimePacket.context,V42RuntimePacket.withSource,V42RuntimePacket.withSourceWords,
    BitMachineBankCodec.encode_length,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_one,Fin.sum_univ_zero,List.length_replicate,List.length_nil,Nat.add_zero]
  omega

theorem context_length (g : EncodedGraph.Graph) (hg : g.Valid) (k Δ : ℕ)
    (hk : 2 ≤ k) (hn : 0 < g.vertices)
    (hnN : g.vertices ≤ V42PublicSchedule.generatedN k)
    (hdeg : 2*g.edges.length ≤ Δ*g.vertices)
    (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
      (V42RuntimePacket.repetition k g.edges.length)) :
    (V42RuntimeWords.context g hg k hk hn hq).length ≤ sourceCap Δ (V42PublicSchedule.generatedN k) := by
  letI : NeZero (s k) := ⟨(s_pos k).ne'⟩
  have hs := V42GeneratedConstruction.s_ge_four k hk
  have he := V42RuntimeSource.envelope (V42RuntimeSource.input g k 0)
  rw [V42RuntimeSource.result g hg k 0 hn hs hq] at he
  have hout : (V42RuntimeSource.output g hg k 0 hn hs hq).length ≤
      V42RuntimeSource.coefficient*((V42RuntimeSource.input g k 0).length+1)^V42RuntimeSource.degree := by omega
  have hb := scalar_length g hg k Δ hnN hdeg
  have hsource := hout.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) _))
  exact (context_length_le (EncodedGraph.encode g) g.vertices g.edges.length k
    (V42RuntimeSource.lawBytes g k hn hs) (V42RuntimeSource.activityBytes g hg k hs hq)).trans hsource

def input (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (hk : 2 ≤ k) (hn : 0 < g.vertices)
    (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
      (V42RuntimePacket.repetition k g.edges.length)) (R : StoredMatrix) :=
  StoredStepContext.packet (q₁ k) (w k) (Q k) (V42RuntimeWords.law g k hk hn)
    (V42RuntimeWords.activity g hg k hk hq) R

def output (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (hk : 2 ≤ k) (hn : 0 < g.vertices)
    (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
      (V42RuntimePacket.repetition k g.edges.length)) (R : StoredMatrix) :=
  input g hg k hk hn hq (V42GeneratedConstruction.storedStep k (4*k) hk
    (V42RuntimeWords.law g k hk hn) (V42RuntimeWords.activity g hg k hk hq) R)

theorem input_length (g : EncodedGraph.Graph) (hg : g.Valid) (k Δ : ℕ)
    (hk : 2 ≤ k) (hn : 0 < g.vertices)
    (hnN : g.vertices ≤ V42PublicSchedule.generatedN k)
    (hdeg : 2*g.edges.length ≤ Δ*g.vertices)
    (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
      (V42RuntimePacket.repetition k g.edges.length)) (R : StoredMatrix) :
    (input g hg k hk hn hq R).length ≤
      inputCap Δ (V42PublicSchedule.generatedN k) (StoredWeightedState.encode R).length := by
  have hc := context_length g hg k Δ hk hn hnN hdeg hq
  simp only [input,StoredStepContext.packet,BitMachineBankCodec.encode_length,
    Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,
    Fin.sum_univ_zero,Nat.add_zero]
  change _ ≤ inputCap Δ (V42PublicSchedule.generatedN k) (StoredWeightedState.encode R).length
  unfold inputCap
  change (StoredStepContext.context _ _ _ _ _).length ≤ _ at hc
  omega

theorem one_round_outputs (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ)
    (hk : 2 ≤ k) (hn : 0 < g.vertices)
    (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
      (V42RuntimePacket.repetition k g.edges.length)) (R : StoredMatrix) :
    StoredMatrixPhysicalStep.machine.OutputsWithin (input g hg k hk hn hq R)
      (output g hg k hk hn hq R)
      (StoredMatrixPhysicalStep.coefficient*((input g hg k hk hn hq R).length+1)^StoredMatrixPhysicalStep.degree) :=
  StoredMatrixPhysicalStep.outputs (V42RuntimeWords.data g hg k hk hn hq R)

/-- Constants are fixed before graph, dyadic parameter, arbitrary rational
base matrix, or round number. The complete base-law bit encoding is charged. -/
theorem one_round_polynomial (Δ : ℕ) : ∃ C E : ℕ,
    ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (hk : 2 ≤ k) (hn : 0 < g.vertices)
      (hnN : g.vertices ≤ V42PublicSchedule.generatedN k)
      (hdeg : 2*g.edges.length ≤ Δ*g.vertices)
      (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
        (V42RuntimePacket.repetition k g.edges.length)) (R : StoredMatrix),
    StoredMatrixPhysicalStep.machine.OutputsWithin (input g hg k hk hn hq R)
      (output g hg k hk hn hq R)
      (C*(V42PublicSchedule.generatedN k+(StoredWeightedState.encode R).length+1)^E) := by
  obtain ⟨C,E,hpoly⟩ := clockCap_polynomial Δ
  refine ⟨C,E,?_⟩
  intro g hg k hk hn hnN hdeg hq R
  apply BitMachine.outputsWithin_mono _ (one_round_outputs g hg k hk hn hq R)
  have hi := input_length g hg k Δ hk hn hnN hdeg hq R
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) _)).trans
    (hpoly (V42PublicSchedule.generatedN k) (StoredWeightedState.encode R).length)

#print axioms context_length
#print axioms one_round_outputs
#print axioms one_round_polynomial

end
end CurrentAdditive.V42GeneratedRound

