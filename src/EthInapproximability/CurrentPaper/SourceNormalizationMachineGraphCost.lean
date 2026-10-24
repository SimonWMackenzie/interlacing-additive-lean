import EthInapproximability.CurrentPaper.SourceNormalizationMachineGraphOutput

/-! Runtime bounds and the retained original-variable input bank for the
physical ordered graph normalizer. -/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineGraphCost

open Turing BitMachineEncoding

abbrev originalNStack : SourceNormalizationMachineGraphOutput.Stack :=
  .inl (.inl (.inl (.inl (.inl (.inr 2)))))

private theorem afterCount_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationMachineDecodeRepeat.afterCount g originalN).stk
        (.inr (2 : Fin 3)) =
      List.replicate originalN true := by
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeCount.countStack _ _
    (SourceNormalizationMachineDecodeCount.countStack (.inr (0 : Fin 3))) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

private theorem afterRepeat_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationMachineDecodeRankLocal.afterRepeat g originalN).stk
        (.inr (2 : Fin 3)) =
      List.replicate originalN true := by
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeRepeat.repeatStack _ _
    (SourceNormalizationMachineDecodeRepeat.repeatStack (4 : Fin 5)) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

private theorem afterRepeatHost_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationMachineDecodeRankLocal.afterRepeatHost g originalN).stk
        (.inl (.inr (2 : Fin 3))) =
      List.replicate originalN true := by
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeRankLocal.repeatStack _ _
    (SourceNormalizationMachineDecodeRankLocal.repeatStack (.inr (2 : Fin 3))) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact afterRepeat_originalN g originalN

private theorem afterRank_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationMachineDecodeDouble.afterRank g originalN).stk
        (.inl (.inr (2 : Fin 3))) =
      List.replicate originalN true := by
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeRankLocal.rankStack _ _
    (SourceNormalizationMachineDecodeRankLocal.rankStack (.inr (1 : Fin 5))) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

private theorem afterRankHost_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationMachineDecodeDouble.afterRankHost g originalN).stk
        (.inl (.inl (.inr (2 : Fin 3)))) =
      List.replicate originalN true := by
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeDouble.rankStack _ _
    (SourceNormalizationMachineDecodeDouble.rankStack (.inl (.inr (2 : Fin 3)))) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact afterRank_originalN g originalN

private theorem afterDouble_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationMachineDecodeDouble.finalHost g originalN).stk
        (.inl (.inl (.inr (2 : Fin 3)))) =
      List.replicate originalN true := by
  have ho : ¬ ∃ k : SourceNormalizationMachineDoubleUnary.Stack,
      SourceNormalizationMachineDecodeDouble.doubleStack k =
        (.inl (.inl (.inr (2 : Fin 3))) : SourceNormalizationMachineDecodeDouble.Stack) := by
    rintro ⟨k,hk⟩
    fin_cases k <;> simp [SourceNormalizationMachineDecodeDouble.doubleStack] at hk
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeDouble.doubleStack _ _ _ = _
  rw [BitMachineStackEmbedding.bank_outside _ _ _ _ ho]
  exact afterRankHost_originalN g originalN

private theorem afterDoubleHost_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationMachineDecodeShift.afterDoubleHost g originalN).stk
        (.inl (.inl (.inl (.inr (2 : Fin 3))))) =
      List.replicate originalN true := by
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeShift.doubleStack _ _
    (SourceNormalizationMachineDecodeShift.doubleStack
      (.inl (.inl (.inr (2 : Fin 3))))) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact afterDouble_originalN g originalN

private theorem afterShift_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationMachineDecodeVertices.afterShift g originalN).stk
        (.inl (.inl (.inl (.inr (2 : Fin 3))))) =
      List.replicate originalN true := by
  have ho : ¬ ∃ k : SourceNormalizationMachineShiftCopies.Stack,
      SourceNormalizationMachineDecodeShift.shiftStack k =
        (.inl (.inl (.inl (.inr (2 : Fin 3)))) :
          SourceNormalizationMachineDecodeShift.Stack) := by
    rintro ⟨k,hk⟩
    fin_cases k <;> simp [SourceNormalizationMachineDecodeShift.shiftStack] at hk
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeShift.shiftStack _ _ _ = _
  rw [BitMachineStackEmbedding.bank_outside _ _ _ _ ho]
  exact afterDoubleHost_originalN g originalN

private theorem afterVertices_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationMachineDecodeVertices.finalHost g originalN).stk
        (.inl (.inl (.inl (.inr (2 : Fin 3))))) =
      List.replicate originalN true := by
  have ho : ¬ ∃ k : SourceNormalizationMachineOffsetWidth.Stack,
      SourceNormalizationMachineDecodeVertices.offsetStack k =
        (.inl (.inl (.inl (.inr (2 : Fin 3)))) :
          SourceNormalizationMachineDecodeVertices.Stack) := by
    rintro ⟨k,hk⟩
    fin_cases k <;> simp [SourceNormalizationMachineDecodeVertices.offsetStack,
      SourceNormalizationMachineDecodeShift.shiftStack] at hk
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeVertices.offsetStack _ _ _ = _
  rw [BitMachineStackEmbedding.bank_outside _ _ _ _ ho]
  exact afterShift_originalN g originalN

private theorem afterDecodeWrite_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationMachineDecodeWrite.afterDecode g originalN).stk
        (.inl (.inl (.inl (.inl (.inr (2 : Fin 3)))))) =
      List.replicate originalN true := by
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeWrite.decodeStack _ _
    (SourceNormalizationMachineDecodeWrite.decodeStack
      (.inl (.inl (.inl (.inr (2 : Fin 3)))))) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact afterVertices_originalN g originalN

theorem afterWrite_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationMachineDecodeWrite.finalHost g originalN).stk
        (.inl (.inl (.inl (.inl (.inr (2 : Fin 3)))))) =
      List.replicate originalN true := by
  have ho : ¬ ∃ k : SourceNormalizationMachineEndpointWriter.Stack,
      SourceNormalizationMachineDecodeWrite.writerStack k =
        (.inl (.inl (.inl (.inl (.inr (2 : Fin 3))))) :
          SourceNormalizationMachineDecodeWrite.Stack) := by
    rintro ⟨k,hk⟩
    cases k with
    | inl k => fin_cases k <;> simp [SourceNormalizationMachineDecodeWrite.writerStack] at hk
    | inr k => fin_cases k <;> simp [SourceNormalizationMachineDecodeWrite.writerStack,
        SourceNormalizationMachineDecodeVertices.offsetStack,
        SourceNormalizationMachineDecodeShift.shiftStack] at hk
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeWrite.writerStack _ _ _ = _
  rw [BitMachineStackEmbedding.bank_outside _ _ _ _ ho]
  exact afterDecodeWrite_originalN g originalN

private theorem afterWriteHost_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationMachineGraphOutput.afterWrite g originalN).stk originalNStack =
      List.replicate originalN true := by
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineGraphOutput.decodeStack _ _
    (SourceNormalizationMachineGraphOutput.decodeStack
      (.inl (.inl (.inl (.inl (.inr (2 : Fin 3))))))) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact afterWrite_originalN g originalN

private theorem afterConvert_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationMachineGraphOutput.afterConvert g originalN).stk originalNStack =
      List.replicate originalN true := by
  have ho : ¬ ∃ k : BitMachineIteration.Stack SourceNormalizationMachineGraphOutput.counter,
      SourceNormalizationMachineGraphOutput.converterStack k = originalNStack := by
    rintro ⟨k,hk⟩
    cases k with
    | inl k => fin_cases k <;> simp [SourceNormalizationMachineGraphOutput.converterStack,
        originalNStack] at hk
    | inr k => fin_cases k <;> simp [SourceNormalizationMachineGraphOutput.converterStack,
        SourceNormalizationMachineDecodeWrite.writerStack, originalNStack] at hk
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineGraphOutput.converterStack _ _ _ = _
  rw [BitMachineStackEmbedding.bank_outside _ _ _ _ ho]
  exact afterWriteHost_originalN g originalN

theorem final_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationMachineGraphOutput.finalHost g originalN).stk originalNStack =
      List.replicate originalN true := by
  have ho : ¬ ∃ k : SourceClauseMachine.Stack,
      SourceNormalizationMachineGraphOutput.finalizerStack k = originalNStack := by
    rintro ⟨k,hk⟩
    fin_cases k <;> simp [SourceNormalizationMachineGraphOutput.finalizerStack,
      SourceNormalizationMachineDecodeVertices.offsetStack,
      SourceNormalizationMachineDecodeShift.shiftStack,
      SourceNormalizationMachineDecodeWrite.writerStack, originalNStack] at hk
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineGraphOutput.finalizerStack _ _ _ = _
  rw [BitMachineStackEmbedding.bank_outside _ _ _ _ ho]
  exact afterConvert_originalN g originalN

private theorem list_sum_le {xs : List ℕ} {M : ℕ}
    (h : ∀ x ∈ xs, x ≤ M) : xs.sum ≤ xs.length * M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : x ≤ M := h x (by simp)
      have hxs : ∀ y ∈ xs, y ≤ M := by
        intro y hy
        exact h y (List.mem_cons_of_mem x hy)
      have hi := ih hxs
      simp only [List.sum_cons, List.length_cons]
      nlinarith

private theorem endpointStream_length_le (xs : List ℕ) (M : ℕ)
    (h : ∀ x ∈ xs, x ≤ M) :
    (SourceNormalizationMachineMark.endpointStream xs).length ≤ xs.length * (M + 1) := by
  induction xs with
  | nil => simp [SourceNormalizationMachineMark.endpointStream]
  | cons x xs ih =>
      have hx : x ≤ M := h x (by simp)
      have hxs : ∀ y ∈ xs, y ≤ M := by
        intro y hy
        exact h y (List.mem_cons_of_mem x hy)
      have hi := ih hxs
      simp only [SourceNormalizationMachineMark.endpointStream,
        List.length_append, EncodedGraph.unary, List.length_replicate,
        List.length_cons, List.length_nil]
      nlinarith

def inputSize (g : EncodedGraph.Graph) (originalN : ℕ) : ℕ :=
  (EncodedGraph.encode g).length + originalN + 3

private theorem basic_bounds (g : EncodedGraph.Graph) (originalN : ℕ) :
    g.vertices ≤ inputSize g originalN ∧
      g.edges.length ≤ inputSize g originalN ∧
      originalN ≤ inputSize g originalN ∧
      SourceNormalizationNumeric.repetitions g originalN ≤ inputSize g originalN ∧
      (SourceNormalizationNumeric.support g).count true + 2 ≤ inputSize g originalN := by
  have hlen := EncodedGraph.encode_length_lower g
  have hr := ParameterizedNP.GuardedSourceGraph.copyCount_mul_le
    originalN g.edges.length
  have hcount : (SourceNormalizationNumeric.support g).count true ≤ g.vertices := by
    calc
      _ ≤ (SourceNormalizationNumeric.support g).length := List.count_le_length
      _ = g.vertices := SourceNormalizationNumeric.support_length g
  dsimp [inputSize, SourceNormalizationNumeric.repetitions]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · have hm : ParameterizedNP.GuardedSourceGraph.copyCount originalN g.edges.length ≤
        originalN + g.edges.length + 1 := by
      nlinarith [Nat.zero_le
        (ParameterizedNP.GuardedSourceGraph.copyCount originalN g.edges.length *
          g.edges.length)]
    omega
  · omega

private theorem rank_le_vertices (g : EncodedGraph.Graph) (u : ℕ) :
    SourceNormalizationNumeric.rank g u ≤ g.vertices := by
  calc
    _ ≤ ((SourceNormalizationNumeric.support g).take u).length := List.count_le_length
    _ ≤ (SourceNormalizationNumeric.support g).length := by simp
    _ = g.vertices := SourceNormalizationNumeric.support_length g

private theorem padded_edges_bounded (g : EncodedGraph.Graph) :
    ∀ p ∈ SourceNormalizationNumeric.paddedEdges g,
      p.1 ≤ g.vertices + 1 ∧ p.2 ≤ g.vertices + 1 := by
  intro p hp
  simp only [SourceNormalizationNumeric.paddedEdges, List.mem_append,
    List.mem_map, List.mem_singleton] at hp
  rcases hp with ⟨q, _, rfl⟩ | rfl
  · exact ⟨(rank_le_vertices g q.1).trans (by omega),
      (rank_le_vertices g q.2).trans (by omega)⟩
  · have hc : (SourceNormalizationNumeric.support g).count true ≤ g.vertices := by
      calc
        _ ≤ (SourceNormalizationNumeric.support g).length := List.count_le_length
        _ = g.vertices := SourceNormalizationNumeric.support_length g
    omega

private theorem numeric_size_bound (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationNumeric.numericGraph g originalN).vertices ≤
        (inputSize g originalN)^2 ∧
      (SourceNormalizationNumeric.numericGraph g originalN).edges.length ≤
        (inputSize g originalN)^2 := by
  obtain ⟨_,hm,_,hr,hw⟩ := basic_bounds g originalN
  constructor
  · rw [SourceNormalizationNumeric.numericGraph_vertices]
    simpa only [pow_two] using (Nat.mul_le_mul hr hw)
  · rw [SourceNormalizationNumeric.numericGraph_edges_length]
    have he : g.edges.length + 1 ≤ inputSize g originalN := by
      have hlen := EncodedGraph.encode_length_lower g
      dsimp [inputSize]
      omega
    simpa only [pow_two] using (Nat.mul_le_mul hr he)

private theorem numeric_edges_bounded (g : EncodedGraph.Graph) (originalN : ℕ) :
    ∀ p ∈ (SourceNormalizationNumeric.numericGraph g originalN).edges,
      p.1 ≤ (inputSize g originalN + 1)^2 ∧
      p.2 ≤ (inputSize g originalN + 1)^2 := by
  intro p hp
  let B := inputSize g originalN
  obtain ⟨hn,_,_,hr,hw⟩ := basic_bounds g originalN
  have hlocal := padded_edges_bounded g
  simp only [SourceNormalizationNumeric.numericGraph, List.mem_flatMap,
    List.mem_range, List.mem_map] at hp
  obtain ⟨k,hk,q,hq,hp⟩ := hp
  subst p
  have hq' := hlocal q hq
  have hwidth : (SourceNormalizationNumeric.support g).count true + 2 ≤ B := hw
  have hk' : k ≤ B := (Nat.le_of_lt hk).trans hr
  have hvertexPlus : g.vertices + 1 ≤ B := by
    have hlen := EncodedGraph.encode_length_lower g
    dsimp [B, inputSize]
    omega
  have hq1 : q.1 ≤ B := by omega
  have hq2 : q.2 ≤ B := by omega
  constructor <;> nlinarith [Nat.mul_le_mul hk' hwidth]

private theorem fieldCost_bound (u M : ℕ) (hu : u ≤ M) :
    SourceNormalizationMachineEndpointWriter.fieldCost u ≤
      (UnaryBinaryEncoding.coefficient + 4) * (M + 1)^2 := by
  have hb := UnaryBinaryEncoding.bits_length_le u
  have hq : u + 1 ≤ (u + 1)^2 := by nlinarith
  have hm : (u + 1)^2 ≤ (M + 1)^2 := by
    exact Nat.pow_le_pow_left (by omega) 2
  have hc := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hm
  dsimp [SourceNormalizationMachineEndpointWriter.fieldCost]
  nlinarith

private theorem edgesCost_bound (ps : List (ℕ × ℕ)) (M : ℕ)
    (h : ∀ p ∈ ps, p.1 ≤ M ∧ p.2 ≤ M) :
    SourceNormalizationMachineEndpointWriter.edgesCost ps ≤
      ps.length * (2 * (UnaryBinaryEncoding.coefficient + 4) * (M + 1)^2 + 2) := by
  induction ps with
  | nil => simp [SourceNormalizationMachineEndpointWriter.edgesCost]
  | cons p ps ih =>
      have hp := h p (by simp)
      have hps : ∀ q ∈ ps, q.1 ≤ M ∧ q.2 ≤ M := by
        intro q hq
        exact h q (List.mem_cons_of_mem p hq)
      have h₁ := fieldCost_bound p.1 M hp.1
      have h₂ := fieldCost_bound p.2 M hp.2
      have htail := ih hps
      simp only [SourceNormalizationMachineEndpointWriter.edgesCost,
        SourceNormalizationMachineEndpointWriter.edgeCost, List.length_cons]
      nlinarith

private theorem edgeFields_length_bound (ps : List (ℕ × ℕ)) (M : ℕ)
    (h : ∀ p ∈ ps, p.1 ≤ M ∧ p.2 ≤ M) :
    (EncodedGraph.edgeFields ps).length ≤ ps.length * (4 * M + 2) := by
  induction ps with
  | nil => simp [EncodedGraph.edgeFields]
  | cons p ps ih =>
      have hp := h p (by simp)
      have hps : ∀ q ∈ ps, q.1 ≤ M ∧ q.2 ≤ M := by
        intro q hq
        exact h q (List.mem_cons_of_mem p hq)
      have ht := ih hps
      have hb₁ := UnaryBinaryEncoding.bits_length_le p.1
      have hb₂ := UnaryBinaryEncoding.bits_length_le p.2
      simp only [EncodedGraph.edgeFields, List.length_append,
        EncodedCommunication.natField, EncodedCommunication.field_length,
        List.length_cons]
      nlinarith

private theorem repeatedIndices_length (g : EncodedGraph.Graph) (originalN : ℕ) :
    (SourceNormalizationMachineDecodeRepeat.repeatedIndices g originalN).length =
      SourceNormalizationNumeric.repetitions g originalN *
        (2 * (g.edges.length + 1)) := by
  simp [SourceNormalizationMachineDecodeRepeat.repeatedIndices,
    SourceNormalizationNumeric.paddedEndpoints,
    SourceNormalizationNumeric.endpoints_length, Nat.mul_add]

private theorem rankAt_le_length (bits : List Bool) (u : ℕ) :
    SourceNormalizationMachineRanks.rankAt bits u ≤ bits.length := by
  calc
    _ ≤ (bits.take u).length := List.count_le_length
    _ ≤ bits.length := by simp

private theorem rankedStream_length_bound (bits : List Bool)
    (indices : List ℕ) :
    (SourceNormalizationMachineRanks.rankedStream bits 0 indices).length ≤
      indices.length * (bits.length + 1) := by
  unfold SourceNormalizationMachineRanks.rankedStream
  have hm : ∀ u ∈ indices.map (fun u =>
      SourceNormalizationMachineRanks.rankAt bits u + 0), u ≤ bits.length := by
    intro u hu
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hu
    simpa using rankAt_le_length bits v
  have h := endpointStream_length_le
    (indices.map fun u => SourceNormalizationMachineRanks.rankAt bits u + 0)
    bits.length hm
  simpa using h

private theorem paddedStream_length_bound (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    (SourceNormalizationMachineDecodeRepeat.paddedStream g).length ≤
      2 * (g.edges.length + 1) * (inputSize g originalN + 1) := by
  rw [SourceNormalizationMachineDecodeRepeat.paddedStream_eq_mark]
  have he := SourceNormalizationNumeric.paddedEndpoints_bounded g hg
  have hs : (SourceNormalizationNumeric.paddedSupport g).length ≤
      inputSize g originalN := by
    have hlen := EncodedGraph.encode_length_lower g
    simp only [SourceNormalizationNumeric.paddedSupport_length, inputSize]
    omega
  have he' : ∀ x ∈ SourceNormalizationNumeric.paddedEndpoints g,
      x ≤ inputSize g originalN := by
    intro x hx
    exact (Nat.le_of_lt (he x hx)).trans hs
  have h := endpointStream_length_le
    (SourceNormalizationNumeric.paddedEndpoints g) (inputSize g originalN) he'
  simpa [SourceNormalizationNumeric.paddedEndpoints,
    SourceNormalizationNumeric.endpoints_length, Nat.mul_add] using h

private theorem rankCost_bound (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    SourceNormalizationMachineDecodeRankLocal.rankCost g originalN ≤
      2 * (inputSize g originalN)^2 *
        (6 * inputSize g originalN + 8) + 2 := by
  let B := inputSize g originalN
  let xs := SourceNormalizationMachineDecodeRepeat.repeatedIndices g originalN
  let bits := SourceNormalizationNumeric.paddedSupport g
  obtain ⟨_,_,_,hr,_⟩ := basic_bounds g originalN
  have he : g.edges.length + 1 ≤ B := by
    have hlen := EncodedGraph.encode_length_lower g
    dsimp [B, inputSize]
    omega
  have hl : xs.length ≤ 2 * B^2 := by
    dsimp [xs]
    rw [repeatedIndices_length]
    have hp := Nat.mul_le_mul hr he
    nlinarith
  have hbits : bits.length ≤ B := by
    have hlen := EncodedGraph.encode_length_lower g
    simp only [bits, SourceNormalizationNumeric.paddedSupport_length]
    dsimp [B, inputSize]
    omega
  have hx : ∀ x ∈ xs, x ≤ B := by
    intro x hx
    have h := SourceNormalizationMachineDecodeRepeat.repeatedIndices_bounded
      g hg originalN x hx
    exact (Nat.le_of_lt h).trans hbits
  have hs := list_sum_le hx
  have hout := rankedStream_length_bound bits xs
  have hs' : xs.sum ≤ (2 * B^2) * B :=
    hs.trans (Nat.mul_le_mul_right B hl)
  have hout' :
      (SourceNormalizationMachineRanks.rankedStream bits 0 xs).length ≤
        (2 * B^2) * (B + 1) := by
    exact hout.trans ((Nat.mul_le_mul_left xs.length (by omega)).trans
      (Nat.mul_le_mul_right (B + 1) hl))
  change 5 * xs.sum + 7 * xs.length +
    (SourceNormalizationMachineRanks.rankedStream bits 0 xs).length + 2 ≤
      2 * B^2 * (6 * B + 8) + 2
  nlinarith

private theorem graph_endpoint_length_bound (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    (SourceNormalizationMachineDecode.endpointStream g).length ≤
      2 * g.edges.length * (inputSize g originalN + 1) := by
  rw [SourceNormalizationMachineDecode.endpointStream_eq_mark]
  have he : ∀ x ∈ SourceNormalizationNumeric.endpoints g,
      x ≤ inputSize g originalN := by
    intro x hx
    have hb := (basic_bounds g originalN).1
    exact (Nat.le_of_lt (SourceNormalizationNumeric.endpoints_bounded g hg x hx)).trans hb
  have h := endpointStream_length_le
    (SourceNormalizationNumeric.endpoints g) (inputSize g originalN) he
  simpa [SourceNormalizationNumeric.endpoints_length] using h

theorem rankBound_polynomial (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    SourceNormalizationMachineDecodeDouble.rankBound g originalN ≤
      1000 * (inputSize g originalN + 1)^4 := by
  let B := inputSize g originalN
  obtain ⟨hn,hm,hn₀,hr,_⟩ := basic_bounds g originalN
  have he := graph_endpoint_length_bound g hg originalN
  have hpad := paddedStream_length_bound g hg originalN
  have hrank := rankCost_bound g hg originalN
  change SourceNormalizationMachineDecodeRankLocal.rankCost g originalN ≤
    2 * B^2 * (6 * B + 8) + 2 at hrank
  have hmark := SourceNormalizationNumeric.mark_cost_bound g hg
  have hgraph : SourceNormalizationMachineDecode.graphCost g ≤
      100 * (B + 1)^3 := by
    have hh := SourceNormalizationMachineDecode.graphCost_polynomial g hg
    have hc : (EncodedGraph.encode g).length + 1 ≤ B + 1 := by
      dsimp [B, inputSize]
      omega
    exact hh.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hc 3))
  have hedge : g.edges.length + 1 ≤ B := by
    have hh := EncodedGraph.encode_length_lower g
    dsimp [B, inputSize]
    omega
  have hpad' : (SourceNormalizationMachineDecodeRepeat.paddedStream g).length ≤
      2 * B * (B + 1) :=
    hpad.trans (Nat.mul_le_mul_right (B + 1)
      (by omega : 2 * (g.edges.length + 1) ≤ 2 * B))
  have he' : (SourceNormalizationMachineDecode.endpointStream g).length ≤
      2 * B * (B + 1) :=
    he.trans (Nat.mul_le_mul_right (B + 1) (by omega : 2 * g.edges.length ≤ 2 * B))
  have hrep :
      SourceNormalizationNumeric.repetitions g originalN *
        (2 * (SourceNormalizationMachineDecodeRepeat.paddedStream g).length + 3) + 1 ≤
      B * (4 * B * (B + 1) + 3) + 1 := by
    have hterm : 2 * (SourceNormalizationMachineDecodeRepeat.paddedStream g).length + 3 ≤
        4 * B * (B + 1) + 3 := by nlinarith
    exact Nat.add_le_add_right
      (Nat.mul_le_mul hr hterm) 1
  have hcore : SourceNormalizationMachineDecodeCore.coreCost g ≤
      4 * B + 7 + 10 * B * (B + 1) := by
    dsimp [SourceNormalizationMachineDecodeCore.coreCost]
    nlinarith [Nat.mul_le_mul hm (by omega : g.vertices + 1 ≤ B + 1)]
  have hpadCost : SourceNormalizationMachineDecodePad.padCost g ≤
      2 * B + 7 + 4 * B * (B + 1) := by
    dsimp [SourceNormalizationMachineDecodePad.padCost]
    nlinarith
  have hgoal :
      100 * (B + 1)^3 +
        (2 * B + 7 + 4 * B * (B + 1)) +
        (4 * B + 7 + 10 * B * (B + 1)) +
        (10 * B + 13 * B + 13) +
        (B * (4 * B * (B + 1) + 3) + 1) +
        (2 * B^2 * (6 * B + 8) + 2) ≤
      1000 * (B + 1)^4 := by
    nlinarith [Nat.zero_le (B^4)]
  calc
    SourceNormalizationMachineDecodeDouble.rankBound g originalN ≤
      100 * (B + 1)^3 +
        (2 * B + 7 + 4 * B * (B + 1)) +
        (4 * B + 7 + 10 * B * (B + 1)) +
        (10 * B + 13 * B + 13) +
        (B * (4 * B * (B + 1) + 3) + 1) +
        (2 * B^2 * (6 * B + 8) + 2) := by
          simp only [SourceNormalizationMachineDecodeDouble.rankBound]
          omega
    _ ≤ 1000 * (B + 1)^4 := hgoal

private theorem copiesCost_bound (xs : List ℕ) (bits : List Bool)
    (offset r : ℕ) :
    SourceNormalizationMachineShiftCopies.copiesCost xs bits offset r ≤
      r * (xs.sum + (2 * (offset + r * bits.length) + 5) * xs.length +
        2 * bits.length + xs.length + 5) := by
  induction r generalizing offset with
  | zero => simp [SourceNormalizationMachineShiftCopies.copiesCost]
  | succ r ih =>
      cases r with
      | zero =>
          simp only [SourceNormalizationMachineShiftCopies.copiesCost,
            SourceNormalizationMachineShiftCopies.blockCost,
            Nat.zero_add, Nat.one_mul]
          nlinarith
      | succ r =>
          have hcount : bits.count true ≤ bits.length := List.count_le_length
          have hmono :
              xs.sum +
                  (2 * (offset + bits.count true + (r + 1) * bits.length) + 5) *
                    xs.length + 2 * bits.length + xs.length + 5 ≤
                xs.sum +
                  (2 * (offset + (r + 2) * bits.length) + 5) * xs.length +
                    2 * bits.length + xs.length + 5 := by
            nlinarith [Nat.zero_le xs.length]
          have hi := ih (offset + bits.count true)
          have hi' := hi.trans (Nat.mul_le_mul_left (r + 1) hmono)
          let C := xs.sum + (2 * (offset + (r + 2) * bits.length) + 5) *
            xs.length + 2 * bits.length + xs.length + 5
          have hblock :
              SourceNormalizationMachineShiftCopies.blockCost xs offset +
                  (2 * bits.length + xs.length + 5) ≤ C := by
            dsimp [C, SourceNormalizationMachineShiftCopies.blockCost]
            nlinarith [Nat.zero_le ((r + 2) * bits.length * xs.length)]
          calc
            SourceNormalizationMachineShiftCopies.copiesCost xs bits offset (r + 2) =
                SourceNormalizationMachineShiftCopies.blockCost xs offset +
                  (2 * bits.length + xs.length + 5) +
                  SourceNormalizationMachineShiftCopies.copiesCost xs bits
                    (offset + bits.count true) (r + 1) := rfl
            _ ≤ C + (r + 1) * C := Nat.add_le_add hblock hi'
            _ = (r + 2) * C := by ring

private theorem shifted_length_bound (xs : List ℕ) (M offset : ℕ)
    (h : ∀ x ∈ xs, x ≤ M) :
    (SourceNormalizationMachineShiftCopies.shifted xs offset).length ≤
      xs.length * (M + offset + 1) := by
  unfold SourceNormalizationMachineShiftCopies.shifted
  have hm : ∀ x ∈ xs.map (· + offset), x ≤ M + offset := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact Nat.add_le_add_right (h y hy) offset
  simpa only [List.length_map] using
    endpointStream_length_le (xs.map (· + offset)) (M + offset) hm

private theorem shiftedFrom_length_bound (xs : List ℕ) (M width offset r : ℕ)
    (h : ∀ x ∈ xs, x ≤ M) :
    (SourceNormalizationMachineShiftCopies.shiftedFrom xs width offset r).length ≤
      r * xs.length * (M + offset + r * width + 1) := by
  induction r generalizing offset with
  | zero => simp [SourceNormalizationMachineShiftCopies.shiftedFrom]
  | succ r ih =>
      have hhead := shifted_length_bound xs M offset h
      have htail := ih (offset + width)
      have htail' :
          (SourceNormalizationMachineShiftCopies.shiftedFrom xs width
            (offset + width) r).length ≤
            r * xs.length * (M + offset + (r + 1) * width + 1) := by
        convert htail using 1; ring
      have hmono : xs.length * (M + offset + 1) ≤
          xs.length * (M + offset + (r + 1) * width + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      calc
        (SourceNormalizationMachineShiftCopies.shiftedFrom xs width offset (r + 1)).length =
            (SourceNormalizationMachineShiftCopies.shifted xs offset).length +
              (SourceNormalizationMachineShiftCopies.shiftedFrom xs width
                (offset + width) r).length := by
                  simp only [SourceNormalizationMachineShiftCopies.shiftedFrom,
                    List.length_append]
        _ ≤ xs.length * (M + offset + (r + 1) * width + 1) +
              r * xs.length * (M + offset + (r + 1) * width + 1) :=
                Nat.add_le_add (hhead.trans hmono) htail'
        _ = (r + 1) * xs.length * (M + offset + (r + 1) * width + 1) := by ring

theorem shiftCost_polynomial (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineDecodeShift.shiftCost g originalN ≤
      1000 * (inputSize g originalN + 1)^5 := by
  let B := inputSize g originalN
  let xs := SourceNormalizationMachineDecodeShift.localIndices g
  let bits := SourceNormalizationMachineDecodeShift.localBits g
  let r := SourceNormalizationMachineDecodeShift.copies g originalN
  obtain ⟨_,_,_,hr,_⟩ := basic_bounds g originalN
  have hr' : r ≤ B := hr
  have hbits : bits.length ≤ B := by
    have hlen := EncodedGraph.encode_length_lower g
    simp only [bits, SourceNormalizationMachineDecodeShift.localBits,
      SourceNormalizationNumeric.paddedSupport_length]
    dsimp [B, inputSize]
    omega
  have hwidth : bits.count true ≤ B :=
    (List.count_le_length).trans hbits
  have hlen : xs.length ≤ 2 * B := by
    rw [SourceNormalizationMachineDecodeShift.localIndices_length]
    have he := EncodedGraph.encode_length_lower g
    dsimp [B, inputSize]
    omega
  have hx : ∀ x ∈ xs, x ≤ B := by
    intro x hx
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp
      (show x ∈ (SourceNormalizationNumeric.paddedEndpoints g).map
        (SourceNormalizationMachineRanks.rankAt
          (SourceNormalizationNumeric.paddedSupport g)) by
        simpa only [xs, SourceNormalizationMachineDecodeShift.localIndices] using hx)
    exact (rankAt_le_length _ v).trans hbits
  have hsum : xs.sum ≤ 2 * B^2 := by
    have h := list_sum_le hx
    exact h.trans (by nlinarith [Nat.mul_le_mul_right B hlen])
  have hrbits : r * bits.length ≤ B^2 := by
    simpa only [pow_two] using (Nat.mul_le_mul hr' hbits)
  have hrwidth : r * bits.count true ≤ B^2 := by
    simpa only [pow_two] using (Nat.mul_le_mul hr' hwidth)
  have hbase : xs.sum + (2 * (0 + r * bits.length) + 5) * xs.length +
      2 * bits.length + xs.length + 5 ≤
      2 * B^2 + (2 * B^2 + 5) * (2 * B) + 4 * B + 5 := by
    have hp := Nat.mul_le_mul
      (by omega : 2 * (0 + r * bits.length) + 5 ≤ 2 * B^2 + 5) hlen
    omega
  have hcost : SourceNormalizationMachineShiftCopies.copiesCost xs bits 0 r ≤
      B * (2 * B^2 + (2 * B^2 + 5) * (2 * B) + 4 * B + 5) := by
    exact (copiesCost_bound xs bits 0 r).trans (Nat.mul_le_mul hr' hbase)
  have hshift :
      (SourceNormalizationMachineShiftCopies.shiftedFrom xs (bits.count true) 0 r).length ≤
        B * (2 * B) * (B + B^2 + 1) := by
    have h := shiftedFrom_length_bound xs B (bits.count true) 0 r hx
    have hm : B + 0 + r * bits.count true + 1 ≤ B + B^2 + 1 := by omega
    have hleft := Nat.mul_le_mul hr' hlen
    exact h.trans (by
      calc
        r * xs.length * (B + 0 + r * bits.count true + 1) ≤
            (B * (2 * B)) * (B + B^2 + 1) :=
              Nat.mul_le_mul hleft hm
        _ = B * (2 * B) * (B + B^2 + 1) := rfl)
  have hpoly :
      B * (2 * B^2 + (2 * B^2 + 5) * (2 * B) + 4 * B + 5) +
        B * (2 * B) * (B + B^2 + 1) + 2 ≤
      1000 * (B + 1)^5 := by
    nlinarith [Nat.zero_le (B^5)]
  calc
    SourceNormalizationMachineDecodeShift.shiftCost g originalN ≤
      B * (2 * B^2 + (2 * B^2 + 5) * (2 * B) + 4 * B + 5) +
        B * (2 * B) * (B + B^2 + 1) + 2 := by
          change SourceNormalizationMachineShiftCopies.copiesCost xs bits 0 r +
            (SourceNormalizationMachineShiftCopies.shiftedFrom xs
              (bits.count true) 0 r).length + 2 ≤ _
          omega
    _ ≤ 1000 * (B + 1)^5 := hpoly

theorem totalBound_polynomial (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    SourceNormalizationMachineGraphOutput.totalBound g originalN ≤
      10000 * (UnaryBinaryEncoding.coefficient + 5) *
        (inputSize g originalN + 1)^8 := by
  let B := inputSize g originalN
  let D := B + 1
  let c := UnaryBinaryEncoding.coefficient
  let h := SourceNormalizationNumeric.numericGraph g originalN
  have hrank := rankBound_polynomial g hg originalN
  change SourceNormalizationMachineDecodeDouble.rankBound g originalN ≤
    1000 * D^4 at hrank
  have hshift := shiftCost_polynomial g originalN
  change SourceNormalizationMachineDecodeShift.shiftCost g originalN ≤
    1000 * D^5 at hshift
  obtain ⟨hvertices,hedges⟩ := numeric_size_bound g originalN
  change h.vertices ≤ B^2 at hvertices
  change h.edges.length ≤ B^2 at hedges
  have hedges' : h.edges.length ≤ D^2 :=
    hedges.trans (Nat.pow_le_pow_left (by omega : B ≤ D) 2)
  have hvertices' : h.vertices ≤ D^2 :=
    hvertices.trans (Nat.pow_le_pow_left (by omega : B ≤ D) 2)
  have hend : ∀ p ∈ h.edges, p.1 ≤ D^2 ∧ p.2 ≤ D^2 := by
    simpa only [D] using numeric_edges_bounded g originalN
  have hwriter : SourceNormalizationMachineEndpointWriter.edgesCost h.edges ≤
      D^2 * (2 * (c + 4) * (D^2 + 1)^2 + 2) :=
    (edgesCost_bound h.edges (D^2) hend).trans
      (Nat.mul_le_mul_right _ hedges')
  have hfields : (EncodedGraph.edgeFields h.edges).length ≤
      D^2 * (4 * D^2 + 2) :=
    (edgeFields_length_bound h.edges (D^2) hend).trans
      (Nat.mul_le_mul_right _ hedges')
  have hconvert : c * (h.edges.length + 1)^2 ≤
      c * (D^2 + 1)^2 :=
    Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) 2)
  have hfinalizer : SourceNormalizationMachineGraphOutput.finalizerTime g originalN ≤
      D^2 * (4 * D^2 + 2) + 4 * D^2 + 5 := by
    have hb := UnaryBinaryEncoding.bits_length_le h.edges.length
    change (EncodedGraph.edgeFields h.edges).length +
      3 * h.edges.length.bits.length + h.vertices + 5 ≤ _
    omega
  have hlocal : (SourceNormalizationMachineDecodeVertices.localBits g).length ≤ B := by
    have hlen := EncodedGraph.encode_length_lower g
    simp only [SourceNormalizationMachineDecodeVertices.localBits,
      SourceNormalizationMachineDecodeShift.localBits,
      SourceNormalizationNumeric.paddedSupport_length]
    dsimp [B, inputSize]
    omega
  have hm : g.edges.length + 1 ≤ B := by
    have hlen := EncodedGraph.encode_length_lower g
    dsimp [B, inputSize]
    omega
  have hagg :
      SourceNormalizationMachineGraphOutput.totalBound g originalN ≤
        1000 * D^4 + 2 * B + 2 + 1000 * D^5 + 2 * B + 2 +
        D^2 * (2 * (c + 4) * (D^2 + 1)^2 + 2) + 1 +
        c * (D^2 + 1)^2 +
        (D^2 * (4 * D^2 + 2) + 4 * D^2 + 5) := by
    change SourceNormalizationMachineDecodeDouble.rankBound g originalN +
      2 * (g.edges.length + 1) + 2 +
      SourceNormalizationMachineDecodeShift.shiftCost g originalN +
      2 * (SourceNormalizationMachineDecodeVertices.localBits g).length + 2 +
      SourceNormalizationMachineEndpointWriter.edgesCost h.edges + 1 +
      c * (h.edges.length + 1)^2 +
      SourceNormalizationMachineGraphOutput.finalizerTime g originalN ≤ _
    omega
  have hpoly :
      1000 * D^4 + 2 * B + 2 + 1000 * D^5 + 2 * B + 2 +
        D^2 * (2 * (c + 4) * (D^2 + 1)^2 + 2) + 1 +
        c * (D^2 + 1)^2 +
        (D^2 * (4 * D^2 + 2) + 4 * D^2 + 5) ≤
      10000 * (c + 5) * D^8 := by
    dsimp [D]
    nlinarith [Nat.zero_le B, Nat.zero_le (B^2), Nat.zero_le (B^3),
      Nat.zero_le (B^4), Nat.zero_le (B^5), Nat.zero_le (B^6),
      Nat.zero_le (B^7), Nat.zero_le (B^8),
      Nat.zero_le c, Nat.zero_le (c * B), Nat.zero_le (c * B^2),
      Nat.zero_le (c * B^3), Nat.zero_le (c * B^4),
      Nat.zero_le (c * B^5), Nat.zero_le (c * B^6),
      Nat.zero_le (c * B^7), Nat.zero_le (c * B^8)]
  exact hagg.trans hpoly

/-- A closed polynomial transition clock for the complete physical normalizer
and canonical graph serializer on valid encoded graphs. The original SAT
variable count is a separate unary input bank throughout. -/
theorem graph_output_polynomial_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ 10000 * (UnaryBinaryEncoding.coefficient + 5) *
        ((EncodedGraph.encode g).length + originalN + 4)^8,
      SourceNormalizationMachineGraphOutput.run t
        (SourceNormalizationMachineGraphOutput.start
          (EncodedGraph.encode g) originalN) =
        SourceNormalizationMachineGraphOutput.finalHost g originalN := by
  obtain ⟨t,ht,hr⟩ := SourceNormalizationMachineGraphOutput.graph_output_run
    g hg originalN
  refine ⟨t, ?_, hr⟩
  exact ht.trans (by simpa [inputSize] using totalBound_polynomial g hg originalN)

end EthInapproximability.CurrentPaper.SourceNormalizationMachineGraphCost
