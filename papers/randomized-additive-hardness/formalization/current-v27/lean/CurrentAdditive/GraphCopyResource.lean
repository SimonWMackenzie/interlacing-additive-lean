import CurrentAdditive.GraphCopyEncoded
import CurrentAdditive.GraphUnaryPrinterBounds

/-!
Selected v39 sources.tex:69-78, charged polynomial clock for the actual program.
The generic list/shift arithmetic lemmas below are copied into this private
namespace from SourceNormalizationMachineGraphCost.lean lines190-217,531-612,
SHA C1D24214F785FA27E77FFF48978EC7EBB30E49B18FB99DFEB4F4B6176003521B.
They are reproved here for this actual original-graph stream and count; the old
normalization pipeline and its mathematical constructor are not substituted.
-/
namespace Paper2.CurrentAdditive.GraphCopyResource
open EthInapproximability.CurrentPaper
open Paper2.CurrentAdditive.GraphCopyPadding
open Paper2.CurrentAdditive.GraphCopyMachineStages
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

theorem endpoint_bounded (g : EncodedGraph.Graph) (hg : g.Valid)
    (B : ℕ) (hn : g.vertices ≤ B) : ∀ x ∈ endpointList g, x ≤ B := by
  intro x hx
  obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
  simp at hx
  rcases hx with rfl | rfl
  · exact (hg p hp).1.le.trans hn
  · exact (hg p hp).2.1.le.trans hn

theorem shiftBound_polynomial (g : EncodedGraph.Graph) (hg : g.Valid)
    (c B : ℕ) (hc : c ≤ B) (hn : g.vertices ≤ B) (hm : g.edges.length ≤ B) :
    GraphShiftPrinter.shiftBound g c ≤ 1000 * (B + 1)^5 := by
  let xs := endpointList g
  let bits := List.replicate g.vertices true
  let r := c
  have hr' : r ≤ B := hc
  have hbits : bits.length ≤ B := by simpa [bits] using hn
  have hwidth : bits.count true ≤ B := (List.count_le_length).trans hbits
  have hlen : xs.length ≤ 2 * B := by
    rw [GraphRepeatPrinter.endpointList_length]
    omega
  have hx : ∀ x ∈ xs, x ≤ B := endpoint_bounded g hg B hn
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
      B * (2 * B^2 + (2 * B^2 + 5) * (2 * B) + 4 * B + 5) :=
    (copiesCost_bound xs bits 0 r).trans (Nat.mul_le_mul hr' hbase)
  have hshift :
      (SourceNormalizationMachineShiftCopies.shiftedFrom xs (bits.count true) 0 r).length ≤
        B * (2 * B) * (B + B^2 + 1) := by
    have h := shiftedFrom_length_bound xs B (bits.count true) 0 r hx
    have hm' : B + 0 + r * bits.count true + 1 ≤ B + B^2 + 1 := by omega
    exact h.trans (by
      calc
        r * xs.length * (B + 0 + r * bits.count true + 1) ≤
            (B * (2 * B)) * (B + B^2 + 1) :=
              Nat.mul_le_mul (Nat.mul_le_mul hr' hlen) hm'
        _ = _ := rfl)
  have hpoly :
      B * (2 * B^2 + (2 * B^2 + 5) * (2 * B) + 4 * B + 5) +
        B * (2 * B) * (B + B^2 + 1) + 2 ≤ 1000 * (B + 1)^5 := by
    nlinarith [Nat.zero_le (B^5)]
  have hbound : SourceNormalizationMachineShiftCopies.copiesCost xs bits 0 r +
      (SourceNormalizationMachineShiftCopies.shiftedFrom xs (bits.count true) 0 r).length + 2 ≤
      1000 * (B + 1)^5 := by omega
  unfold GraphShiftPrinter.shiftBound
  rw [← shifted_eq_copied_unary]
  simpa only [xs, bits, r, List.count_replicate_self] using hbound

theorem repeatBound_polynomial (g : EncodedGraph.Graph) (hg : g.Valid)
    (c B : ℕ) (hc : c ≤ B) (hn : g.vertices ≤ B) (hm : g.edges.length ≤ B) :
    GraphRepeatPrinter.totalBound g c ≤
      (200 * UnaryBinaryEncoding.coefficient + 5000) * (B + 1)^6 := by
  have hs := shiftBound_polynomial g hg c B hc hn hm
  have hstream : (GraphRepeatPrinter.originalStream g).length ≤ 2 * B * (B + 1) := by
    unfold GraphRepeatPrinter.originalStream
    rw [unaryEdges_eq_endpointList]
    have h := endpointStream_length_le (endpointList g) B (endpoint_bounded g hg B hn)
    rw [GraphRepeatPrinter.endpointList_length] at h
    exact h.trans (by gcongr)
  have hrepeat : c * (2 * (GraphRepeatPrinter.originalStream g).length + 3) + 1 ≤
      10 * (B + 1)^3 := by
    have h := Nat.mul_le_mul hc (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hstream) 3)
    nlinarith
  have hprinter := GraphUnaryPrinter.totalBound_polynomial (encodedCopies g c)
    (encodedCopies_valid g hg c)
  have hsize : (encodedCopies g c).vertices + (encodedCopies g c).edges.length + 1 ≤
      3 * (B + 1)^2 := by
    rw [encodedCopies_edges_length]
    change c * g.vertices + c * g.edges.length + 1 ≤ _
    have hcn := Nat.mul_le_mul hc hn
    have hcm := Nat.mul_le_mul hc hm
    nlinarith
  have hprinter' : GraphUnaryPrinter.totalBound (encodedCopies g c) ≤
      27 * (4 * UnaryBinaryEncoding.coefficient + 30) * (B + 1)^6 := by
    calc
      _ ≤ (4 * UnaryBinaryEncoding.coefficient + 30) * (3 * (B + 1)^2)^3 :=
        hprinter.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 3))
      _ = _ := by ring
  have hpow1 : (B + 1)^1 ≤ (B + 1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpow3 : (B + 1)^3 ≤ (B + 1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpow5 : (B + 1)^5 ≤ (B + 1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hrepeat' := hrepeat.trans (Nat.mul_le_mul_left 10 hpow3)
  have hs' := hs.trans (Nat.mul_le_mul_left 1000 hpow5)
  have hoff : 2 * g.vertices + 2 ≤ 2 * (B + 1)^6 := by
    simp only [pow_one] at hpow1
    omega
  unfold GraphRepeatPrinter.totalBound GraphShiftPrinter.totalBound
  nlinarith

def inputSize (g : EncodedGraph.Graph) (N : ℕ) : ℕ :=
  N + (EncodedGraph.encode g).length + 1

theorem copies_le_inputSize (g : EncodedGraph.Graph) (N : ℕ)
    (hm : 0 < g.edges.length) : copies N g.edges.length ≤ inputSize g N := by
  have he := EncodedGraph.encode_length_lower g
  have hd := Nat.div_le_self (N + g.edges.length - 1) g.edges.length
  unfold copies inputSize
  omega

/-- A degree-six charged transition bound for the actual canonical-input
copy printer, uniform over every N and every valid nonempty source graph. -/
theorem totalBound_polynomial (g : EncodedGraph.Graph) (hg : g.Valid) (N : ℕ)
    (hm : 0 < g.edges.length) :
    GraphCopyEncoded.totalBound g N ≤
      (200 * UnaryBinaryEncoding.coefficient + 5200) * (inputSize g N + 1)^6 := by
  let B := inputSize g N
  have he := EncodedGraph.encode_length_lower g
  have hn : g.vertices ≤ B := by dsimp [B, inputSize]; omega
  have hm' : g.edges.length ≤ B := by dsimp [B, inputSize]; omega
  have hN : N ≤ B := by dsimp [B, inputSize]; omega
  have hc : copies N g.edges.length ≤ B := copies_le_inputSize g N hm
  have hr := repeatBound_polynomial g hg (copies N g.edges.length) B hc hn hm'
  have hd := SourceNormalizationMachineDecode.graphCost_polynomial g hg
  have hlen : (EncodedGraph.encode g).length + 1 ≤ B + 1 := by dsimp [B, inputSize]; omega
  have hd' : SourceNormalizationMachineDecode.graphCost g ≤ 100 * (B + 1)^6 :=
    hd.trans ((Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hlen 3)).trans
      (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_right (by omega) (by decide))))
  have hpow : B + 1 ≤ (B + 1)^6 := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (show 0 < B + 1 by omega) (show 1 ≤ 6 by decide))
  have hcount : 10 * N + 15 * g.edges.length + 16 ≤ 41 * (B + 1)^6 := by omega
  unfold GraphCopyEncoded.totalBound GraphCopyFromUnary.totalBound
  dsimp only [B] at hr hd' hcount
  nlinarith

theorem encoded_graph_copy_polynomial_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (N : ℕ) (hm : 0 < g.edges.length) :
    ∃ t ≤ (200 * UnaryBinaryEncoding.coefficient + 5200) * (inputSize g N + 1)^6,
      GraphCopyEncoded.run t (GraphCopyEncoded.start (EncodedGraph.encode g) N) =
        GraphCopyEncoded.finalHost g N := by
  obtain ⟨t, ht, hr⟩ := GraphCopyEncoded.encoded_graph_copy_run g hg N hm
  exact ⟨t, ht.trans (totalBound_polynomial g hg N hm), hr⟩

#print axioms totalBound_polynomial
#print axioms encoded_graph_copy_polynomial_run

end Paper2.CurrentAdditive.GraphCopyResource
