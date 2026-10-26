import EthInapproximability.CurrentPaper.ExactParameters
import EthInapproximability.CurrentPaper.MatrixMaterialization
import EthInapproximability.CurrentPaper.EncodedCommunication
import EthInapproximability.CurrentPaper.EncodedGraph
import Mathlib.Data.Nat.Size

/-!
# The exact graph reduction into literal encoded communication instances

Source: frozen v8 `03-exact-hardness.tex`, explicit truth-table reduction.
The table is produced from the existing Boolean stored-family materializer,
including its actual sampler labels and five-copy source vectors. It is not
an unrelated enumeration of an abstract communication matrix.

This file proves finite semantics and output bit length. It does not yet
assert that the noncomputable finite-field realization is polynomial-time.
-/

namespace EthInapproximability.CurrentPaper.ExactEncodedReduction

open ExactParameters ExactConstruction MatrixMaterialization
open Workspace.Types.CommComplexity

noncomputable def firstFamily (s : ℕ) (hs : 2 ^ 21 ≤ s) :=
  ExactSamplerInstances.firstFamilyFor (actualParameters s hs) (actual_r_pos s hs) rfl

noncomputable def secondFamily (s : ℕ) (hs : 2 ^ 21 ≤ s) :=
  ExactSamplerInstances.secondFamilyFor (actualParameters s hs) (actual_r_pos s hs) rfl

/-- The three literal Boolean payloads retain all repeated sampled labels. -/
noncomputable def payload (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) : ExactBitData :=
  storeBits (firstFamily s hs) (secondFamily s hs) (sourceVectors (dimension s) e)

def rowCount (s n : ℕ) := 4 * secondListSize s + 5 * n
def columnCount (s : ℕ) := 8 * (dimension s * firstListSize s) ^ 4

/-- The existing materializer runs on those payloads with the same numeric
row and column codecs as its correctness theorem. -/
noncomputable def literalTable (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) : List Bool :=
  bitTable (d := dimension s) (N₁ := firstListSize s) (N₂ := secondListSize s)
    (n := 5 * n) (payload s hs e) (actualParameters s hs).ha

theorem literalTable_length (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) :
    (literalTable s hs e).length = rowCount s n * columnCount s := by
  unfold literalTable bitTable
  exact table_length _ _

theorem literalTable_cost (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) :
    D (ProtocolVerifier.tableGame (rowCount s n) (columnCount s) (literalTable s hs e)) =
      D (actualMatrix s hs e) :=
  D_bitTable_storeBits (actualParameters s hs).ha (firstFamily s hs)
    (secondFamily s hs) (sourceVectors (dimension s) e) (sourceVectors_cap (dimension s) e)

theorem counts_pos (s : ℕ) (hs : 2 ^ 21 ≤ s) (n : ℕ) :
    0 < rowCount s n ∧ 0 < columnCount s := by
  have hb := actual_size_bounds (s := s) (by omega)
  have hd : 0 < dimension s := by unfold dimension; positivity
  have hfirst : 0 < firstListSize s := (pow_pos hd 64).trans_le hb.1.1
  have hsecond : 0 < secondListSize s := (pow_pos hd 6).trans_le hb.2.1
  constructor <;> simp only [rowCount, columnCount] <;> positivity

noncomputable def instanceAt (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) : EncodedCommunication.Instance :=
  ⟨rowCount s n, columnCount s, firstExponent s + 1 + dimensionLog s + 2,
    literalTable s hs e⟩

theorem instanceAt_valid (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) : (instanceAt s hs e).Valid :=
  ⟨(counts_pos s hs n).1, (counts_pos s hs n).2, literalTable_length s hs e⟩

noncomputable def instanceFor {n d : ℕ} (e : Fin d → Fin 2 → Fin n) :
    EncodedCommunication.Instance :=
  instanceAt (ExactSourcePadding.paddedExponent d) (ExactSourcePadding.cutoff d) e

theorem instanceFor_valid {n d : ℕ} (e : Fin d → Fin 2 → Fin n) :
    (instanceFor e).Valid :=
  instanceAt_valid (ExactSourcePadding.paddedExponent d) (ExactSourcePadding.cutoff d) e

noncomputable def output {n d : ℕ} (e : Fin d → Fin 2 → Fin n) : List Bool :=
  EncodedCommunication.encodeInstance (instanceFor e)

theorem output_decodes {n d : ℕ} (e : Fin d → Fin 2 → Fin n) :
    EncodedCommunication.decodeInstance (output e) = some (instanceFor e) :=
  EncodedCommunication.decode_encode _ (instanceFor_valid e)

theorem encode_mem_iff (i : EncodedCommunication.Instance) (hi : i.Valid) :
    EncodedCommunication.encodeInstance i ∈ EncodedCommunication.Language ↔
      D (ProtocolVerifier.tableGame i.rows i.cols i.table) ≤ i.threshold := by
  change (∃ j, EncodedCommunication.decodeInstance (EncodedCommunication.encodeInstance i) =
    some j ∧ D (ProtocolVerifier.tableGame j.rows j.cols j.table) ≤ j.threshold) ↔ _
  rw [EncodedCommunication.decode_encode i hi]
  simp only [Option.some.injEq]
  constructor
  · rintro ⟨j, rfl, hj⟩
    exact hj
  · intro hc
    exact ⟨i, rfl, hc⟩

theorem encodeAt_mem_iff (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) (hD : 5 * d ≤ dimension s)
    (hinj : ∀ α, Function.Injective (e α)) :
    EncodedCommunication.encodeInstance (instanceAt s hs e) ∈ EncodedCommunication.Language ↔
      ∃ colour : Fin n → Fin 4, ∀ α : Fin d, colour (e α 0) ≠ colour (e α 1) := by
  rw [encode_mem_iff _ (instanceAt_valid s hs e)]
  change D (ProtocolVerifier.tableGame (rowCount s n) (columnCount s) (literalTable s hs e)) ≤
    firstExponent s + 1 + dimensionLog s + 2 ↔ _
  rw [literalTable_cost]
  exact actual_decision_equivalence s hs e hD hinj

/-- Exact semantics in the concrete communication language, not merely a
relabelled abstract family of Boolean functions. -/
theorem output_mem_iff {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (hinj : ∀ α, Function.Injective (e α)) :
    output e ∈ EncodedCommunication.Language ↔
      ∃ colour : Fin n → Fin 4, ∀ α : Fin d, colour (e α 0) ≠ colour (e α 1) :=
  encodeAt_mem_iff (ExactSourcePadding.paddedExponent d) (ExactSourcePadding.cutoff d)
    e (ExactSourcePadding.coverage d) hinj

/-- A simple linear upper bound suffices for the self-delimiting binary
headers; it avoids relying on unit-cost arithmetic for those fields. -/
theorem natField_length_le (n : ℕ) : (EncodedCommunication.natField n).length ≤ 2 * n + 1 := by
  rw [EncodedCommunication.natField, EncodedCommunication.field_length, Nat.size_eq_bits_len]
  have h := Nat.size_le.mpr (Nat.lt_two_pow_self : n < 2 ^ n)
  omega

theorem encode_length_le (i : EncodedCommunication.Instance) :
    (EncodedCommunication.encodeInstance i).length ≤
      i.table.length + 2 * i.rows + 2 * i.cols + 2 * i.threshold + 3 := by
  have hr := natField_length_le i.rows
  have hc := natField_length_le i.cols
  have ht := natField_length_le i.threshold
  simp only [EncodedCommunication.encodeInstance, List.length_append]
  omega

theorem threshold_le_columns (s : ℕ) (hs : 2 ^ 21 ≤ s) :
    firstExponent s + 1 + dimensionLog s + 2 ≤ columnCount s := by
  have hn := naming_exponent_bound (s := s) (by omega)
  have hr := linear_lt_power (s := s) (by omega)
  have hrd : dimensionLog s ≤ dimension s := Nat.le_of_lt Nat.lt_two_pow_self
  have hd : 0 < dimension s := by unfold dimension; positivity
  have hb := (actual_size_bounds (s := s) (by omega)).1.1
  have hfirst : 1 ≤ firstListSize s := (pow_pos hd 64).trans_le hb
  have hbase : dimension s ≤ dimension s * firstListSize s := by nlinarith
  have hp : dimension s * firstListSize s ≤ (dimension s * firstListSize s) ^ 4 := by
    convert Nat.pow_le_pow_right (by omega : 1 ≤ dimension s * firstListSize s)
      (by omega : 1 ≤ 4) using 1
    simp
  unfold columnCount
  omega

theorem output_length_le_table {n d : ℕ} (e : Fin d → Fin 2 → Fin n) :
    (output e).length ≤ 7 * (instanceFor e).table.length + 3 := by
  have hb := encode_length_le (instanceFor e)
  have hv := instanceFor_valid e
  have hr : (instanceFor e).rows ≤ (instanceFor e).table.length := by
    rw [hv.2.2]
    nlinarith [hv.2.1]
  have hc : (instanceFor e).cols ≤ (instanceFor e).table.length := by
    rw [hv.2.2]
    nlinarith [hv.1]
  have ht : (instanceFor e).threshold ≤ (instanceFor e).cols :=
    threshold_le_columns _ (ExactSourcePadding.cutoff d)
  change (EncodedCommunication.encodeInstance (instanceFor e)).length ≤ _
  omega

theorem instance_table_size {n d : ℕ} (e : Fin d → Fin 2 → Fin n) :
    let B := ExactSourcePadding.paddingConstant * (2 * max 1 (5 * d)) ^ 2
    (instanceFor e).table.length ≤ 8 * (4 * B ^ 100 + 5 * n) * B ^ 1204 := by
  have hsize := source_matrix_size n d
  simpa only [instanceFor, instanceAt, literalTable_length, rowCount, columnCount,
    card_rows, card_columns] using hsize

/-- A single fixed polynomial in any bound on the source's vertex and edge
counts. The coefficient is huge but independent of the input. -/
def outputLengthBound (L : ℕ) : ℕ :=
  let B := ExactSourcePadding.paddingConstant * (10 * L + 2) ^ 2
  56 * (4 * B ^ 100 + 5 * L) * B ^ 1204 + 3

theorem output_length_polynomial {n d L : ℕ} (e : Fin d → Fin 2 → Fin n)
    (hn : n ≤ L) (hd : d ≤ L) : (output e).length ≤ outputLengthBound L := by
  have ht := instance_table_size e
  have he := output_length_le_table e
  have hB : ExactSourcePadding.paddingConstant * (2 * max 1 (5 * d)) ^ 2 ≤
      ExactSourcePadding.paddingConstant * (10 * L + 2) ^ 2 := by
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : 2 * max 1 (5 * d) ≤
      10 * L + 2) 2)
  have htable : (instanceFor e).table.length ≤
      8 * (4 * (ExactSourcePadding.paddingConstant * (10 * L + 2) ^ 2) ^ 100 + 5 * L) *
        (ExactSourcePadding.paddingConstant * (10 * L + 2) ^ 2) ^ 1204 := by
    apply ht.trans
    dsimp only
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 8
      (Nat.add_le_add (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hB 100))
        (Nat.mul_le_mul_left 5 hn))) (Nat.pow_le_pow_left hB 1204)
  unfold outputLengthBound
  apply he.trans
  have hmul := Nat.add_le_add_right (Nat.mul_le_mul_left 7 htable) 3
  simpa only [← Nat.mul_assoc, Nat.reduceMul] using hmul

/-- A total mapping on Boolean strings. Rejected source encodings map to the
empty string, which the target parser also rejects. -/
noncomputable def reduction (input : List Bool) : List Bool :=
  match h : EncodedGraph.decode input with
  | none => []
  | some g => output (EncodedGraph.endpoints g (EncodedGraph.decode_valid h))

theorem reduction_of_decoded {input : List Bool} {g : EncodedGraph.Graph}
    (h : EncodedGraph.decode input = some g) :
    reduction input = output (EncodedGraph.endpoints g (EncodedGraph.decode_valid h)) := by
  unfold reduction
  split
  · rename_i hn
    rw [h] at hn
    contradiction
  · rename_i g' hg'
    have he : g' = g := Option.some.inj (hg'.symm.trans h)
    subst g'
    rfl

theorem reduction_of_malformed {input : List Bool} (h : EncodedGraph.decode input = none) :
    reduction input = [] := by
  unfold reduction
  split
  · rfl
  · rename_i g hg
    rw [h] at hg
    contradiction

theorem empty_not_target : [] ∉ EncodedCommunication.Language := by
  simp [EncodedCommunication.Language, EncodedCommunication.decodeInstance,
    EncodedCommunication.readNat, EncodedCommunication.readField]

/-- Exact source-to-target language equivalence for every Boolean input,
including malformed source strings. No source-hardness premise is used. -/
theorem reduction_correct (input : List Bool) :
    reduction input ∈ EncodedCommunication.Language ↔ input ∈ EncodedGraph.Language := by
  cases h : EncodedGraph.decode input with
  | none =>
      rw [reduction_of_malformed h]
      exact iff_of_false empty_not_target (EncodedGraph.malformed_not_mem h)
  | some g =>
      rw [reduction_of_decoded h, EncodedGraph.language_iff_decoded h]
      exact output_mem_iff (EncodedGraph.endpoints g (EncodedGraph.decode_valid h))
        (EncodedGraph.endpoints_injective g (EncodedGraph.decode_valid h))

/-- Polynomial **output length** in the actual source bitstring length.
The execution-time theorem is intentionally separate. -/
theorem reduction_length (input : List Bool) :
    (reduction input).length ≤ outputLengthBound input.length := by
  cases h : EncodedGraph.decode input with
  | none =>
      rw [reduction_of_malformed h]
      exact Nat.zero_le _
  | some g =>
      rw [reduction_of_decoded h]
      exact output_length_polynomial _ (EncodedGraph.decoded_vertices_bound h)
        (EncodedGraph.decoded_edges_bound h)

end EthInapproximability.CurrentPaper.ExactEncodedReduction
