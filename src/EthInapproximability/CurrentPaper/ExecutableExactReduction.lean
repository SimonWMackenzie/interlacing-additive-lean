import EthInapproximability.CurrentPaper.ExactEncodedReduction
import EthInapproximability.CurrentPaper.ExecutableSmallBiasSampler

/-!
# Executable realization of the exact encoded graph reduction

Source: v8 `03-exact-hardness.tex` and `E-exact-details.tex`.
The two sampler maps now execute the canonical binary-polynomial search and
list-backed finite-field arithmetic. Their proved balancedness instantiates
the same exact finite gadget theorem; no communication conclusion or sampler
oracle is supplied. The output uses the existing Boolean payload materializer.

Every definition of the reduction is executable Lean code. This is not yet
a fixed Boolean-stack program or its polynomial running-time proof.
-/

namespace EthInapproximability.CurrentPaper.ExecutableExactReduction

open ExactParameters ExactConstruction MatrixMaterialization
open Workspace.Types.CommComplexity
open ExactEncodedReduction (rowCount columnCount outputLengthBound)

def firstFamily (s : ℕ) : FirstFamily (firstExponent s) (firstListSize s) :=
  ExecutableSmallBiasSampler.exactFirstFamily (firstExponent s) (firstOrder s) (dimension s)

def secondFamily (s : ℕ) : SecondFamily (firstExponent s) (dimension s) (secondListSize s) :=
  ExecutableSmallBiasSampler.exactSecondFamily (firstExponent s) (secondOrder s) (dimension s)

theorem firstFamily_balanced (s : ℕ) :
    NPCC.IsBalancedFamily (firstOrder s) (firstFamily s) (errorDensity s) :=
  ExecutableSmallBiasSampler.exactFirstFamily_balanced _ _ _
    (ExactSamplerInstances.two_le_width (Nat.one_le_pow _ _ (by omega)))

theorem secondFamily_balanced (s : ℕ) :
    NPCC.IsBalancedFamily (secondOrder s) (secondFamily s) (errorDensity s) :=
  ExecutableSmallBiasSampler.exactSecondFamily_balanced _ _ _
    (by unfold firstExponent; omega)
    (ExactSamplerInstances.two_le_width (Nat.one_le_pow _ _ (by omega)))

theorem alphabet_valid (s : ℕ) (hs : 2 ^ 21 ≤ s) : 2 ≤ firstExponent s := by
  unfold firstExponent
  omega

def matrixAt (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ} (e : Fin d → Fin 2 → Fin n) :
    Rows (secondListSize s) (5 * n) → Columns (dimension s) (firstListSize s) → Bool :=
  matrix (alphabet_valid s hs) (firstFamily s) (secondFamily s)
    (sourceVectors (dimension s) e) (sourceVectors_cap (dimension s) e)

theorem matrix_decision_equivalence (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) (hD : 5 * d ≤ dimension s)
    (hinj : ∀ α, Function.Injective (e α)) :
    D (matrixAt s hs e) ≤ firstExponent s + 1 + dimensionLog s + 2 ↔
      ∃ colour : Fin n → Fin 4, ∀ α : Fin d, colour (e α 0) ≠ colour (e α 1) :=
  ExactFiniteReduction.decision_equivalence (actualParameters s hs)
    (firstFamily s) (secondFamily s) (firstFamily_balanced s) (secondFamily_balanced s)
    e hD hinj

theorem matrix_finite_gap (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) (hD : 5 * d ≤ dimension s)
    (hinj : ∀ α, Function.Injective (e α)) :
    (∀ colour : Fin n → Fin 4, (∀ α : Fin d, colour (e α 0) ≠ colour (e α 1)) →
      D (matrixAt s hs e) = firstExponent s + 1 + dimensionLog s + 2) ∧
    ((∀ colour : Fin n → Fin 4, ∃ α : Fin d, colour (e α 0) = colour (e α 1)) →
      D (matrixAt s hs e) = firstExponent s + 1 + dimensionLog s + 3) :=
  ExactFiniteReduction.finite_gap (actualParameters s hs)
    (firstFamily s) (secondFamily s) (firstFamily_balanced s) (secondFamily_balanced s)
    e hD hinj

/-- Direct finite-gap instantiation also proves exact cost agreement with
the earlier abstract-field presentation, without asserting equal table bits. -/
theorem matrix_cost_eq_abstract (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) (hD : 5 * d ≤ dimension s)
    (hinj : ∀ α, Function.Injective (e α)) :
    D (matrixAt s hs e) = D (ExactParameters.actualMatrix s hs e) := by
  classical
  obtain ⟨hnewYes, hnewNo⟩ := matrix_finite_gap s hs e hD hinj
  obtain ⟨holdYes, holdNo⟩ := ExactParameters.actual_finite_gap s hs e hD hinj
  by_cases h : ∃ colour : Fin n → Fin 4, ∀ α : Fin d, colour (e α 0) ≠ colour (e α 1)
  · obtain ⟨colour, hc⟩ := h
    rw [hnewYes colour hc, holdYes colour hc]
  · push Not at h
    rw [hnewNo h, holdNo h]

/-- Stored Boolean payloads, produced by the executable coefficient samplers. -/
def payload (s : ℕ) {n d : ℕ} (e : Fin d → Fin 2 → Fin n) : ExactBitData :=
  storeBits (firstFamily s) (secondFamily s) (sourceVectors (dimension s) e)

def literalTable (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) : List Bool :=
  bitTable (d := dimension s) (N₁ := firstListSize s) (N₂ := secondListSize s)
    (n := 5 * n) (payload s e) (alphabet_valid s hs)

theorem literalTable_length (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) :
    (literalTable s hs e).length = rowCount s n * columnCount s := by
  unfold literalTable bitTable
  exact table_length _ _

theorem literalTable_cost (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) :
    D (ProtocolVerifier.tableGame (rowCount s n) (columnCount s) (literalTable s hs e)) =
      D (matrixAt s hs e) :=
  D_bitTable_storeBits (alphabet_valid s hs) (firstFamily s) (secondFamily s)
    (sourceVectors (dimension s) e) (sourceVectors_cap (dimension s) e)

def instanceAt (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) : EncodedCommunication.Instance :=
  ⟨rowCount s n, columnCount s, firstExponent s + 1 + dimensionLog s + 2,
    literalTable s hs e⟩

theorem instanceAt_valid (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) : (instanceAt s hs e).Valid :=
  ⟨(ExactEncodedReduction.counts_pos s hs n).1,
    (ExactEncodedReduction.counts_pos s hs n).2, literalTable_length s hs e⟩

theorem encodeAt_mem_iff (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) (hD : 5 * d ≤ dimension s)
    (hinj : ∀ α, Function.Injective (e α)) :
    EncodedCommunication.encodeInstance (instanceAt s hs e) ∈ EncodedCommunication.Language ↔
      ∃ colour : Fin n → Fin 4, ∀ α : Fin d, colour (e α 0) ≠ colour (e α 1) := by
  rw [ExactEncodedReduction.encode_mem_iff _ (instanceAt_valid s hs e)]
  change D (ProtocolVerifier.tableGame (rowCount s n) (columnCount s) (literalTable s hs e)) ≤
    firstExponent s + 1 + dimensionLog s + 2 ↔ _
  rw [literalTable_cost]
  exact matrix_decision_equivalence s hs e hD hinj

def instanceFor {n d : ℕ} (e : Fin d → Fin 2 → Fin n) : EncodedCommunication.Instance :=
  instanceAt (ExactSourcePadding.paddedExponent d) (ExactSourcePadding.cutoff d) e

def output {n d : ℕ} (e : Fin d → Fin 2 → Fin n) : List Bool :=
  EncodedCommunication.encodeInstance (instanceFor e)

theorem output_decodes {n d : ℕ} (e : Fin d → Fin 2 → Fin n) :
    EncodedCommunication.decodeInstance (output e) = some (instanceFor e) :=
  EncodedCommunication.decode_encode _
    (instanceAt_valid _ (ExactSourcePadding.cutoff d) e)

theorem output_mem_iff {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (hinj : ∀ α, Function.Injective (e α)) :
    output e ∈ EncodedCommunication.Language ↔
      ∃ colour : Fin n → Fin 4, ∀ α : Fin d, colour (e α 0) ≠ colour (e α 1) :=
  encodeAt_mem_iff _ (ExactSourcePadding.cutoff d) e (ExactSourcePadding.coverage d) hinj

/-- Only the seed presentation changes. Table/header lengths are unchanged,
even though the individual output bits need not be identical in that order. -/
theorem encodeAt_length_eq (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) :
    (EncodedCommunication.encodeInstance (instanceAt s hs e)).length =
      (EncodedCommunication.encodeInstance (ExactEncodedReduction.instanceAt s hs e)).length := by
  simp only [EncodedCommunication.encodeInstance, instanceAt, ExactEncodedReduction.instanceAt,
    List.length_append, literalTable_length, ExactEncodedReduction.literalTable_length]

theorem output_length_eq {n d : ℕ} (e : Fin d → Fin 2 → Fin n) :
    (output e).length = (ExactEncodedReduction.output e).length :=
  encodeAt_length_eq _ (ExactSourcePadding.cutoff d) e

theorem output_length_polynomial {n d L : ℕ} (e : Fin d → Fin 2 → Fin n)
    (hn : n ≤ L) (hd : d ≤ L) : (output e).length ≤ outputLengthBound L := by
  rw [output_length_eq]
  exact ExactEncodedReduction.output_length_polynomial e hn hd

def reduction (input : List Bool) : List Bool :=
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

/-- Correctness of the concrete executable Boolean-list algorithm. -/
theorem reduction_correct (input : List Bool) :
    reduction input ∈ EncodedCommunication.Language ↔ input ∈ EncodedGraph.Language := by
  cases h : EncodedGraph.decode input with
  | none =>
      rw [reduction_of_malformed h]
      exact iff_of_false ExactEncodedReduction.empty_not_target (EncodedGraph.malformed_not_mem h)
  | some g =>
      rw [reduction_of_decoded h, EncodedGraph.language_iff_decoded h]
      exact output_mem_iff (EncodedGraph.endpoints g (EncodedGraph.decode_valid h))
        (EncodedGraph.endpoints_injective g (EncodedGraph.decode_valid h))

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

/-- The executable and abstract presentations decide exactly the same
target instances on all source inputs, including rejected strings. -/
theorem reduction_target_equivalence (input : List Bool) :
    reduction input ∈ EncodedCommunication.Language ↔
      ExactEncodedReduction.reduction input ∈ EncodedCommunication.Language :=
  (reduction_correct input).trans (ExactEncodedReduction.reduction_correct input).symm

theorem malformed_regression : reduction [] = [] := by decide

end EthInapproximability.CurrentPaper.ExecutableExactReduction
