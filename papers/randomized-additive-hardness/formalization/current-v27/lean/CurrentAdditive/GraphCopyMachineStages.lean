import CurrentAdditive.GraphCopyPadding
import EthInapproximability.CurrentPaper.SourceNormalizationMachineCounts
import EthInapproximability.CurrentPaper.SourceNormalizationMachineShiftCopies
import EthInapproximability.CurrentPaper.SourceNormalizationMachineEndpointWriter

/-!
Physical machine stages for the v38 source graph-copy construction.
These are existing finite-stack programs instantiated at the *unmodified*
ordered edge-occurrence list. The stage boundaries are explicit; this file
does not claim a composed whole-input printer.
-/

namespace Paper2.CurrentAdditive.GraphCopyMachineStages

open EthInapproximability.CurrentPaper
open Paper2.CurrentAdditive.GraphCopyPadding

def endpointList (g : EncodedGraph.Graph) : List ℕ :=
  g.edges.flatMap fun p => [p.1, p.2]

theorem endpointList_ne_nil (g : EncodedGraph.Graph)
    (hm : 0 < g.edges.length) : endpointList g ≠ [] := by
  unfold endpointList
  cases he : g.edges with
  | nil => simp [he] at hm
  | cons p ps => simp [he]

/-- The existing unary division controller computes exactly the required
ceiling when fed `m-1` as its second counter. -/
theorem copies_eq_physical_count (N m : ℕ) (hm : 0 < m) :
    copies N m =
      EthInapproximability.ParameterizedNP.GuardedSourceGraph.copyCount N (m - 1) := by
  unfold copies EthInapproximability.ParameterizedNP.GuardedSourceGraph.copyCount
  have hsub : m - 1 + 1 = m := by omega
  have hsum : N + m - 1 = N + (m - 1) := by omega
  rw [hsub, hsum]

/-- Exact fixed-control division run, with the input payload retained. -/
theorem physical_count_run (N m : ℕ) (hm : 0 < m)
    (payload : List Bool) :
    ∃ t ≤ 10 * N + 13 * (m - 1) + 13,
      SourceNormalizationMachineCounts.run t
        (SourceNormalizationMachineCounts.cfg (some (.inr .copyN)) false [] [] [] [] [] []
          (List.replicate N true) (List.replicate (m - 1) true) payload) =
      SourceNormalizationMachineCounts.cfg none false [] (List.replicate m true) []
        (List.replicate ((N + (m - 1)) % m) true)
        (List.replicate (copies N m) true) []
        (List.replicate N true) (List.replicate (m - 1) true) payload := by
  obtain ⟨t, ht, hr⟩ := SourceNormalizationMachineCounts.count_run N (m - 1) payload
  refine ⟨t, ht, ?_⟩
  have hs : m - 1 + 1 = m := by omega
  rw [hs, ← copies_eq_physical_count N m hm] at hr
  exact hr

theorem unaryEdges_eq_endpointList (g : EncodedGraph.Graph) :
    SourceNormalizationMachineEndpointWriter.unaryEdges g.edges =
      SourceNormalizationMachineMark.endpointStream (endpointList g) := by
  exact SourceNormalizationMachineEndpointWriter.unaryEdges_eq_endpointStream g.edges

private theorem endpointStream_append (xs ys : List ℕ) :
    SourceNormalizationMachineMark.endpointStream (xs ++ ys) =
      SourceNormalizationMachineMark.endpointStream xs ++
        SourceNormalizationMachineMark.endpointStream ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [SourceNormalizationMachineMark.endpointStream, ih,
        List.append_assoc]

private theorem endpointStream_flatMap {α : Type*} (xs : List α)
    (f : α → List ℕ) :
    SourceNormalizationMachineMark.endpointStream (xs.flatMap f) =
      xs.flatMap (fun x => SourceNormalizationMachineMark.endpointStream (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [endpointStream_append, ih]

private theorem endpointList_copies (g : EncodedGraph.Graph) (c : ℕ) :
    endpointList (encodedCopies g c) =
      (List.range c).flatMap (fun j =>
        (endpointList g).map (fun x => j * g.vertices + x)) := by
  unfold endpointList encodedCopies
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro j hj
  simp [List.flatMap_map, List.map_flatMap, Function.comp_def]

/-- The shift controller's concrete output stream is precisely the endpoint
stream for the ordered labelled copies, including parallel occurrences. -/
theorem shifted_eq_copied_unary (g : EncodedGraph.Graph) (c : ℕ) :
    SourceNormalizationMachineShiftCopies.shiftedFrom (endpointList g) g.vertices 0 c =
      SourceNormalizationMachineEndpointWriter.unaryEdges (encodedCopies g c).edges := by
  rw [SourceNormalizationMachineShiftCopies.shiftedFrom_eq_copy_major,
    SourceNormalizationMachineEndpointWriter.unaryEdges_eq_endpointStream]
  change (List.range c).flatMap (fun k =>
      SourceNormalizationMachineShiftCopies.shifted (endpointList g)
        (0 + k * g.vertices)) =
    SourceNormalizationMachineMark.endpointStream
      (endpointList (encodedCopies g c))
  rw [endpointList_copies, endpointStream_flatMap]
  simp only [Nat.zero_add, SourceNormalizationMachineShiftCopies.shifted]
  apply List.flatMap_congr
  intro j hj
  congr 1
  apply List.map_congr_left
  intro x hx
  omega

/-- A literal nine-stack run copies and shifts the endpoint fields. It has a
charged transition count and retains the unary vertex-width vector. -/
theorem physical_shift_run (g : EncodedGraph.Graph)
    (hm : 0 < g.edges.length) (c : ℕ) (hc : 0 < c) :
    ∃ t ≤ SourceNormalizationMachineShiftCopies.copiesCost (endpointList g)
          (List.replicate g.vertices true) 0 c +
        (SourceNormalizationMachineEndpointWriter.unaryEdges (encodedCopies g c).edges).length + 2,
      SourceNormalizationMachineShiftCopies.run t
        (SourceNormalizationMachineShiftCopies.cfg (some .peek) (false, none)
          (SourceNormalizationMachineShiftCopies.copyInput (endpointList g) c) [] [] [] []
          (List.replicate (endpointList g).length true) []
          (List.replicate g.vertices true) []) =
      SourceNormalizationMachineShiftCopies.cfg none (false, none) []
        (List.replicate ((c - 1) * g.vertices) true) [] []
        (SourceNormalizationMachineEndpointWriter.unaryEdges (encodedCopies g c).edges)
        [] (List.replicate (endpointList g).length true)
        (List.replicate g.vertices true) [] := by
  obtain ⟨t, ht, hr⟩ := SourceNormalizationMachineShiftCopies.copies_run (endpointList g)
    (endpointList_ne_nil g hm) (List.replicate g.vertices true)
    c 0 hc []
  simp only [List.count_replicate_self, Nat.zero_add, List.append_nil] at ht hr
  rw [shifted_eq_copied_unary] at ht hr
  exact ⟨t, ht, hr⟩

/-- A separate fixed-control unary-to-binary field writer prints precisely
the target edge fields and the target number of edge-count tokens. -/
theorem physical_edge_fields_run (g : EncodedGraph.Graph) (c : ℕ) :
    ∃ t ≤ SourceNormalizationMachineEndpointWriter.edgesCost (encodedCopies g c).edges + 1,
      SourceNormalizationMachineEndpointWriter.run t
        (SourceNormalizationMachineEndpointWriter.start (SourceNormalizationMachineEndpointWriter.unaryEdges (encodedCopies g c).edges)) =
      SourceNormalizationMachineEndpointWriter.cfg none (none, (SourceNormalizationMachineEndpointWriter.counter.initial, none))
        (SourceNormalizationMachineEndpointWriter.idleBank []) []
        (EncodedGraph.edgeFields (encodedCopies g c).edges).reverse
        (List.replicate (encodedCopies g c).edges.length true) [] := by
  exact SourceNormalizationMachineEndpointWriter.writer_run (encodedCopies g c).edges

#print axioms copies_eq_physical_count
#print axioms physical_count_run
#print axioms shifted_eq_copied_unary
#print axioms physical_shift_run
#print axioms physical_edge_fields_run

end Paper2.CurrentAdditive.GraphCopyMachineStages
