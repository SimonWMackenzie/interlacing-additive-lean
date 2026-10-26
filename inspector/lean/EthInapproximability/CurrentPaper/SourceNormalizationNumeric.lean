import EthInapproximability.CurrentPaper.SourceNormalizationMachineMark
import EthInapproximability.CurrentPaper.SourceNormalizationMachineRanks
import EthInapproximability.CurrentPaper.EncodedETHSource

/-!
# Ordered numeric normalization of a finite graph

The original vertex count and edge-occurrence order are retained.  This
module defines the numeric target of the physical normalization machine;
the source theorem's abstract ordered graph is a separate object until an
explicit serialization equality is proved.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationNumeric

open SourceNormalizationMachineMark

def endpoints (g : EncodedGraph.Graph) : List ℕ :=
  g.edges.flatMap fun p => [p.1, p.2]

def support (g : EncodedGraph.Graph) : List Bool :=
  (List.range g.vertices).map fun v => decide (v ∈ endpoints g)

def rank (g : EncodedGraph.Graph) (v : ℕ) : ℕ :=
  ((support g).take v).count true

@[simp] theorem rank_eq_machine_rankAt (g : EncodedGraph.Graph) (v : ℕ) :
    rank g v = SourceNormalizationMachineRanks.rankAt (support g) v := rfl

def paddedEdges (g : EncodedGraph.Graph) : List (ℕ × ℕ) :=
  g.edges.map (fun p => (rank g p.1, rank g p.2)) ++
    [((support g).count true, (support g).count true + 1)]

def paddedSupport (g : EncodedGraph.Graph) : List Bool :=
  support g ++ [true, true]

def paddedEndpoints (g : EncodedGraph.Graph) : List ℕ :=
  endpoints g ++ [g.vertices, g.vertices + 1]

def repetitions (g : EncodedGraph.Graph) (originalN : ℕ) : ℕ :=
  EthInapproximability.ParameterizedNP.GuardedSourceGraph.copyCount
    originalN g.edges.length

def numericGraph (g : EncodedGraph.Graph) (originalN : ℕ) : EncodedGraph.Graph :=
  let width := (support g).count true + 2
  let copies := repetitions g originalN
  ⟨copies * width,
    (List.range copies).flatMap fun k =>
      (paddedEdges g).map fun p => (k * width + p.1, k * width + p.2)⟩

@[simp] theorem support_length (g : EncodedGraph.Graph) :
    (support g).length = g.vertices := by simp [support]

@[simp] theorem endpoints_length (g : EncodedGraph.Graph) :
    (endpoints g).length = 2 * g.edges.length := by
  simp [endpoints, Nat.mul_comm]

private theorem sum_le_length_mul (xs : List ℕ) (N : ℕ)
    (h : ∀ x ∈ xs, x ≤ N) : xs.sum ≤ xs.length * N := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs : ∀ y ∈ xs, y ≤ N := by
        intro y hy
        exact h y (List.mem_cons_of_mem x hy)
      have hi := ih hxs
      simp only [List.sum_cons, List.length_cons]
      nlinarith

@[simp] theorem paddedEdges_length (g : EncodedGraph.Graph) :
    (paddedEdges g).length = g.edges.length + 1 := by
  simp [paddedEdges]

@[simp] theorem paddedSupport_length (g : EncodedGraph.Graph) :
    (paddedSupport g).length = g.vertices + 2 := by
  simp [paddedSupport]

theorem padded_rank_old (g : EncodedGraph.Graph) (v : ℕ) (hv : v ≤ g.vertices) :
    SourceNormalizationMachineRanks.rankAt (paddedSupport g) v = rank g v := by
  simp [SourceNormalizationMachineRanks.rankAt, rank, paddedSupport,
    List.take_append_of_le_length, support_length, hv]

@[simp] theorem padded_rank_new0 (g : EncodedGraph.Graph) :
    SourceNormalizationMachineRanks.rankAt (paddedSupport g) g.vertices =
      (support g).count true := by
  rw [padded_rank_old g g.vertices le_rfl, rank]
  simp [List.take_of_length_le, support_length]

@[simp] theorem padded_rank_new1 (g : EncodedGraph.Graph) :
    SourceNormalizationMachineRanks.rankAt (paddedSupport g) (g.vertices + 1) =
      (support g).count true + 1 := by
  simp [SourceNormalizationMachineRanks.rankAt, paddedSupport, support_length,
    List.take_append, List.take_of_length_le]

@[simp] theorem numericGraph_vertices (g : EncodedGraph.Graph) (originalN : ℕ) :
    (numericGraph g originalN).vertices =
      repetitions g originalN * ((support g).count true + 2) := rfl

@[simp] theorem numericGraph_edges_length (g : EncodedGraph.Graph) (originalN : ℕ) :
    (numericGraph g originalN).edges.length =
      repetitions g originalN * (g.edges.length + 1) := by
  simp [numericGraph, repetitions]

theorem endpoints_bounded (g : EncodedGraph.Graph) (hg : g.Valid) :
    ∀ u ∈ endpoints g, u < g.vertices := by
  intro u hu
  simp only [endpoints, List.mem_flatMap] at hu
  obtain ⟨p, hp, hu⟩ := hu
  have h := hg p hp
  simp at hu
  rcases hu with rfl | rfl
  · exact h.1
  · exact h.2.1

theorem endpoints_sum_bound (g : EncodedGraph.Graph) (hg : g.Valid) :
    (endpoints g).sum ≤ 2 * g.edges.length * g.vertices := by
  rw [← endpoints_length]
  exact sum_le_length_mul (endpoints g) g.vertices
    (fun x hx => Nat.le_of_lt (endpoints_bounded g hg x hx))

theorem mark_cost_bound (g : EncodedGraph.Graph) (hg : g.Valid) :
    5 * (endpoints g).sum + 5 * (endpoints g).length + 1 ≤
      10 * g.edges.length * (g.vertices + 1) + 1 := by
  have hs := endpoints_sum_bound g hg
  rw [endpoints_length]
  nlinarith

theorem paddedEndpoints_bounded (g : EncodedGraph.Graph) (hg : g.Valid) :
    ∀ u ∈ paddedEndpoints g, u < (paddedSupport g).length := by
  intro u hu
  simp [paddedEndpoints] at hu
  rcases hu with hu | hu
  · have h := endpoints_bounded g hg u hu
    rw [paddedSupport_length]
    omega
  · rcases hu with rfl | rfl <;> simp [paddedSupport_length]

theorem padded_ranked_endpoints (g : EncodedGraph.Graph) (hg : g.Valid) :
    (paddedEndpoints g).map
      (SourceNormalizationMachineRanks.rankAt (paddedSupport g)) =
    (paddedEdges g).flatMap (fun p => [p.1, p.2]) := by
  have h : (endpoints g).map
      (SourceNormalizationMachineRanks.rankAt (paddedSupport g)) =
      (endpoints g).map (rank g) := by
    apply List.map_congr_left
    intro u hu
    exact padded_rank_old g u (Nat.le_of_lt (endpoints_bounded g hg u hu))
  simp only [paddedEndpoints, List.map_append, h, paddedEdges,
    List.flatMap_append, List.flatMap_map]
  simp [endpoints, List.map_flatMap, padded_rank_new0, padded_rank_new1]

theorem rankedStream_padded (g : EncodedGraph.Graph) (hg : g.Valid) (offset : ℕ) :
    SourceNormalizationMachineRanks.rankedStream
      (paddedSupport g) offset (paddedEndpoints g) =
    SourceNormalizationMachineMark.endpointStream
      (((paddedEdges g).flatMap (fun p => [p.1, p.2])).map (· + offset)) := by
  unfold SourceNormalizationMachineRanks.rankedStream
  congr 1
  calc
    (paddedEndpoints g).map
        (fun u => SourceNormalizationMachineRanks.rankAt (paddedSupport g) u + offset) =
      ((paddedEndpoints g).map
        (SourceNormalizationMachineRanks.rankAt (paddedSupport g))).map (· + offset) := by
          simp only [List.map_map, Function.comp_def]
    _ = ((paddedEdges g).flatMap (fun p => [p.1, p.2])).map (· + offset) := by
      rw [padded_ranked_endpoints g hg]

theorem markIndices_length (bits : List Bool) (indices : List ℕ) :
    (markIndices bits indices).length = bits.length := by
  induction indices generalizing bits with
  | nil => rfl
  | cons u us ih => simpa only [markIndices, ih, List.length_set]

theorem markIndices_getElem (bits : List Bool) (indices : List ℕ)
    (i : ℕ) (hi : i < bits.length) :
    (markIndices bits indices)[i]'(by rw [markIndices_length]; exact hi) =
      (bits[i] || decide (i ∈ indices)) := by
  induction indices generalizing bits with
  | nil => simp [markIndices]
  | cons u us ih =>
      have hi' : i < (bits.set u true).length := by simpa using hi
      change (markIndices (bits.set u true) us)[i]'(by
        rw [markIndices_length]; exact hi') = _
      rw [ih (bits.set u true) hi']
      by_cases h : i = u
      · subst i
        simp [List.getElem_set_self]
      · have hneq : u ≠ i := Ne.symm h
        rw [List.getElem_set_of_ne hneq]
        simp [h]

theorem markIndices_false_eq_support (g : EncodedGraph.Graph) :
    markIndices (List.replicate g.vertices false) (endpoints g) = support g := by
  apply List.ext_getElem
  · simp [markIndices_length, support_length]
  · intro i hi₁ hi₂
    have hi : i < g.vertices := by simpa [support_length] using hi₂
    rw [markIndices_getElem _ _ i (by simpa using hi)]
    simp [support]

theorem decoded_endpoint_stream (g : EncodedGraph.Graph) :
    SourceNormalizationMachineMark.endpointStream (endpoints g) =
      (g.edges.flatMap (fun p => [p.1, p.2])).flatMap EncodedGraph.unary := by
  have h (xs : List ℕ) : SourceNormalizationMachineMark.endpointStream xs =
      xs.flatMap EncodedGraph.unary := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa [SourceNormalizationMachineMark.endpointStream, ih]
  exact h (endpoints g)

example : numericGraph ⟨0, []⟩ 0 = ⟨2, [(0, 1)]⟩ := by decide

example : numericGraph ⟨4, [(1, 2), (1, 2)]⟩ 5 =
    ⟨8, [(0, 1), (0, 1), (2, 3), (4, 5), (4, 5), (6, 7)]⟩ := by decide

end EthInapproximability.CurrentPaper.SourceNormalizationNumeric
