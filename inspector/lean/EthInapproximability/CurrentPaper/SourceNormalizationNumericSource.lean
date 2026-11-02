import EthInapproximability.CurrentPaper.SourceNormalizationOrderRank
import EthInapproximability.CurrentPaper.SourceNormalizationNumeric

/-! Exact ordered serialization of the abstract source normalization. -/

namespace EthInapproximability.CurrentPaper.SourceNormalizationNumericSource

open SourceNormalizationOrderRank SourceNormalizationNumeric
open EthInapproximability.ParameterizedNP.GuardedSourceGraph

universe u w

variable {V : Type u} {E : Type w}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

private def copyIndex (r m : ℕ) (i : Fin r) (j : Fin m) : Fin (r * m) :=
  ⟨i.val * m + j.val, by
    have h₁ : i.val * m + j.val < (i.val + 1) * m := by
      nlinarith [j.isLt]
    have h₂ : (i.val + 1) * m ≤ r * m :=
      Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr i.isLt)
    omega⟩

theorem copied_pair_values (G : EndpointGraph V E) (r : ℕ) (hr : 0 < r)
    (i : Fin r) (j : Fin (Fintype.card E)) :
    let k : Fin (Fintype.card (Fin r × E)) :=
      Fin.cast (by simp : r * Fintype.card E = Fintype.card (Fin r × E))
        (copyIndex r (Fintype.card E) i j)
    let p := SourceNormalization.endpointPair (G.copies r hr) k
    (p.1.val, p.2.val) =
      (i.val * Fintype.card V + (SourceNormalization.endpointPair G j).1.val,
       i.val * Fintype.card V + (SourceNormalization.endpointPair G j).2.val) := by
  dsimp only
  have he : SourceNormalization.edgeEnumeration (G.copies r hr)
      (Fin.cast (by simp : r * Fintype.card E = Fintype.card (Fin r × E))
        (copyIndex r (Fintype.card E) i j)) =
      (i, SourceNormalization.edgeEnumeration G j) := by
    simpa only [copyIndex, Fin.cast_mk] using
      (copied_edge_enumeration G r hr i j)
  apply Prod.ext
  · simp only [SourceNormalization.endpointPair]
    rw [he]
    simpa [EndpointGraph.copies, SourceNormalization.vertexEnumeration] using
      (copied_vertex_label G r hr i (G.bd₀ (SourceNormalization.edgeEnumeration G j)))
  · simp only [SourceNormalization.endpointPair]
    rw [he]
    simpa [EndpointGraph.copies, SourceNormalization.vertexEnumeration] using
      (copied_vertex_label G r hr i (G.bd₁ (SourceNormalization.edgeEnumeration G j)))

private theorem range_eq_ofFn (r : ℕ) :
    List.range r = List.ofFn (fun i : Fin r => i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

private theorem flatMap_eq_flatten_map {α β : Type*} (xs : List α)
    (f : α → List β) : xs.flatMap f = (xs.map f).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem endpointList_copies (G : EndpointGraph V E) (r : ℕ) (hr : 0 < r) :
    SourceNormalization.endpointList (G.copies r hr) =
      (List.range r).flatMap fun k =>
        (SourceNormalization.endpointList G).map fun p =>
          (k * Fintype.card V + p.1, k * Fintype.card V + p.2) := by
  unfold SourceNormalization.endpointList
  have hc : Fintype.card (Fin r × E) = r * Fintype.card E := by simp
  rw [List.ofFn_congr hc, List.ofFn_mul]
  rw [range_eq_ofFn, flatMap_eq_flatten_map, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply]
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  simpa only [copyIndex, Fin.cast_mk, Fin.cast_cast] using
    copied_pair_values G r hr i j

theorem raw_edge_order (g : EncodedGraph.Graph) (hg : g.Valid)
    (j : Fin (Fintype.card (Fin g.edges.length))) :
    (letI := (EncodedETHSource.rawGraph g hg).orderE;
      (Fintype.orderIsoFinOfCardEq (Fin g.edges.length) rfl).toEquiv j) =
      Fin.cast (Fintype.card_fin _) j := by
  simpa [EncodedETHSource.rawGraph] using (fin_order_enum_eq_cast j)

theorem raw_edge_at (g : EncodedGraph.Graph) (hg : g.Valid)
    (j : Fin g.edges.length) :
    (letI := (EncodedETHSource.rawGraph g hg).orderE;
      (Fintype.orderIsoFinOfCardEq (Fin g.edges.length) rfl).toEquiv
        (Fin.cast (Fintype.card_fin _).symm j)) = j := by
  simpa only [raw_edge_order, Fin.cast_cast, Fin.cast_refl, id_eq]

theorem padded_old_pair_labels (G : SourceNormalization.RawGraph V E)
    (j : Fin (Fintype.card E)) :
    let p := SourceNormalization.endpointPair G.padded
      ⟨j.val, by simp only [SourceNormalization.RawGraph.padded_edge_count]; omega⟩
    (p.1.val, p.2.val) =
      ((letI := G.orderV;
        ((Fintype.orderIsoFinOfCardEq G.Support rfl).symm
          (G.endpoint₀ (letI := G.orderE;
            (Fintype.orderIsoFinOfCardEq E rfl).toEquiv j))).val),
       (letI := G.orderV;
        ((Fintype.orderIsoFinOfCardEq G.Support rfl).symm
          (G.endpoint₁ (letI := G.orderE;
            (Fintype.orderIsoFinOfCardEq E rfl).toEquiv j))).val)) := by
  dsimp only
  apply Prod.ext
  · simp only [SourceNormalization.endpointPair]
    rw [padded_edge_enumeration_old G j]
    simpa only [SourceNormalization.RawGraph.padded, SourceNormalization.vertexEnumeration]
      using (padded_endpoint_zero_label G
        (letI := G.orderE; (Fintype.orderIsoFinOfCardEq E rfl).toEquiv j))
  · simp only [SourceNormalization.endpointPair]
    rw [padded_edge_enumeration_old G j]
    simpa only [SourceNormalization.RawGraph.padded, SourceNormalization.vertexEnumeration]
      using (padded_endpoint_one_label G
        (letI := G.orderE; (Fintype.orderIsoFinOfCardEq E rfl).toEquiv j))

theorem padded_new_pair_labels (G : SourceNormalization.RawGraph V E) :
    let p := SourceNormalization.endpointPair G.padded
      ⟨Fintype.card E, by simp only [SourceNormalization.RawGraph.padded_edge_count]; omega⟩
    (p.1.val, p.2.val) =
      (Fintype.card G.Support, Fintype.card G.Support + 1) := by
  dsimp only
  apply Prod.ext
  · simp only [SourceNormalization.endpointPair]
    rw [padded_edge_enumeration_new G]
    simpa only [SourceNormalization.RawGraph.padded, SourceNormalization.vertexEnumeration]
      using (padded_vertex_label_new G (0 : Fin 2))
  · simp only [SourceNormalization.endpointPair]
    rw [padded_edge_enumeration_new G]
    simpa only [SourceNormalization.RawGraph.padded, SourceNormalization.vertexEnumeration]
      using (padded_vertex_label_new G (1 : Fin 2))

private def supportLabel (G : SourceNormalization.RawGraph V E)
    (v : G.Support) : ℕ :=
  letI := G.orderV
  (Finset.univ.filter (fun w : G.Support => w < v)).card

private theorem supportLabel_eq_inverse (G : SourceNormalization.RawGraph V E)
    (v : G.Support) :
    supportLabel G v =
      (letI := G.orderV;
        ((Fintype.orderIsoFinOfCardEq G.Support rfl).symm v).val) := by
  letI := G.orderV
  exact (inverse_enum_eq_card_below v).symm

private def orderedEdge (G : SourceNormalization.RawGraph V E)
    (j : Fin (Fintype.card E)) : E :=
  letI := G.orderE
  (Fintype.orderIsoFinOfCardEq E rfl).toEquiv j

theorem endpointList_padded (G : SourceNormalization.RawGraph V E) :
    SourceNormalization.endpointList G.padded =
      List.ofFn (fun j : Fin (Fintype.card E) =>
        (supportLabel G (G.endpoint₀ (orderedEdge G j)),
         supportLabel G (G.endpoint₁ (orderedEdge G j)))) ++
      [(Fintype.card G.Support, Fintype.card G.Support + 1)] := by
  unfold SourceNormalization.endpointList
  have hc : Fintype.card G.PaddedEdge = Fintype.card E + 1 :=
    SourceNormalization.RawGraph.padded_edge_count G
  rw [List.ofFn_congr hc, List.ofFn_succ']
  simp only [List.concat_eq_append]
  congr 1
  · apply congrArg List.ofFn
    funext j
    simp only [supportLabel_eq_inverse]
    simpa only [Fin.castSucc, Fin.cast_mk, orderedEdge] using
      (padded_old_pair_labels G j)
  · simp only [Fin.last, Fin.cast_mk]
    exact congrArg (fun p : ℕ × ℕ => [p]) (padded_new_pair_labels G)

theorem supportLabel_raw (g : EncodedGraph.Graph) (hg : g.Valid)
    (v : (EncodedETHSource.rawGraph g hg).Support) :
    supportLabel (EncodedETHSource.rawGraph g hg) v = rank g v.val.val := by
  have h := support_label_eq_rank g hg v.val v.property
  have heq : (⟨v.val, v.property⟩ : (EncodedETHSource.rawGraph g hg).Support) = v :=
    Subtype.eta v v.property
  rw [heq] at h
  unfold supportLabel
  rw [inverse_enum_eq_card_below] at h
  refine Eq.trans ?_ h
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change x.val.val < v.val.val ↔ x.val.val < v.val.val
  rfl

theorem orderedEdge_raw (g : EncodedGraph.Graph) (hg : g.Valid)
    (j : Fin (Fintype.card (Fin g.edges.length))) :
    orderedEdge (EncodedETHSource.rawGraph g hg) j =
      Fin.cast (Fintype.card_fin _) j := by
  exact raw_edge_order g hg j

theorem raw_padded_old_pair_numeric (g : EncodedGraph.Graph) (hg : g.Valid)
    (j : Fin (Fintype.card (Fin g.edges.length))) :
    let G := EncodedETHSource.rawGraph g hg
    (supportLabel G (G.endpoint₀ (orderedEdge G j)),
     supportLabel G (G.endpoint₁ (orderedEdge G j))) =
      (rank g (g.edges.get (Fin.cast (Fintype.card_fin _) j)).1,
       rank g (g.edges.get (Fin.cast (Fintype.card_fin _) j)).2) := by
  dsimp only
  rw [orderedEdge_raw, supportLabel_raw, supportLabel_raw]
  simp [SourceNormalization.RawGraph.endpoint₀,
    SourceNormalization.RawGraph.endpoint₁, EncodedETHSource.rawGraph,
    EncodedGraph.endpoints_zero, EncodedGraph.endpoints_one]

private def paddedNumericEdges (G : SourceNormalization.RawGraph V E) :
    List (ℕ × ℕ) :=
  List.ofFn (fun j : Fin (Fintype.card E) =>
    (supportLabel G (G.endpoint₀ (orderedEdge G j)),
     supportLabel G (G.endpoint₁ (orderedEdge G j)))) ++
  [(Fintype.card G.Support, Fintype.card G.Support + 1)]

theorem endpointList_normalize (G : SourceNormalization.RawGraph V E)
    (n : ℕ) :
    SourceNormalization.endpointList (G.normalize n) =
      (List.range (G.repetitions n)).flatMap fun k =>
        (paddedNumericEdges G).map fun p =>
          (k * (Fintype.card G.Support + 2) + p.1,
           k * (Fintype.card G.Support + 2) + p.2) := by
  change SourceNormalization.endpointList
    (G.padded.copies (G.repetitions n) (copyCount_pos n (Fintype.card E))) = _
  rw [endpointList_copies, endpointList_padded]
  simp only [paddedNumericEdges, SourceNormalization.RawGraph.padded_vertex_count]

theorem paddedNumericEdges_raw (g : EncodedGraph.Graph) (hg : g.Valid) :
    paddedNumericEdges (EncodedETHSource.rawGraph g hg) = paddedEdges g := by
  let G := EncodedETHSource.rawGraph g hg
  unfold paddedNumericEdges paddedEdges
  have hold :
      List.ofFn (fun j : Fin (Fintype.card (Fin g.edges.length)) =>
        (supportLabel G (G.endpoint₀ (orderedEdge G j)),
         supportLabel G (G.endpoint₁ (orderedEdge G j)))) =
      g.edges.map (fun p => (rank g p.1, rank g p.2)) := by
    have hc : Fintype.card (Fin g.edges.length) = g.edges.length :=
      Fintype.card_fin _
    rw [List.ofFn_congr hc]
    calc
      List.ofFn (fun j : Fin g.edges.length =>
        (supportLabel G (G.endpoint₀ (orderedEdge G (Fin.cast hc.symm j))),
         supportLabel G (G.endpoint₁ (orderedEdge G (Fin.cast hc.symm j))))) =
          List.ofFn (fun j : Fin g.edges.length =>
            (rank g (g.edges.get j).1, rank g (g.edges.get j).2)) := by
              apply congrArg List.ofFn
              funext j
              simpa only [Fin.cast_cast, Fin.cast_refl] using
                (raw_padded_old_pair_numeric g hg (Fin.cast hc.symm j))
      _ = g.edges.map (fun p => (rank g p.1, rank g p.2)) := by
            conv_rhs => rw [← List.ofFn_get g.edges]
            rw [List.map_ofFn]
            apply congrArg List.ofFn
            funext j
            rfl
  have hcard : Fintype.card G.Support = (support g).count true := by
    have h := support_card_eq_numeric g hg
    rw [Fintype.card_subtype] at h ⊢
    refine Eq.trans ?_ h
    apply congrArg Finset.card
    ext x
    rfl
  rw [hold]
  apply congrArg (fun tail : List (ℕ × ℕ) =>
    g.edges.map (fun p => (rank g p.1, rank g p.2)) ++ tail)
  apply congrArg (fun p : ℕ × ℕ => [p])
  apply Prod.ext
  all_goals simp only [Prod.fst, Prod.snd]
  · rw [Fintype.card_subtype]
    have h := support_card_eq_numeric g hg
    rw [Fintype.card_subtype] at h
    refine Eq.trans ?_ h
    apply congrArg Finset.card
    ext x
    rfl
  · congr 1
    rw [Fintype.card_subtype]
    have h := support_card_eq_numeric g hg
    rw [Fintype.card_subtype] at h
    refine Eq.trans ?_ h
    apply congrArg Finset.card
    ext x
    rfl

def serializeNormalized (G : SourceNormalization.RawGraph V E) (n : ℕ) :
    EncodedGraph.Graph :=
  EncodedETHSource.serializeGraph (G.normalize n)

theorem serializeNormalized_generic (G : SourceNormalization.RawGraph V E)
    (n : ℕ) :
    serializeNormalized G n =
      ⟨G.repetitions n * (Fintype.card G.Support + 2),
        (List.range (G.repetitions n)).flatMap fun k =>
          (paddedNumericEdges G).map fun p =>
            (k * (Fintype.card G.Support + 2) + p.1,
             k * (Fintype.card G.Support + 2) + p.2)⟩ := by
  unfold serializeNormalized EncodedETHSource.serializeGraph
  apply congrArg₂ EncodedGraph.Graph.mk
  · simp [SourceNormalization.RawGraph.normalize,
      SourceNormalization.RawGraph.PaddedVertex]
  · exact endpointList_normalize G n

/-- The ordered abstract source graph has exactly the numeric vertices and
edge occurrences produced by the finite-stack normalization target. -/
theorem serializeNormalized_raw (g : EncodedGraph.Graph) (hg : g.Valid)
    (n : ℕ) :
    serializeNormalized (EncodedETHSource.rawGraph g hg) n =
      numericGraph g n := by
  rw [serializeNormalized_generic, paddedNumericEdges_raw]
  unfold numericGraph
  simp only [SourceNormalization.RawGraph.repetitions, repetitions,
    Fintype.card_fin]
  have hc : Nat.card (EncodedETHSource.rawGraph g hg).Support =
      (support g).count true := by
    simpa only [Fintype.card_eq_nat_card] using
      (support_card_eq_numeric g hg)
  simpa only [Fintype.card_eq_nat_card, hc]

end EthInapproximability.CurrentPaper.SourceNormalizationNumericSource
