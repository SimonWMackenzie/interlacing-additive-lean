import EthInapproximability.CurrentPaper.GraphVectors
import EthInapproximability.CurrentPaper.EncodedETHSource
import EthInapproximability.CurrentPaper.SourceGraphPayloadMachine

/-!
# Segment 2 specification: every bit of `GraphVectors.vectors G s` from the
# serialized graph and index arithmetic

Lane owner:b-stage4-entry-program-2, segment 2 (first piece; NOT a machine).

`vectors_formula` rewrites each bit of the actual copy-major vectors table as
index arithmetic on the unary words `|V|`, `s - 3`, `|E|` plus ONE admitted
endpoint query `SourceGraphPayloadMachine.endpointHit` on the literal edge
list of `EncodedETHSource.serializeGraph G` (the bytes the level retains).
This is the per-cell specification a physical `EntryRuns` cell program must
meet; no machine is claimed here.
-/

namespace EthInapproximability.CurrentPaper.EntryVectorsFormula

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The arithmetic cell rule. `nV = |V|`, `B = s - 3`, `m = |E|`. -/
def cellRule (edges : List (ℕ × ℕ)) (s nV B m x y : ℕ) : Bool :=
  decide (y < 4 * s * m) && decide (y / m = x / (nV + B)) &&
    (if x % (nV + B) < nV then SourceGraphPayloadMachine.endpointHit edges (y % m) (x % (nV + B))
      else true)

theorem serialized_edge_get (G : EndpointGraph V E) (k : Fin (Fintype.card E)) :
    (EncodedETHSource.serializeGraph G).edges[k.val]? =
      some (((GraphVectors.vertexEnum G).symm (G.bd₀ (GraphVectors.edgeEnum G k))).val,
        ((GraphVectors.vertexEnum G).symm (G.bd₁ (GraphVectors.edgeEnum G k))).val) := by
  simp [EncodedETHSource.serializeGraph, SourceNormalization.endpointList,
    SourceNormalization.endpointPair, SourceNormalization.vertexEnumeration,
    SourceNormalization.edgeEnumeration, GraphVectors.vertexEnum, GraphVectors.edgeEnum]

theorem hit_vertex (G : EndpointGraph V E) (v : V) (e : E) :
    SourceGraphPayloadMachine.endpointHit (EncodedETHSource.serializeGraph G).edges
        ((GraphVectors.edgeEnum G).symm e).val ((GraphVectors.vertexEnum G).symm v).val =
      decide (v = G.bd₀ e ∨ v = G.bd₁ e) := by
  unfold SourceGraphPayloadMachine.endpointHit
  rw [serialized_edge_get G ((GraphVectors.edgeEnum G).symm e)]
  simp only [Equiv.apply_symm_apply]
  have h (u : V) : ((GraphVectors.vertexEnum G).symm v).val =
      ((GraphVectors.vertexEnum G).symm u).val ↔ v = u := by
    constructor
    · intro hv
      exact (GraphVectors.vertexEnum G).symm.injective (Fin.ext hv)
    · rintro rfl; rfl
  simp only [h]

theorem vectors_formula (G : EndpointGraph V E) (s : ℕ)
    (i : Fin (GraphVectors.vertexCount V s + GraphVectors.auxiliaryCount s))
    (α : Fin (q2 G s)) :
    GraphVectors.vectors G s i α =
      cellRule (EncodedETHSource.serializeGraph G).edges s (Fintype.card V) (s - 3)
        (Fintype.card E) i.val α.val := by
  set nV := Fintype.card V
  set m := Fintype.card E
  obtain ⟨⟨r, a⟩, rfl⟩ := (GraphVectors.itemIndex G s).surjective i
  rw [GraphVectors.vectors_itemIndex]
  unfold cellRule
  by_cases hα : α.val < 4 * s * m
  · obtain ⟨⟨r', e⟩, rfl⟩ := (GraphVectors.coordinate_exists_iff G s α).2 hα
    have hcv := GraphVectors.coordinate_val G s r' e
    have hek := ((GraphVectors.edgeEnum G).symm e).isLt
    have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hek
    have hdiv : (GraphVectors.coordinate G s (r', e)).val / m = r'.val := by
      rw [hcv, Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hek, zero_add]
    have hmod : (GraphVectors.coordinate G s (r', e)).val % m =
        ((GraphVectors.edgeEnum G).symm e).val := by
      rw [hcv, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hek]
    rw [decide_eq_true hα, Bool.true_and, hdiv, hmod]
    rcases a with v | b
    · have hiv := GraphVectors.itemIndex_vertex_val G s r v
      have hvk := ((GraphVectors.vertexEnum G).symm v).isLt
      have hpos : 0 < nV + (s - 3) := by omega
      have hq : (GraphVectors.itemIndex G s (r, Sum.inl v)).val / (nV + (s - 3)) = r.val := by
        rw [hiv, Nat.add_comm, Nat.add_mul_div_right _ _ hpos,
          Nat.div_eq_of_lt (by omega), zero_add]
      have hr : (GraphVectors.itemIndex G s (r, Sum.inl v)).val % (nV + (s - 3)) =
          ((GraphVectors.vertexEnum G).symm v).val := by
        rw [hiv, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      rw [hq, hr, if_pos hvk, hit_vertex]
      by_cases hrr : r = r'
      · subst hrr
        have := (GraphVectors.vector_vertex G s r r v e)
        cases hb : GraphVectors.vector G s (r, Sum.inl v) (GraphVectors.coordinate G s (r, e))
        · have hn : ¬ (v = G.bd₀ e ∨ v = G.bd₁ e) := by
            intro hh; rw [(this.2 ⟨rfl, hh⟩)] at hb; cases hb
          simp [hn]
        · have hh := (this.1 hb).2
          simp [hh]
      · have hne : r.val ≠ r'.val := fun h => hrr (Fin.ext h)
        rw [GraphVectors.vector_cross_copy G s r r' hrr]
        simp [Ne.symm hne]
    · have hib := GraphVectors.itemIndex_auxiliary_val G s r b
      have hbk := b.isLt
      have hpos : 0 < nV + (s - 3) := by omega
      have hq : (GraphVectors.itemIndex G s (r, Sum.inr b)).val / (nV + (s - 3)) = r.val := by
        rw [hib, Nat.add_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ hpos,
          Nat.div_eq_of_lt (by omega), zero_add]
      have hr : (GraphVectors.itemIndex G s (r, Sum.inr b)).val % (nV + (s - 3)) =
          nV + b.val := by
        rw [hib, Nat.add_assoc, Nat.add_comm, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (by omega)]
      rw [hq, hr, if_neg (by omega), Bool.and_true]
      by_cases hrr : r = r'
      · subst hrr
        have := GraphVectors.vector_auxiliary G s r r b e
        have ht : GraphVectors.vector G s (r, Sum.inr b) (GraphVectors.coordinate G s (r, e)) =
            true := this.2 rfl
        rw [ht]
        simp
      · have hne : r.val ≠ r'.val := fun h => hrr (Fin.ext h)
        rw [GraphVectors.vector_cross_copy G s r r' hrr]
        simp [Ne.symm hne]
  · rw [GraphVectors.vector_padding_of_rank G s _ α (Nat.le_of_not_lt hα), decide_eq_false hα,
      Bool.false_and, Bool.false_and]

#print axioms serialized_edge_get
#print axioms hit_vertex
#print axioms vectors_formula

end EthInapproximability.CurrentPaper.EntryVectorsFormula
