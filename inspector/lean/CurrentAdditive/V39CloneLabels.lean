import CurrentAdditive.V38CloneMachine

/-!
Literal readback of the strengthened clone enumeration. Each occurrence edge
has a designated injective lift, found in the actual list by `idxOf`; original
edge occurrences remain distinct labels even if their ordered vertices agree.
No additional source promise is assumed here.
-/

namespace CurrentAdditive.V39CloneLabels

open CurrentAdditive.V38Source
open Paper2.YaoCloneSource Paper2.YaoSourceCodec

set_option maxHeartbeats 1000000

variable {K S v e : ℕ}

def directLift (hS : 0 < S) : Fin K → Fin (K * S) :=
  fun j => ⟨j.val, j.isLt.trans_le (Nat.le_mul_of_pos_right K hS)⟩

theorem directLift_injective (hS : 0 < S) :
    Function.Injective (directLift (K := K) hS) := by
  intro i j h
  have hval := congrArg (fun z : Fin (K * S) => z.val) h
  exact Fin.ext hval

theorem directLift_mem (hS : 0 < S) (edges : Fin e → Fin K → Fin v)
    (i : Fin e) :
    (i, directLift (K := K) hS) ∈ allLifts edges S := by
  apply (mem_allLifts edges i _).2
  intro j k h
  exact directLift_injective hS (congrArg Prod.snd h)

/-- A numerical index into the actual edge list, with no reordering. -/
def occurrenceIndex (hS : 0 < S) (edges : Fin e → Fin K → Fin v)
    (i : Fin e) : Fin (cloneEdgeCount edges S) :=
  ⟨(allLifts edges S).idxOf (i, directLift hS),
    List.idxOf_lt_length_of_mem (directLift_mem hS edges i)⟩

theorem occurrenceIndex_readback (hS : 0 < S)
    (edges : Fin e → Fin K → Fin v) (i : Fin e) :
    (allLifts edges S).get (occurrenceIndex hS edges i) =
      (i, directLift hS) := by
  exact List.idxOf_get _

theorem occurrenceIndex_injective (hS : 0 < S)
    (edges : Fin e → Fin K → Fin v) :
    Function.Injective (occurrenceIndex hS edges) := by
  intro i j h
  have heq := congrArg (fun k => ((allLifts edges S).get k).1) h
  simpa only [occurrenceIndex_readback] using heq

/-- Distinct occurrence labels remain distinct even when their tuples coincide. -/
def occurrenceEmbedding (hS : 0 < S)
    (edges : Fin e → Fin K → Fin v) :
    Fin e ↪ Fin (cloneEdgeCount edges S) :=
  ⟨occurrenceIndex hS edges, occurrenceIndex_injective hS edges⟩

theorem cloneEdgeCount_lower (hS : 0 < S)
    (edges : Fin e → Fin K → Fin v) :
    e ≤ cloneEdgeCount edges S := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective _ (occurrenceIndex_injective hS edges)

/-- The `j`th vertex of the designated lift is precisely clone `j` of the
`j`th original occurrence. This is an equality of the actual numeric labels. -/
theorem occurrenceEdge_numeric (hS : 0 < S)
    (edges : Fin e → Fin K → Fin v) (i : Fin e) (j : Fin K) :
    (cloneEdges edges S (occurrenceIndex hS edges i) j).val =
      (edges i j).val * (K * S) + j.val := by
  change (vertexNumber v K S
    (edges ((allLifts edges S).get (occurrenceIndex hS edges i)).1 j,
      ((allLifts edges S).get (occurrenceIndex hS edges i)).2 j)).val = _
  rw [occurrenceIndex_readback, vertexNumber_val]
  rfl

/-- Every old edge occurrence has a labelled edge in the selected source. -/
theorem selectedSource_edgeCount_lower {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) :
    (G.output input).2.1 ≤ (selectedSource G input).2.1 :=
  cloneEdgeCount_lower (by simp [colourCount]) (G.output input).2.2

theorem selectedSource_edgeCount_bounds {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) :
    (G.output input).2.1 ≤ (selectedSource G input).2.1 ∧
      (selectedSource G input).2.1 ≤ (G.output input).2.1 *
        (2 ^ t * 2 ^ t * colourCount t) ^ (2 ^ t * 2 ^ t) :=
  ⟨selectedSource_edgeCount_lower G input, (selectedSource_sizes G input).2.2⟩

#print axioms directLift_injective
#print axioms directLift_mem
#print axioms occurrenceIndex_readback
#print axioms occurrenceIndex_injective
#print axioms cloneEdgeCount_lower
#print axioms occurrenceEdge_numeric
#print axioms selectedSource_edgeCount_lower
#print axioms selectedSource_edgeCount_bounds

end CurrentAdditive.V39CloneLabels
