import EthInapproximability.CurrentPaper.MatrixWeightedOrderPreparation
import EthInapproximability.CurrentPaper.MatrixWeightedEntryController

/-!
# Canonical order production for the weighted entry bank

For the graph-specific `ItemOrder`, the fixed order-preparation machine
fills global slot 60 with its exact serialized word and clears its own
scratch.  All other already-supplied weighted metadata remains unchanged.
The input count words are literal unary words in the preparation seed;
production of those words and of the raw table is not part of this theorem.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedOrderToEntry

open MatrixWeightedOrderPreparation MatrixWeightedEntryController

theorem persistent_scratch_empty (d : Input) (i : Fin 8) :
    persistentBank d (scratchSlots i) = [] := by
  fin_cases i <;> rfl

theorem graph_ready_bank {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (s : ℕ) (d : Input)
    (horder : d.orderBits =
      MatrixWeightedRowOrderLookup.orderWord (GraphVectors.itemOrder G s)) :
    readyBank (persistentBank d) (Fintype.card V) (s - 3) (4 * s) =
      persistentBank d := by
  apply readyBank_eq_base
  · calc
      persistentBank d 60 = d.orderBits := rfl
      _ = MatrixWeightedRowOrderLookup.orderWord
            (GraphVectors.itemOrder G s) := horder
      _ = MatrixWeightedCanonicalOrderMachine.canonicalWord
            (Fintype.card V) (s - 3) (4 * s) :=
          (MatrixWeightedCanonicalOrderBridge.canonicalWord_itemOrder G s).symm
  · exact persistent_scratch_empty d

theorem graph_order_into_entry {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (s : ℕ) (d : Input)
    (horder : d.orderBits =
      MatrixWeightedRowOrderLookup.orderWord (GraphVectors.itemOrder G s)) :
    ∃ t ≤ prepCost (Fintype.card V) (s - 3) (4 * s),
      run t (cfg (some start) initial
        (sourceBank (persistentBank d)
          (Fintype.card V) (s - 3) (4 * s))) =
        cfg none initial (persistentBank d) := by
  obtain ⟨t, ht, he⟩ := canonical_order_polynomial_run (persistentBank d)
    (Fintype.card V) (s - 3) (4 * s)
  exact ⟨t, ht, he.trans (by rw [graph_ready_bank G s d horder])⟩

end EthInapproximability.CurrentPaper.MatrixWeightedOrderToEntry
