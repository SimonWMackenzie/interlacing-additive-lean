import EthInapproximability.CurrentPaper.MatrixWeightedCanonicalOrderRun

/-! Identification of the physical rank stream with the frozen graph ItemOrder. -/

namespace EthInapproximability.CurrentPaper.MatrixWeightedCanonicalOrderBridge

open MatrixWeightedCanonicalOrderMachine MatrixWeightedCanonicalOrderRun

theorem range_eq_ofFn (n : ℕ) :
    List.range n = List.ofFn (fun i : Fin n => i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem flatMap_eq_flatten_map {α β : Type*} (xs : List α)
    (f : α → List β) : xs.flatMap f = (xs.map f).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem vertexRanks_eq_ofFn (v a K : ℕ) :
    vertexRanks v a K =
      List.ofFn (fun i : Fin (K * v) =>
        i.val / v * (v + a) + i.val % v) := by
  rw [List.ofFn_mul]
  unfold vertexRanks
  rw [range_eq_ofFn K]
  rw [flatMap_eq_flatten_map, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext copy
  simp only [Function.comp_apply]
  rw [range_eq_ofFn v, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  have hv : 0 < v := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hq : (i.val + v * copy.val) / v = copy.val := by
    simpa [Nat.add_comm, Nat.div_eq_of_lt i.isLt] using
      (Nat.mul_add_div hv copy.val i.val)
  have hm : (i.val + v * copy.val) % v = i.val := by
    simpa [Nat.add_comm, Nat.mod_eq_of_lt i.isLt] using
      (Nat.mul_add_mod v copy.val i.val)
  change copy.val * (v + a) + i.val =
    (copy.val * v + i.val) / v * (v + a) +
      (copy.val * v + i.val) % v
  rw [Nat.mul_comm copy.val v,
    Nat.add_comm (v * copy.val) i.val, hq, hm]

theorem auxiliaryRanks_eq_ofFn (v a K : ℕ) :
    auxiliaryRanks v a K =
      List.ofFn (fun i : Fin (K * a) =>
        i.val / a * (v + a) + v + i.val % a) := by
  rw [List.ofFn_mul]
  unfold auxiliaryRanks
  rw [range_eq_ofFn K]
  rw [flatMap_eq_flatten_map, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext copy
  simp only [Function.comp_apply]
  rw [range_eq_ofFn a, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  have ha : 0 < a := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hq : (i.val + a * copy.val) / a = copy.val := by
    simpa [Nat.add_comm, Nat.div_eq_of_lt i.isLt] using
      (Nat.mul_add_div ha copy.val i.val)
  have hm : (i.val + a * copy.val) % a = i.val := by
    simpa [Nat.add_comm, Nat.mod_eq_of_lt i.isLt] using
      (Nat.mul_add_mod a copy.val i.val)
  change copy.val * (v + a) + v + i.val =
    (copy.val * a + i.val) / a * (v + a) + v +
      (copy.val * a + i.val) % a
  rw [Nat.mul_comm copy.val a,
    Nat.add_comm (a * copy.val) i.val, hq, hm]

universe u w

variable {V : Type u} {E : Type w}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem canonicalWord_itemOrder
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (s : ℕ) :
    canonicalWord (Fintype.card V) (s - 3) (4 * s) =
      MatrixWeightedRowOrderLookup.orderWord (GraphVectors.itemOrder G s) := by
  unfold MatrixWeightedRowOrderLookup.orderWord canonicalWord
  rw [List.ofFn_add]
  apply congrArg MatrixWeightedRowOrderLookup.fields
  rw [vertexRanks_eq_ofFn, auxiliaryRanks_eq_ofFn]
  congr 1
  · apply congrArg List.ofFn
    funext i
    simpa [GraphVectors.vertexCount] using
      (MatrixWeightedCanonicalOrderMachine.vertex_rank G s i).symm
  · apply congrArg List.ofFn
    funext i
    simpa [GraphVectors.auxiliaryCount] using
      (MatrixWeightedCanonicalOrderMachine.auxiliary_rank G s i).symm

/-- The canonical copy-major order table is computed from three unary count
words by one fixed finite-stack program. In particular, the order word is
not supplied to the initial bank or queried as an abstract permutation. -/
theorem graph_order_run
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (s : ℕ) :
    ∃ t ≤ totalCost (Fintype.card V) (s - 3) (4 * s),
      run t ⟨some start, none,
        initialBank (Fintype.card V) (s - 3) (4 * s)⟩ =
        ⟨none, none,
          outputBank (Fintype.card V) (s - 3) (4 * s)⟩ ∧
      outputBank (Fintype.card V) (s - 3) (4 * s) 8 =
        MatrixWeightedRowOrderLookup.orderWord (GraphVectors.itemOrder G s) := by
  obtain ⟨t, ht, hr⟩ := complete_run (Fintype.card V) (s - 3) (4 * s)
  exact ⟨t, ht, hr,
    (outputBank_table (Fintype.card V) (s - 3) (4 * s)).trans
      (canonicalWord_itemOrder G s)⟩

end EthInapproximability.CurrentPaper.MatrixWeightedCanonicalOrderBridge
