import Paper2.ProtectedMassPartition

namespace Paper2.OwnerTransferReindex

open scoped BigOperators

/-- Convert the physical receiver sum to the owner subtype, then exchange
donor and receiver. The omitted diagonal is the same physical owner. -/
theorem owner_receipts_reindex {V : Type*} [DecidableEq V]
    (O : Finset V) (f : O → V → ℝ) :
    (∑ u : O, ∑ v ∈ O.erase u.val, f u v) =
      ∑ v : O, ∑ u ∈ Finset.univ.erase v, f u v.val := by
  classical
  have hinner (u : O) :
      (∑ v ∈ O.erase u.val, f u v) =
        (∑ v : O, if v = u then 0 else f u v.val) := by
    rw [Finset.sum_erase_eq_sub u.property]
    rw [← Finset.sum_coe_sort O (f u)]
    have hsub := Finset.sum_erase_eq_sub (s := Finset.univ)
      (f := fun v : O => f u v.val) (Finset.mem_univ u)
    rw [← hsub]
    simp only [Finset.sum_ite, Finset.filter_eq', Finset.mem_univ, if_true,
      Finset.sum_const_zero, zero_add]
    congr 1
    ext v
    simp [and_comm]
  simp_rw [hinner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ v)]
  have hsub := Finset.sum_erase_eq_sub (s := Finset.univ)
    (f := fun u : O => f u v.val) (Finset.mem_univ v)
  rw [← hsub]
  simp only [Finset.sum_ite, Finset.filter_eq', Finset.mem_univ, if_true,
    Finset.sum_const_zero, zero_add]
  congr 1
  ext u
  simp [eq_comm, and_comm]

end Paper2.OwnerTransferReindex

#print axioms Paper2.OwnerTransferReindex.owner_receipts_reindex
