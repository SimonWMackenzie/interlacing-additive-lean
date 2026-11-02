import CurrentAdditive.SequentialArrayBridge

/-!
Totality obligations for sequential support compression, using the proved
typed Gauss--Jordan finder while preserving the labelled array source.
-/

namespace CurrentAdditive.SequentialCompressionTotality

open SequentialCode SequentialArrayBridge

private theorem foldl_max_const (rows : List (Array ℚ)) (K : Nat)
    (hrows : ∀ row ∈ rows, row.size = K) :
    rows.foldl (fun n row => max n row.size) K = K := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      have hrow : row.size = K := hrows row (by simp)
      have hrest : ∀ x ∈ rest, x.size = K := by
        intro x hx
        exact hrows x (by simp [hx])
      simpa [List.foldl_cons, hrow] using ih hrest

private theorem columnCount_rectangular (a : Array (Array ℚ)) (K : Nat)
    (hne : 0 < a.size)
    (hrows : ∀ row ∈ a.toList, row.size = K) :
    columnCount a = K := by
  have hlist : a.toList ≠ [] := by
    intro hnil
    have hempty : a = #[] := Array.toList_eq_nil_iff.mp hnil
    subst a
    simp at hne
  obtain ⟨row, rest, heq⟩ := List.exists_cons_of_ne_nil hlist
  have hrow : row.size = K := hrows row (by simp [heq])
  have hrest : ∀ x ∈ rest, x.size = K := by
    intro x hx
    exact hrows x (by simp [heq, hx])
  unfold columnCount
  rw [← Array.foldl_toList, heq]
  simpa [hrow] using foldl_max_const rest K hrest

theorem featureRows_columnCount {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (source : Array (α × ℚ)) (hn : 0 < n) :
    columnCount (featureRows n φ source) = source.size := by
  apply columnCount_rectangular _ source.size
  · simpa [featureRows] using hn
  · intro row hrow
    simp [featureRows] at hrow
    obtain ⟨j, hj⟩ := hrow
    subst row
    simp

/-- Every overfull labelled source has an executable exact dependence
certificate for its finite feature rows. -/
theorem featureRows_certified_dependence {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (source : Array (α × ℚ))
    (hn : 0 < n) (hover : n < source.size) :
    ∃ cert,
      certifiedTypedDependence (featureRows n φ source) = some cert := by
  apply certifiedTypedDependence_total
  rw [featureRows_columnCount n φ source hn]
  simpa [featureRows] using hover

#print axioms featureRows_columnCount
#print axioms featureRows_certified_dependence

end CurrentAdditive.SequentialCompressionTotality
