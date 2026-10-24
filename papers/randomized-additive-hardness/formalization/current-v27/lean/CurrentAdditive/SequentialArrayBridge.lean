import CurrentAdditive.SequentialTotality

/-!
Connect the proved typed Gauss--Jordan dependence finder to the indexed
array representation used by the sequential cylinder constructor. This is
new work; the previously reviewed source files remain byte-identical.
-/

namespace CurrentAdditive.SequentialArrayBridge

open SequentialCode SequentialTotality

def matrixOfArray (a : Array (Array ℚ)) :
    Fin a.size → Fin (columnCount a) → ℚ :=
  fun i j => cell a i.val j.val

def typedArrayDependence (a : Array (Array ℚ)) : Option (Array ℚ) :=
  (typedDependence (matrixOfArray a)).map Array.ofFn

private theorem listRangeSum (n : Nat) (f : Nat → ℚ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem typedArrayDependence_total (a : Array (Array ℚ))
    (h : a.size < columnCount a) :
    ∃ x, typedArrayDependence a = some x ∧
      x.size = columnCount a ∧
      (∃ j ∈ List.range x.size, x[j]?.getD 0 ≠ 0) ∧
      ∀ i ∈ List.range a.size,
        ((List.range x.size).map
          (fun j => cell a i j * (x[j]?.getD 0))).sum = 0 := by
  obtain ⟨v, hv, hvnonzero, hvkernel⟩ :=
    typedDependence_total (matrixOfArray a) h
  refine ⟨Array.ofFn v, ?_, ?_, ?_, ?_⟩
  · simp [typedArrayDependence, hv]
  · simp
  · obtain ⟨j, hj⟩ := hvnonzero
    refine ⟨j.val, ?_, ?_⟩
    · simpa using (List.mem_range.mpr j.isLt)
    simpa using hj
  · intro i hi
    let fi : Fin a.size := ⟨i, List.mem_range.mp hi⟩
    have hz := hvkernel fi
    simp only [Array.size_ofFn] at *
    change ((List.range (columnCount a)).map
      (fun j => cell a i j * ((Array.ofFn v)[j]?.getD 0))).sum = 0
    rw [listRangeSum]
    unfold rowDot matrixOfArray at hz
    rw [Finset.sum_fin_eq_sum_range] at hz
    dsimp [fi] at hz
    calc
      (∑ j ∈ Finset.range (columnCount a),
          cell a i j * ((Array.ofFn v)[j]?.getD 0)) =
          ∑ j ∈ Finset.range (columnCount a),
            (if h : j < columnCount a then cell a i j * v ⟨j, h⟩ else 0) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjk := Finset.mem_range.mp hj
              simp [hjk]
      _ = 0 := hz

theorem typedArrayDependence_check (a : Array (Array ℚ))
    (h : a.size < columnCount a) :
    ∃ x, typedArrayDependence a = some x ∧
      dependenceCheck a x = true := by
  obtain ⟨x, hx, hs, hn, hrows⟩ := typedArrayDependence_total a h
  exact ⟨x, hx, (dependence_spec a x).2 ⟨hs, hn, hrows⟩⟩

/-- The deterministic typed finder, packaged with the exact array checker.
Unlike the frozen candidate's optional checker, this option is proved to
succeed on every overfull array matrix. -/
def certifiedTypedDependence (a : Array (Array ℚ)) :
    Option {x : Array ℚ // IsDependence a x} :=
  match typedArrayDependence a with
  | none => none
  | some x =>
      if h : dependenceCheck a x = true then some ⟨x, h⟩ else none

theorem certifiedTypedDependence_total (a : Array (Array ℚ))
    (h : a.size < columnCount a) :
    ∃ cert, certifiedTypedDependence a = some cert := by
  obtain ⟨x, hx, hcheck⟩ := typedArrayDependence_check a h
  refine ⟨⟨x, hcheck⟩, ?_⟩
  simp [certifiedTypedDependence, hx, hcheck]

#print axioms typedArrayDependence_total
#print axioms typedArrayDependence_check
#print axioms certifiedTypedDependence_total

end CurrentAdditive.SequentialArrayBridge
