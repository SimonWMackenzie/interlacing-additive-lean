import CurrentAdditive.SequentialCompressionTotality

/-!
An explicitly materialized Gauss--Jordan implementation. Every pivot step
stores the complete rational matrix in nested arrays before the next step.
This prevents repeated evaluation of nested function-valued row updates.
The algebraic result is proved equal to `echelonTyped`; a bit-machine cost
theorem is still a separate obligation.
-/

namespace CurrentAdditive.MaterializedGauss

open SequentialTotality SequentialCode SequentialArrayBridge

def packed {m k : Nat} (A : Fin m → Fin k → ℚ) : Array (Array ℚ) :=
  Array.ofFn (fun i => Array.ofFn (fun j => A i j))

/-- Reify a typed matrix through an eager nested array. -/
def materialize {m k : Nat} (A : Fin m → Fin k → ℚ) :
    Fin m → Fin k → ℚ :=
  let data := packed A
  fun i j => cell data i.val j.val

theorem materialize_eq {m k : Nat} (A : Fin m → Fin k → ℚ) :
    materialize A = A := by
  funext i j
  simp [materialize, packed, cell]

/-- A pivot loop with an array allocation after each swap/clear update. -/
def echelonMaterialized {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r c fuel : Nat) : (Fin m → Fin k → ℚ) × List (Fin m × Fin k) :=
  match fuel with
  | 0 => (A, [])
  | fuel + 1 =>
    if hr : r < m then
      if hc : c < k then
        let rf : Fin m := ⟨r, hr⟩
        let cf : Fin k := ⟨c, hc⟩
        match pivotTyped A r cf with
        | none => echelonMaterialized A r (c + 1) fuel
        | some i =>
          let C := materialize (clearTyped (swapTyped A rf i) rf cf)
          let (out, pivots) := echelonMaterialized C (r + 1) (c + 1) fuel
          (out, (rf, cf) :: pivots)
      else (A, [])
    else (A, [])

theorem echelonMaterialized_eq {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r c fuel : Nat) :
    echelonMaterialized A r c fuel = echelonTyped A r c fuel := by
  induction fuel generalizing A r c with
  | zero => rfl
  | succ fuel ih =>
      simp only [echelonMaterialized, echelonTyped]
      split_ifs with hr hc <;> try rfl
      cases hp : pivotTyped A r ⟨c, hc⟩ with
      | none => exact ih A r (c + 1)
      | some i =>
          simp [materialize_eq, ih]

def dependenceMaterialized {m k : Nat} (A : Fin m → Fin k → ℚ) :
    Option (Fin k → ℚ) :=
  let (B, ps) := echelonMaterialized A 0 0 k
  (typedFree ps).map (typedCandidate B ps)

theorem dependenceMaterialized_eq {m k : Nat}
    (A : Fin m → Fin k → ℚ) :
    dependenceMaterialized A = typedDependence A := by
  simp [dependenceMaterialized, typedDependence, echelonMaterialized_eq]

theorem dependenceMaterialized_total {m k : Nat}
    (A : Fin m → Fin k → ℚ) (hkm : m < k) :
    ∃ x, dependenceMaterialized A = some x ∧
      (∃ j : Fin k, x j ≠ 0) ∧
      ∀ i, rowDot A x i = 0 := by
  simpa [dependenceMaterialized_eq] using typedDependence_total A hkm

def materializedArrayDependence (a : Array (Array ℚ)) :
    Option (Array ℚ) :=
  (dependenceMaterialized (matrixOfArray a)).map Array.ofFn

theorem materializedArrayDependence_eq (a : Array (Array ℚ)) :
    materializedArrayDependence a = typedArrayDependence a := by
  simp [materializedArrayDependence, typedArrayDependence,
    dependenceMaterialized_eq]

def certifiedMaterializedDependence (a : Array (Array ℚ)) :
    Option {x : Array ℚ // IsDependence a x} :=
  match materializedArrayDependence a with
  | none => none
  | some x =>
      if h : dependenceCheck a x = true then some ⟨x, h⟩ else none

theorem certifiedMaterializedDependence_eq (a : Array (Array ℚ)) :
    certifiedMaterializedDependence a = certifiedTypedDependence a := by
  simp [certifiedMaterializedDependence, certifiedTypedDependence,
    materializedArrayDependence_eq]
  rfl

theorem certifiedMaterializedDependence_total (a : Array (Array ℚ))
    (h : a.size < columnCount a) :
    ∃ cert, certifiedMaterializedDependence a = some cert := by
  simpa [certifiedMaterializedDependence_eq] using
    certifiedTypedDependence_total a h

#print axioms echelonMaterialized_eq
#print axioms dependenceMaterialized_total
#print axioms certifiedMaterializedDependence_total

end CurrentAdditive.MaterializedGauss
