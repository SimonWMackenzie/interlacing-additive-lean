import CurrentAdditive.HadamardIntegerRelation
import CurrentAdditive.TransientArithmetic

set_option maxHeartbeats 1000000

namespace CurrentAdditive.HadamardTransientAdapter

open SequentialCode SequentialTotality SequentialArrayBridge
open RationalBitBounds MaterializedGauss
open HadamardSupport TransientArithmetic

/-- Integer coefficient fields have the same O(r log(r+1)) budget as the
canonical rational fields used by the implementation. -/
theorem size_le_hadamard_budget (r a : Nat) (ha : a ^ 2 ≤ r ^ r) :
    Nat.size a ≤ r * Nat.size (r + 1) + 1 := by
  have ha' : a ≤ r ^ r := by nlinarith
  have hpow : r ^ r ≤ 2 ^ (r * Nat.size (r + 1)) := by
    calc
      r ^ r ≤ (r + 1) ^ r := Nat.pow_le_pow_left (by omega) _
      _ ≤ (2 ^ Nat.size (r + 1)) ^ r :=
        Nat.pow_le_pow_left (le_of_lt (Nat.lt_size_self _)) _
      _ = 2 ^ (r * Nat.size (r + 1)) := by
        rw [← pow_mul, Nat.mul_comm]
  exact size_le_of_pow_bound (ha'.trans hpow)

/-- Canonical numerator and denominator bits of the actual typed return,
with the exact pivot rank as the coefficient budget parameter. -/
theorem materialized_dependence_hadamard_fits {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (x : Fin k → ℚ)
    (hx : dependenceMaterialized (fun i j => (A i j : ℚ)) = some x) :
    let out := echelonTyped (fun i j => (A i j : ℚ)) 0 0 k
    let r := Fintype.card (PivotIndex out.2)
    ∀ j, Fits (r * Nat.size (r + 1) + 1) (x j) := by
  obtain ⟨f, D, coeff, hf, hD, hDB, hcoeff, hrep, hfc, hs⟩ :=
    materialized_dependence_hadamard A h01 x hx
  dsimp only
  intro j
  exact hadamard_representation_fits (x j) (coeff j) D _ hD
    (hrep j) (hcoeff j) hDB

/-- Ambient feature count replaces actual rank without changing the return. -/
theorem materialized_dependence_hadamard_fits_rows {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (x : Fin k → ℚ)
    (hx : dependenceMaterialized (fun i j => (A i j : ℚ)) = some x) :
    ∀ j, Fits (m * Nat.size (m + 1) + 1) (x j) := by
  have hr := (materialized_integer_hadamard_relation A h01 x hx).1
  have hfits := materialized_dependence_hadamard_fits A h01 x hx
  intro j
  apply fits_mono (hfits j)
  have hsize := Nat.size_le_size (Nat.add_le_add_right hr 1)
  have hprod := Nat.mul_le_mul hr hsize
  omega

/-- The exact bound applies to every entry of the actual eagerly returned
array, through the typed/materialized equality and the original zero-one
array cells. -/
theorem materialized_array_hadamard_fits (a : Array (Array ℚ))
    (h01 : ∀ i : Fin a.size, ∀ j : Fin (columnCount a),
      matrixOfArray a i j = 0 ∨ matrixOfArray a i j = 1)
    (y : Array ℚ) (hy : materializedArrayDependence a = some y) :
    ∀ i : Fin y.size,
      Fits (a.size * Nat.size (a.size + 1) + 1) y[i] := by
  let A : Matrix (Fin a.size) (Fin (columnCount a)) ℤ :=
    fun i j => if matrixOfArray a i j = 0 then 0 else 1
  have hA : ∀ i j, A i j = 0 ∨ A i j = 1 := by
    intro i j
    by_cases h : matrixOfArray a i j = 0
    · exact Or.inl (by simp [A, h])
    · exact Or.inr (by simp [A, h])
  have hAq : (fun i j => (A i j : ℚ)) = matrixOfArray a := by
    funext i j
    by_cases h : matrixOfArray a i j = 0
    · simp [A, h]
    · have h1 := (h01 i j).resolve_left h
      simp [A, h1]
  cases hdep : dependenceMaterialized (matrixOfArray a) with
  | none => simp [materializedArrayDependence, hdep] at hy
  | some x =>
      have hyarr : y = Array.ofFn x := by
        simpa [materializedArrayDependence, hdep] using hy.symm
      have hfits := materialized_dependence_hadamard_fits_rows A hA x
        (by simpa [hAq] using hdep)
      intro i
      let j : Fin (columnCount a) := ⟨i.val, by simpa [hyarr] using i.isLt⟩
      simpa [hyarr, j] using hfits j

/-- Ready-made replacement for the former Gram coefficient-fit adapter.
Its input is the actual certified materialized return, not a bounded
coefficient certificate supplied independently of the program. -/
theorem certified_materialized_hadamard_fits (a : Array (Array ℚ))
    (h01 : ∀ i : Fin a.size, ∀ j : Fin (columnCount a),
      matrixOfArray a i j = 0 ∨ matrixOfArray a i j = 1)
    (cert : {x : Array ℚ // IsDependence a x})
    (hcert : certifiedMaterializedDependence a = some cert) :
    ∀ i : Fin cert.val.size,
      Fits (a.size * Nat.size (a.size + 1) + 1) cert.val[i] := by
  unfold certifiedMaterializedDependence at hcert
  cases hraw : materializedArrayDependence a with
  | none => simp [hraw] at hcert
  | some y =>
      simp only [hraw] at hcert
      split at hcert
      · cases hcert
        exact materialized_array_hadamard_fits a h01 y hraw
      · cases hcert

#print axioms size_le_hadamard_budget
#print axioms materialized_dependence_hadamard_fits
#print axioms materialized_dependence_hadamard_fits_rows
#print axioms materialized_array_hadamard_fits
#print axioms certified_materialized_hadamard_fits

end CurrentAdditive.HadamardTransientAdapter
