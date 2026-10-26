import CurrentAdditive.CoefficientScale
import CurrentAdditive.SequentialSourceCode

set_option maxHeartbeats 1000000

namespace CurrentAdditive.RationalCandidateCompletion

open CurrentAdditive.SequentialCode
open CurrentAdditive.SequentialArrayBridge
open CurrentAdditive.MaterializedGauss
open CurrentAdditive.RationalBitBounds
open CurrentAdditive.SequentialSourceCode

theorem featureRows_zero_one {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (source : Array (α × ℚ))
    (hφ : ∀ x j, φ x j = 0 ∨ φ x j = 1) :
    ∀ i : Fin (featureRows n φ source).size,
      ∀ j : Fin (columnCount (featureRows n φ source)),
        matrixOfArray (featureRows n φ source) i j = 0 ∨
          matrixOfArray (featureRows n φ source) i j = 1 := by
  intro i j
  let a := featureRows n φ source
  have hi : i.val < n := by simpa [a, featureRows] using i.isLt
  by_cases hj : j.val < source.size
  · have hcell : matrixOfArray a i j = φ (source[j.val]).1 ⟨i.val, hi⟩ := by
      simp [matrixOfArray, cell, a, featureRows, hi, hj]
    rw [hcell]
    exact hφ _ _
  · have hcell : matrixOfArray a i j = 0 := by
      simp [matrixOfArray, cell, a, featureRows, hi, hj]
    exact Or.inl hcell

theorem generatedFeatureRows_zero_one {Y : Type*} [DecidableEq Y]
    (q D : Nat) (alphabet : Array Y)
    (source : Array ((Fin q → Y) × ℚ)) :
    let F := generatedFeatures q D alphabet
    let φ : (Fin q → Y) → Fin F.size → ℚ :=
      fun v j => generatedFeatureValue v F[j]
    ∀ i : Fin (featureRows F.size φ source).size,
      ∀ j : Fin (columnCount (featureRows F.size φ source)),
        matrixOfArray (featureRows F.size φ source) i j = 0 ∨
          matrixOfArray (featureRows F.size φ source) i j = 1 := by
  intro F φ
  apply featureRows_zero_one F.size φ source
  intro v j
  dsimp [φ, generatedFeatureValue]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- One successful physical support-elimination call, using precisely the
relation returned by `certifiedMaterializedDependence`, grows a represented
common denominator by at most `2^(4m log₂(m+1))` where m is the row count.
No product of component denominators is used. -/
theorem certified_materialized_update_bound
    (a : Array (Array ℚ)) (weights out : Array ℚ)
    (h01 : ∀ i : Fin a.size, ∀ j : Fin (columnCount a),
      matrixOfArray a i j = 0 ∨ matrixOfArray a i j = 1)
    (hweights : weights.size = columnCount a)
    (cert : {x : Array ℚ // IsDependence a x})
    (hcert : certifiedMaterializedDependence a = some cert)
    (hout : eliminateWeights weights cert.val = some out)
    (enc : CommonDenominator (fun i : Fin weights.size => weights[i])) :
    ∃ next : CommonDenominator
        (fun i : Fin weights.size => out[i.val]?.getD 0),
      out.size = weights.size ∧
      next.denominator ≤ enc.denominator *
        2 ^ (4 * a.size * Nat.size (a.size + 1)) := by
  obtain ⟨D, coeff, hD, _, hcoeffBound, hcertSize, hcertRep⟩ :=
    certified_materialized_shared a h01 cert hcert
  have hsame : cert.val.size = weights.size := by omega
  let z : Fin weights.size → ℤ := fun i =>
    coeff ⟨i.val, by omega⟩
  have hzBound (i : Fin weights.size) :
      (z i).natAbs ≤ (a.size.factorial * a.size ^ a.size) ^ 2 := by
    exact hcoeffBound ⟨i.val, by omega⟩
  have hrep (i : Fin weights.size) :
      cert.val[i.val]?.getD 0 = (z i : ℚ) / (D : ℚ) := by
    simpa [z] using hcertRep ⟨i.val, by omega⟩
  obtain ⟨j, hjpos, hsize, hrepr⟩ :=
    eliminateWeights_shared_denominator weights cert.val out hsame
      hout D hD z hrep enc
  let next : CommonDenominator
      (fun i : Fin weights.size => out[i.val]?.getD 0) :=
    { denominator := enc.denominator * (z j).toNat
      positive := Nat.mul_pos enc.positive (by omega)
      numerator := removedNumerator enc.numerator z j
      represents := hrepr }
  refine ⟨next, hsize, ?_⟩
  have hznat : (z j).toNat = (z j).natAbs := by omega
  have hcoef : (z j).toNat ≤
      2 ^ (4 * a.size * Nat.size (a.size + 1)) := by
    rw [hznat]
    calc
      (z j).natAbs ≤ (a.size.factorial * a.size ^ a.size) ^ 2 := hzBound j
      _ ≤ (a.size + 1) ^ (4 * a.size) := shared_gram_pow_bound _
      _ ≤ (2 ^ Nat.size (a.size + 1)) ^ (4 * a.size) :=
        Nat.pow_le_pow_left (le_of_lt (Nat.lt_size_self _)) _
      _ = 2 ^ (4 * a.size * Nat.size (a.size + 1)) := by
        simp only [← pow_mul]
        congr 1
        ring
  exact Nat.mul_le_mul_left _ hcoef

#print axioms certified_materialized_update_bound
#print axioms generatedFeatureRows_zero_one

end CurrentAdditive.RationalCandidateCompletion
