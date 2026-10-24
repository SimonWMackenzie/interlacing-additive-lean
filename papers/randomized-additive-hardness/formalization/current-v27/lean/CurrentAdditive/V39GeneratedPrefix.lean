import CurrentAdditive.V38Fin2IndexedSeparation
import CurrentAdditive.V39GeneratedSourceBridge

/-! Actual finite ordinal labels of the selected generated construction.
The template width is literally `s-2`; the protocol computes SourceData.B
on the retained inputs, rather than a replacement decoded matrix. -/

namespace CurrentAdditive.V39GeneratedPrefix

open Paper2 Workspace.Types.Protocol
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.V39GeneratedConstruction
open CurrentAdditive.V39GeneratedSourceBridge

variable {D q₂ t nx ny ni : ℕ}
  [NeZero q₂] [NeZero (2^t)] [NeZero (2^t-2)]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}

/-- The actual indexed template entry on the retained finite alphabets. -/
def template
    (src : SourceData (D := D) (q₁ := 2^t-2) (q₂ := q₂) (s := 2^t) μX μY)
    (R : Fin nx → Fin ny → Bool) (z : Fin src.inner.size)
    (j : Fin q₂ × Fin src.gamma.size) : Bool :=
  R (src.inner.decode z j.1).2
    (SourceMatrix.head (src.gamma.decode j.2) (src.inner.decode z j.1).1)

theorem template_eq
    (src : SourceData (D := D) (q₁ := 2^t-2) (q₂ := q₂) (s := 2^t) μX μY)
    (R : Fin nx → Fin ny → Bool) :
    Sources.T (toSources src) R = template src R := rfl

def retainedPrefixFibre
    (src : SourceData (D := D) (q₁ := 2^t-2) (q₂ := q₂) (s := 2^t) μX μY)
    {U : Set src.Column} {V : Set (src.Row (ni := ni))}
    (P : Protocol V U Bool) (p w : Fin (2^t)) : Set (Fin src.inner.size) :=
  {z | ∃ h : (Sum.inl (p,z) : src.Row (ni := ni)) ∈ V,
    NPCC.Protocol.prefixCodeRaw t P ⟨Sum.inl (p,z),h⟩ = w}

theorem separation
    (src : SourceData (D := D) (q₁ := 2^t-2) (q₂ := q₂) (s := 2^t) μX μY)
    (hD : 8 ≤ D) (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin (2^t)))
    (U : Set src.Column) (V : Set (src.Row (ni := ni)))
    (P : Protocol V U Bool)
    (d : ℕ) (ρ z : ℝ)
    (ht : 2 ≤ t) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hscale : (2 : ℝ)^t*ρ ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (template src R)
      src.inner.law.toFiniteLaw
      (product (uniform q₂) src.gamma.law).toFiniteLaw ρ (d : ℤ))
    (hrow : ∀ p : Fin (2^t), z ≤ src.inner.law.toFiniteLaw.prob
      (fun x => (Sum.inl (p,x) : src.Row (ni := ni)) ∈ V))
    (hgap : 2*(2 : ℝ)^t*ρ < z)
    (hU : (99/100 : ℝ) < src.columnLaw.toFiniteLaw.prob (· ∈ U))
    (hcost : P.cost ≤ d+t)
    (hcompute : P.Computes (fun v u => src.B R activity v.val u.val)) :
    SourceProtocolPrefixTree.CompleteAlicePrefix t P ∧
    ∃ dom : Fin (2^t) ≃ Fin (2^t),
      (∀ w, z/(2 : ℝ)^t ≤ src.inner.law.toFiniteLaw.prob
        (· ∈ retainedPrefixFibre src P (dom w) w)) ∧
      (∀ w j, j ≠ dom w → src.inner.law.toFiniteLaw.prob
        (· ∈ retainedPrefixFibre src P j w) < 2*ρ) ∧
      (∀ w, z-2*((2^t : ℕ)-1 : ℕ)*ρ < src.inner.law.toFiniteLaw.prob
        (· ∈ retainedPrefixFibre src P (dom w) w)) := by
  classical
  let y₀ : Fin ny := Classical.choice μY.toFiniteLaw.nonempty
  let ξ₀ : SourceMatrix.Tail (2^t) (Fin ny) := fun _ => y₀
  have hprofile' : V38RestrictionProfiles.TwoThresholdProfile (Sources.T (toSources src) R)
      (toSources src).inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod (toSources src).gamma.law).toFiniteLaw
      ρ (d : ℤ) := by
    simpa only [template_eq,product_eq,uniform_eq] using hprofile
  have hU' : (99/100 : ℝ) < (V38IndexedTwoTag.law (toSources src)).toFiniteLaw.prob
      (· ∈ U) := by simpa only [columnLaw_eq] using hU
  have hcompute' : P.Computes (fun v u =>
      V38IndexedTwoTag.matrix (toSources src) R activity ξ₀ u.val v.val) := by
    intro v u
    exact (hcompute v u).trans (matrix_eq src R activity ξ₀ u.val v.val).symm
  exact V38IndexedTwoTag.indexed_two_threshold_separation (toSources src)
    hD R activity ξ₀ U V P d ρ z (by omega) hd hρ hscale hprofile'
    hrow hgap hU' hcost hcompute'

#print axioms template_eq
#print axioms separation

end CurrentAdditive.V39GeneratedPrefix
