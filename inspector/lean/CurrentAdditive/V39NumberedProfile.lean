import CurrentAdditive.V39GeneratedTable
import CurrentAdditive.V39GeneratedSourceBridge
import CurrentAdditive.V38RestrictionProfiles
import Paper2.SourceLawBinding

/-! Finite law and restriction transport for the actual numbered constructor.
The target matrix is not supplied as a new presentation or certificate.
-/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2

theorem reindex_prob {A : Type} [Fintype A] {n : ℕ}
    (e : A ≃ Fin n) (μ : PositiveRationalLaw A) (P : Fin n → Prop) :
    (reindex e μ).toFiniteLaw.prob P = μ.toFiniteLaw.prob (fun a => P (e a)) := by
  have hlaw : reindex e μ=μ.relabel e := by
    cases μ
    rfl
  rw [hlaw]
  exact PositiveRationalLaw.relabel_prob μ e P

namespace SourceData

variable {q₁ q₂ s w Q nx ny ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  {μI : PositiveRationalLaw (Fin ni)}
  (src : SourceData (D:=8192) (q₁:=q₁) (q₂:=q₂) (s:=s) μX μY)
  (st : src.Streams (w:=w) (μI:=μI))
  (out : ExactList 8192 Q (Fin w × src.Column) (product (uniform w) src.columnLaw))

theorem numbered_profile
    (R : Fin nx → Fin ny → Bool) (act : Fin ni → Fin q₂ → Option (Fin s))
    (ρ : ℝ) (d : ℤ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile (src.successor st out R act)
      out.law.toFiniteLaw (product (uniform Q) (Streams.law src st)).toFiniteLaw ρ d) :
    V38RestrictionProfiles.TwoThresholdProfile (src.numbered st out R act).entry
      (src.numbered st out R act).rowLaw.toFiniteLaw
      (src.numbered st out R act).colLaw.toFiniteLaw ρ d := by
  classical
  intro j U Z hU hZ
  let e := successorColumnOrder (Q:=Q) src st
  have hZ' : ((3/5:ℝ)*(1/2:ℝ)^j.val) ≤
      (product (uniform Q) (Streams.law src st)).toFiniteLaw.prob
        (fun a => e a ∈ Z) := by
    rw [← reindex_prob e]
    exact hZ
  have h := hp j U (e ⁻¹' Z) hU hZ'
  have heq : Compression.restrictionD (src.successor st out R act) U (e ⁻¹' Z) =
      Compression.restrictionD (src.numbered st out R act).entry U Z := by
    have h' := restrictionD_pullback_preimage (src.numbered st out R act).entry
      id e Function.surjective_id e.surjective U Z
    have hf : (fun a b => (src.numbered st out R act).entry (id a) (e b)) =
        src.successor st out R act := by
      funext a b
      change src.successor st out R act a (e.symm (e b)) = _
      rw [Equiv.symm_apply_apply]
    rw [hf] at h'
    exact h'
  simpa only [heq] using h

end SourceData
end CurrentAdditive.V39GeneratedConstruction

#print axioms CurrentAdditive.V39GeneratedConstruction.SourceData.numbered_profile
