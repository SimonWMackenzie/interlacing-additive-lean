import Paper2.SourceLawBinding
import Paper2.RestrictionProfiles

/-!
# Exact iid law transport under labelled coordinate and value equivalences

This generic lemma is for finite positive-rational laws. It explicitly
preserves every labelled coordinate, including when values repeat. It does
not assert any pointwise agreement of sampler outputs on a shared tape.
-/

namespace Paper2.CoordinateLawTransport

open scoped BigOperators

variable {A B : Type*} [Fintype A] [Fintype B]

/-- A new-position to old-position equivalence `π` precomposes the old
tuple; the value equivalence is applied at each retained labelled slot. -/
def tupleEquiv (n : ℕ) (π : Fin n ≃ Fin n) (e : A ≃ B) :
    (Fin n → A) ≃ (Fin n → B) where
  toFun f j := e (f (π j))
  invFun g i := e.symm (g (π.symm i))
  left_inv f := by
    funext i
    simp
  right_inv g := by
    funext j
    simp

omit [Fintype A] [Fintype B] in
@[simp] theorem tupleEquiv_apply (n : ℕ) (π : Fin n ≃ Fin n) (e : A ≃ B)
    (f : Fin n → A) (j : Fin n) :
    tupleEquiv n π e f j = e (f (π j)) := rfl

omit [Fintype A] [Fintype B] in
/-- No quotient by equal values occurs: two independently labelled tuples
remain distinct whenever they differed at any labelled coordinate. -/
theorem tupleEquiv_injective (n : ℕ) (π : Fin n ≃ Fin n) (e : A ≃ B) :
    Function.Injective (tupleEquiv n π e) := (tupleEquiv n π e).injective

/-- Exact rational weight equality, not merely equal carrier cardinality.
The product reindexing retains labels even when several `f i` coincide. -/
theorem iid_weight (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B)
    (n : ℕ) (π : Fin n ≃ Fin n) (e : A ≃ B)
    (hweight : ∀ a, ν.weight (e a) = μ.weight a)
    (f : Fin n → A) :
    (ν.iid n).weight (tupleEquiv n π e f) = (μ.iid n).weight f := by
  simp only [PositiveRationalLaw.iid, tupleEquiv_apply]
  simp_rw [hweight]
  exact π.prod_comp (fun i => μ.weight (f i))

/-- The full joint law, on every event of the relabelled tuple. In particular
the `n=0` empty product is included; no nonempty-coordinate hypothesis is
introduced. -/
theorem iid_prob_relabel (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B)
    (n : ℕ) (π : Fin n ≃ Fin n) (e : A ≃ B)
    (hweight : ∀ a, ν.weight (e a) = μ.weight a)
    (E : (Fin n → B) → Prop) :
    (μ.iid n).toFiniteLaw.prob (fun f => E (tupleEquiv n π e f)) =
      (ν.iid n).toFiniteLaw.prob E := by
  classical
  unfold FiniteLaw.prob
  have hs := (tupleEquiv n π e).sum_comp
    (fun g => if E g then ((ν.iid n).weight g : ℝ) else 0)
  simpa only [PositiveRationalLaw.toFiniteLaw, iid_weight μ ν n π e hweight,
    Rat.cast_inj] using hs

/-- The same claim in the repository's arbitrary-event pushforward form. -/
theorem iid_pushesTo (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B)
    (n : ℕ) (π : Fin n ≃ Fin n) (e : A ≃ B)
    (hweight : ∀ a, ν.weight (e a) = μ.weight a) :
    (μ.iid n).toFiniteLaw.PushesTo (ν.iid n).toFiniteLaw
      (tupleEquiv n π e) := by
  intro E
  exact iid_prob_relabel μ ν n π e hweight E

/-- Explicit zero-coordinate specialization: the generic arbitrary-event
identity includes the unique empty tuple, with empty-product mass one. -/
theorem iid_prob_relabel_zero (μ : PositiveRationalLaw A)
    (ν : PositiveRationalLaw B) (e : A ≃ B)
    (hweight : ∀ a, ν.weight (e a) = μ.weight a)
    (E : (Fin 0 → B) → Prop) :
    (μ.iid 0).toFiniteLaw.prob
      (fun f => E (tupleEquiv 0 (Equiv.refl (Fin 0)) e f)) =
      (ν.iid 0).toFiniteLaw.prob E :=
  iid_prob_relabel μ ν 0 (Equiv.refl (Fin 0)) e hweight E

/-- Invariance of the actual uniform positive-rational law on a nonempty
`Fin m` carrier under any label permutation and any tuple-position
permutation. `n` may still be zero. -/
noncomputable def uniformFin (m : ℕ) (hm : 0 < m) :
    PositiveRationalLaw (Fin m) := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact PositiveRationalLaw.uniform (Fin m)

theorem uniformFin_iid_pushesTo (m n : ℕ) (hm : 0 < m)
    (π : Fin n ≃ Fin n) (e : Fin m ≃ Fin m) :
    ((uniformFin m hm).iid n).toFiniteLaw.PushesTo
      ((uniformFin m hm).iid n).toFiniteLaw
      (tupleEquiv n π e) := by
  apply iid_pushesTo
  intro a
  rfl

#print axioms iid_weight
#print axioms iid_prob_relabel
#print axioms iid_pushesTo
#print axioms iid_prob_relabel_zero
#print axioms uniformFin_iid_pushesTo

end Paper2.CoordinateLawTransport
