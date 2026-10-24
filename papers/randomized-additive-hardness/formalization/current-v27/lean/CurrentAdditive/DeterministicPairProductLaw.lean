import CurrentAdditive.DeterministicSuffixLongSource

/-! Private Appendix H bridge: the actual indicators of disjoint selected
original-coordinate pairs have a heterogeneous Bernoulli product law. -/

namespace CurrentAdditive.SuffixLong

open Paper2

variable {Z S : Type*} [Fintype Z] [Fintype S]

/-- The finite law of a Boolean test on a finite source. -/
noncomputable def boolImageLaw {Ω : Type*} [Fintype Ω]
    (ρ : FiniteLaw Ω) (f : Ω → Bool) : FiniteLaw Bool where
  weight b := ρ.prob (fun ω => f ω = b)
  nonneg b := ρ.prob_nonneg _
  total := by
    classical
    simp only [Fintype.sum_bool]
    change ρ.prob (fun ω => f ω = true) +
      ρ.prob (fun ω => f ω = false) = 1
    unfold FiniteLaw.prob
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ ω : Ω, ρ.weight ω := by
        apply Finset.sum_congr rfl
        intro ω _
        cases h : f ω <;> simp [h]
      _ = 1 := ρ.total

def pairBlock {m q : ℕ} (e : Fin (2*m) → Fin q) (i : Fin m) :
    Finset (Fin q) :=
  Finset.univ.image (fun j : Fin 2 => e (pairPosition i j))

theorem pairBlock_mem {m q : ℕ} (e : Fin (2*m) → Fin q)
    (i : Fin m) (j : Fin 2) :
    e (pairPosition i j) ∈ pairBlock e i := by
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

noncomputable def localPairHit {m q : ℕ} (decode : S → Fin q → Z)
    (e : Fin (2*m) → Fin q) (K : Set S) (i : Fin m)
    (z : pairBlock e i → Z) : Bool := by
  classical
  exact decide ((fun j : Fin 2 => z ⟨e (pairPosition i j), pairBlock_mem e i j⟩)
    ∈ pairImage decode e K i)

omit [Fintype Z] [Fintype S] in
theorem localPairHit_restrict {m q : ℕ} (decode : S → Fin q → Z)
    (e : Fin (2*m) → Fin q) (K : Set S) (i : Fin m)
    (c : Fin q → Z) :
    localPairHit decode e K i (fun j => c j.val) =
      pairHit decode e K i c := by
  rfl

omit [Fintype S] in
/-- The full vector of actual pair-image tests is a product of its Boolean
marginal laws. The tests may correlate the two columns within each pair;
only different pairs are independent. -/
theorem pairHit_vector_product_law (ν : FiniteLaw Z) {m q : ℕ}
    (decode : S → Fin q → Z) (e : Fin (2*m) → Fin q)
    (he : Function.Injective e) (K : Set S)
    (E : (Fin m → Bool) → Prop) :
    (ν.iid q).prob (fun c => E (fun i => pairHit decode e K i c)) =
      (FiniteLaw.pi (fun i : Fin m =>
        boolImageLaw (ν.iid q) (pairHit decode e K i))).prob E := by
  classical
  let ρ := ν.iid q
  let μ : Fin m → FiniteLaw Bool :=
    fun i => boolImageLaw ρ (pairHit decode e K i)
  apply FiniteLaw.prob_preimage_eq_of_fibres ρ (FiniteLaw.pi μ)
    (fun c i => pairHit decode e K i c)
  intro v
  have hatom : ρ.prob (fun c => (fun i => pairHit decode e K i c) = v) =
      ∏ i : Fin m, ρ.prob (fun c => pairHit decode e K i c = v i) := by
    have h := ProductProjections.prob_disjoint_blocks
      (fun _ : Fin q => ν) (pairBlock e) (selected_pairs_disjoint e he)
      (fun i z => localPairHit decode e K i z = v i)
    have hblock (i : Fin m) :
        (FiniteLaw.pi (fun j : pairBlock e i => ν)).prob
          (fun z => localPairHit decode e K i z = v i) =
        ρ.prob (fun c => pairHit decode e K i c = v i) := by
      have hr := FiniteLaw.pi_prob_restrict (fun _ : Fin q => ν)
        (fun j : pairBlock e i => j.val) Subtype.val_injective
        (fun z => localPairHit decode e K i z = v i)
      simpa only [FiniteLaw.iid, ρ, localPairHit_restrict] using hr.symm
    simpa only [FiniteLaw.iid, ρ, localPairHit_restrict, funext_iff] using
      h.trans (by
        apply Finset.prod_congr rfl
        intro i _
        exact hblock i)
  rw [hatom]
  rfl

#print axioms pairHit_vector_product_law

end CurrentAdditive.SuffixLong
