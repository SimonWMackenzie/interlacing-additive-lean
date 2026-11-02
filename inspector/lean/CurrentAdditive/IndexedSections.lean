import CurrentAdditive.IndexedMetadataTail

/-! Averaging over complete independent source indices, with the selector
source left unfixed. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2
open scoped BigOperators

private theorem positive_product_section
    {A B : Type*} [Fintype A] [Fintype B]
    (ρ : PositiveRationalLaw A) (σ : PositiveRationalLaw B)
    (E : A → B → Prop) (v : ℝ)
    (h : v ≤ (ρ.prod σ).toFiniteLaw.prob (fun z => E z.1 z.2)) :
    ∃ a : A, v ≤ σ.toFiniteLaw.prob (E a) := by
  classical
  have hprod : (ρ.prod σ).toFiniteLaw =
      ρ.toFiniteLaw.prod σ.toFiniteLaw :=
    PositiveRationalLaw.toFiniteLaw_prod ρ σ
  rw [hprod, FiniteLaw.prod_prob ρ.toFiniteLaw σ.toFiniteLaw E] at h
  have hconst : (∑ a : A, v * ρ.toFiniteLaw.weight a) = v := by
    rw [← Finset.mul_sum, ρ.toFiniteLaw.total, mul_one]
  have hsum : (∑ a : A, v * ρ.toFiniteLaw.weight a) ≤
      ∑ a : A, ρ.toFiniteLaw.weight a * σ.toFiniteLaw.prob (E a) := by
    rwa [hconst]
  let a₀ : A := Classical.choice ρ.nonempty
  have hnonempty : (Finset.univ : Finset A).Nonempty :=
    ⟨a₀, Finset.mem_univ _⟩
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_sum_le hnonempty
    (by simpa using hsum)
  refine ⟨a, ?_⟩
  have hp : 0 < ρ.toFiniteLaw.weight a := by
    change (0 : ℝ) < (ρ.weight a : ℝ)
    exact_mod_cast ρ.positive a
  nlinarith [ha]

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : Sources.InternalStreams src μI w)

/-- Any positive-mass event in the actual triple product has a complete
metadata index and complete base index whose selector section retains at
least that mass.  The source labels are never collapsed to decoded words. -/
theorem exists_complete_stream_section
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (Good : streams.metadataStream.Label → Prop) (v : ℝ) (hv : 0 < v)
    (hY : v ≤ streams.law.toFiniteLaw.prob
      (fun a => a ∈ Yevent ∧ Good a.1)) :
    ∃ md : streams.metadataStream.Label,
      Good md ∧ ∃ base : streams.baseStream.Label,
      v ≤ streams.selectorStream.law.toFiniteLaw.prob
        (fun select => (md, (base, select)) ∈ Yevent) := by
  let ρ := streams.metadataStream.law
  let σ := streams.baseStream.law
  let τ := streams.selectorStream.law
  have houter : v ≤ (ρ.prod (σ.prod τ)).toFiniteLaw.prob
      (fun z => z ∈ Yevent ∧ Good z.1) := by
    simpa [Sources.InternalStreams.law, ρ, σ, τ] using hY
  obtain ⟨md, hmd⟩ := positive_product_section ρ (σ.prod τ)
    (fun md bt => (md, bt) ∈ Yevent ∧ Good md) v houter
  have hgood : Good md := by
    by_contra hn
    have hz : (σ.prod τ).toFiniteLaw.prob
        (fun bt => (md, bt) ∈ Yevent ∧ Good md) = 0 := by
      simp [hn]
    linarith
  have hbase : v ≤ (σ.prod τ).toFiniteLaw.prob
      (fun bt => (md, bt) ∈ Yevent) := by
    simpa [hgood] using hmd
  obtain ⟨base, hselect⟩ := positive_product_section σ τ
    (fun base select => (md, (base, select)) ∈ Yevent) v hbase
  exact ⟨md, hgood, base, hselect⟩

#print axioms exists_complete_stream_section

end CurrentAdditive.DeterministicIndexedMatrix
