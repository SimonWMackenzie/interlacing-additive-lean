import CurrentAdditive.V42HeterogeneousPairLaw
import CurrentAdditive.V38Fin2Exact
import CurrentAdditive.V39TaggedFibrePopulation
import CurrentAdditive.IndexedProfileConditioning

/-! Source v42 `res:paired` at its full finite weighted-list interface.
The base matrix is arbitrary and the two source carriers and laws may differ.
The retained pair set is measured in the original independent product law;
it need not have a product form. Tagged columns remain distinct. -/

namespace CurrentAdditive.V42PairedInterface

open Paper2 Paper2.PairedSelectorPopulation
open CurrentAdditive.ArbitraryPrefix
open CurrentAdditive.DeterministicIndexedMatrix
open scoped BigOperators

variable {Γ J So Sf : Type*}
  [Fintype Γ] [Fintype J] [Fintype So] [Fintype Sf]
  {q : ℕ} [NeZero q]

def matrix (A : Γ → J → Bool)
    (decode_o : So → Fin q → J) (decode_f : Sf → Fin q → J) :
    (So × Sf) → ((Bool × Fin q) × Γ) → Bool :=
  fun z c => A c.2 (V42HeterogeneousPairLaw.concat decode_o decode_f z c.1)

@[simp] theorem matrix_false (A : Γ → J → Bool)
    (decode_o : So → Fin q → J) (decode_f : Sf → Fin q → J)
    (z : So × Sf) (α : Fin q) (γ : Γ) :
    matrix A decode_o decode_f z ((false,α),γ) = A γ (decode_o z.1 α) := rfl

@[simp] theorem matrix_true (A : Γ → J → Bool)
    (decode_o : So → Fin q → J) (decode_f : Sf → Fin q → J)
    (z : So × Sf) (α : Fin q) (γ : Γ) :
    matrix A decode_o decode_f z ((true,α),γ) = A γ (decode_f z.2 α) := rfl

/-- Two independently drawn exact eight-wise lists give one further bit
beyond H+ell. Neither the matrix nor either source has a source-gadget shape.
This includes ell=0 (q=1), epsilon=0, duplicate decoded words, different
source carriers/laws, and arbitrary correlated retention of pair labels. -/
theorem paired_restriction_lower
    (μ : PositiveRationalLaw Γ) (ν : PositiveRationalLaw J)
    (A : Γ → J → Bool) (H ell : ℕ) (hH : 2 ≤ H) (hq : q=2^ell)
    (x : ℝ) (hx : 0 < x)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile A
      μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (σo : FiniteLaw So) (σf : FiniteLaw Sf)
    (decode_o : So → Fin q → J) (decode_f : Sf → Fin q → J)
    (ho : IsDWise 8 σo decode_o ν.toFiniteLaw)
    (hf : IsDWise 8 σf decode_f ν.toFiniteLaw)
    (K : Set (So × Sf)) (O F : Set (Fin q × Γ)) (ε δ : ℝ)
    (hK : (49/64 : ℝ) ≤ (σo.prod σf).prob (· ∈ K))
    (hO : 1-ε ≤ (columnLaw μ (I := Fin q)).toFiniteLaw.prob (· ∈ O))
    (hF : δ ≤ (columnLaw μ (I := Fin q)).toFiniteLaw.prob (· ∈ F))
    (hε : 0 ≤ ε) (hδpos : 0 < δ) (hδ : δ ≤ 1)
    (hsmall : 2*q*x ≤ 1/8) (hslack : 2*q*x+ε < δ) :
    H+ell+1 ≤ Compression.restrictionD (matrix A decode_o decode_f) K (columns O F) := by
  classical
  let t : ℝ := 2*q*x
  let Tags := Bool × Fin q
  let e := Fintype.equivFin Tags
  let TaggedGood := V39TaggedFibrePopulation.taggedGood μ.toFiniteLaw O F t
  let Good := TaggedGood.image e
  let Rows : Fin (Fintype.card Tags) → Set Γ := fun i =>
    {γ | γ ∈ support O F (e.symm i)}
  let decode : So × Sf → Fin (Fintype.card Tags) → J :=
    fun z i => V42HeterogeneousPairLaw.concat decode_o decode_f z (e.symm i)
  have hwise : IsDWise 8 (σo.prod σf) decode ν.toFiniteLaw := by
    exact isDWise_reindex 8 (σo.prod σf) ν.toFiniteLaw
      (V42HeterogeneousPairLaw.concat decode_o decode_f) e.symm e.symm.injective
      (V42HeterogeneousPairLaw.concat_dwise 8 σo σf ν.toFiniteLaw decode_o decode_f ho hf)
  have htag : q < TaggedGood.card := by
    simpa only [TaggedGood,t,Fintype.card_fin] using
      V39TaggedFibrePopulation.tagged_good_count_gt μ O F (2*q*x) ε δ hO hF hε hδ hslack
  have hcount : 2^((ell+1)-1)+1 ≤ Good.card := by
    dsimp only [Good]
    rw [Finset.card_image_of_injective _ e.injective]
    simp only [Nat.add_sub_cancel]
    rw [← hq]
    omega
  have hpow : (2 : ℝ)^(ell+1)=2*(q : ℝ) := by
    exact_mod_cast (show (2 : ℕ)^(ell+1)=2*q from by rw [pow_succ,← hq]; omega)
  have hscale : (2 : ℝ)^(ell+1)*x ≤ 1 := by rw [hpow]; linarith
  have hrow : ∀ i ∈ Good, (2 : ℝ)^(ell+1)*x ≤ μ.toFiniteLaw.prob (· ∈ Rows i) := by
    intro i hi
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
    have hm := V39TaggedFibrePopulation.tagged_good_floor μ.toFiniteLaw O F t a ha
    simpa only [Rows,e.symm_apply_apply,SourceSupportStep.mass,hpow,t] using hm
  have hmass : (9/25 : ℝ) ≤ (σo.prod σf).prob (· ∈ K) := by linarith
  have hlower := V38Fin2Exact.exactboost μ ν A (σo.prod σf) decode hwise
    Good Rows K H (ell+1) x (by omega) hH hx hscale hprofile hcount hrow hmass
  let cMap : (Fin (Fintype.card Tags) × Γ) → (Tags × Γ) := fun a => (e.symm a.1,a.2)
  have hmapped : Set.MapsTo cMap (rowRectangle Good Rows) (columns O F) := by
    intro a ha
    exact initial_reaches O F (e.symm a.1) a.2 ha.2
  have hmap := SourceProjection.restrictionD_map_le
    (fun c z => matrix A decode_o decode_f z c) cMap id
    (columns O F) K (rowRectangle Good Rows) K hmapped (fun _ h => h)
  change Compression.restrictionD (fun a z => A a.2 (decode z a.1))
    (rowRectangle Good Rows) K ≤ _ at hmap
  rw [SourceProjection.restrictionD_transpose (matrix A decode_o decode_f) K (columns O F)] at hmap
  exact (by omega : H+ell+1 ≤ H+(ell+1)).trans (hlower.trans hmap)

end CurrentAdditive.V42PairedInterface

#print axioms CurrentAdditive.V42PairedInterface.paired_restriction_lower
