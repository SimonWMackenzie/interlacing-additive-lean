import CurrentAdditive.V38IndexedTwoTag
import CurrentAdditive.V38Fin2SourceSeparation
import CurrentAdditive.DeterministicIndexedTemplates
import Paper2.AModelTape

/-! v39 `src:near-full`: the common prefix and its dominant bins on the
actual indexed two-family source.  Projection forgets only the independent
ordinary tail label, never the outer source index or duplicate labels. -/

namespace CurrentAdditive.V38IndexedTwoTag

open Paper2 Workspace.Types.Protocol
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ t : ℕ} [NeZero q₁] [NeZero q₂] [NeZero (2^t)]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := 2^t) μX μY)

/-- The original outer index has some retained ordinary completion. -/
def outerRetained (U : Set (Column src)) : Set src.outer.Label :=
  {j | ∃ γ : src.gamma.Label, Sum.inl (j,γ) ∈ U}

theorem outer_projection_mass (U : Set (Column src)) :
    (src.outer.law.prod src.gamma.law).toFiniteLaw.prob
        (fun z => Sum.inl z ∈ U) ≤
      src.outer.law.toFiniteLaw.prob (· ∈ outerRetained src U) := by
  rw [PositiveRationalLaw.toFiniteLaw_prod]
  calc
    _ ≤ (src.outer.law.toFiniteLaw.prod src.gamma.law.toFiniteLaw).prob
        (fun z => z.1 ∈ outerRetained src U) := by
      apply FiniteLaw.prob_mono
      intro z hz
      exact ⟨z.2,hz⟩
    _ = _ := AModel.prod_prob_fst _ _ _

/-- This original-label image has sufficient mass before any conditioning.
One completion may be chosen for each index independently of every row. -/
theorem retained_outer_mass_and_representatives
    (U : Set (Column src))
    (hU : (99/100 : ℝ) < (law src).toFiniteLaw.prob (· ∈ U)) :
    (18/25 : ℝ) ≤ src.outer.law.toFiniteLaw.prob (· ∈ outerRetained src U) ∧
    ∀ j : outerRetained src U, ∃ γ : src.gamma.Label, Sum.inl (j.val,γ) ∈ U := by
  have hsplit := prob_split src (· ∈ U)
  have hdiag := (((PositiveRationalLaw.uniform (Fin q₂)).prod
    src.gamma.law).toFiniteLaw).prob_le_one (fun z => Sum.inr z ∈ U)
  have hord : (18/25 : ℝ) ≤ (src.outer.law.prod src.gamma.law).toFiniteLaw.prob
      (fun z => Sum.inl z ∈ U) := by linarith
  exact ⟨hord.trans (outer_projection_mass src U),fun j => j.property⟩

theorem indexed_outer_eight_wise (hD : 8 ≤ D) :
    IsDWise 8 src.outer.law.toFiniteLaw src.outer.decode
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw := by
  intro J hJ E
  exact src.outer.exactLaw J (hJ.trans hD) E

/-- Actual retained template labels reaching an actual Alice prefix code. -/
def retainedIndexedPrefixFibre
    {U : Set (Column src)} {V : Set (Row (I := I) src)}
    (P : Protocol V U Bool) (p w : Fin (2^t)) : Set src.inner.Label :=
  {z | ∃ h : (Sum.inl (p,z) : Row (I := I) src) ∈ V,
    NPCC.Protocol.prefixCodeRaw t P ⟨Sum.inl (p,z),h⟩ = w}

/-- The original unpruned protocol, including all its retained diagonal
columns and item rows, has this complete prefix and dominant-bin assignment.
The only source profile premise is the current template profile. -/
theorem indexed_two_threshold_separation
    (hD : 8 ≤ D) (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin (2^t)))
    (ξ₀ : Paper2.SourceMatrix.Tail (2^t) Y)
    (U : Set (Column src)) (V : Set (Row (I := I) src))
    (P : Protocol V U Bool)
    (d : ℕ) (ρ z : ℝ)
    (ht : 1 ≤ t) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hscale : (2 : ℝ)^t*ρ ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (Sources.T src R)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw ρ (d : ℤ))
    (hrow : ∀ p : Fin (2^t), z ≤ src.inner.law.toFiniteLaw.prob
      (fun x => (Sum.inl (p,x) : Row (I := I) src) ∈ V))
    (hgap : 2*(2 : ℝ)^t*ρ < z)
    (hU : (99/100 : ℝ) < (law src).toFiniteLaw.prob (· ∈ U))
    (hcost : P.cost ≤ d+t)
    (hcompute : P.Computes (fun v u => matrix src R activity ξ₀ u.val v.val)) :
    SourceProtocolPrefixTree.CompleteAlicePrefix t P ∧
    ∃ dom : Fin (2^t) ≃ Fin (2^t),
      (∀ w, z/(2 : ℝ)^t ≤ src.inner.law.toFiniteLaw.prob
        (· ∈ retainedIndexedPrefixFibre src P (dom w) w)) ∧
      (∀ w j, j ≠ dom w → src.inner.law.toFiniteLaw.prob
        (· ∈ retainedIndexedPrefixFibre src P j w) < 2*ρ) ∧
      (∀ w, z-2*((2^t : ℕ)-1 : ℕ)*ρ < src.inner.law.toFiniteLaw.prob
        (· ∈ retainedIndexedPrefixFibre src P (dom w) w)) := by
  classical
  let K : Set src.outer.Label := outerRetained src U
  obtain ⟨hK,hreps⟩ := retained_outer_mass_and_representatives src U hU
  have hKne : K.Nonempty := by
    by_contra hn
    have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    change (18/25 : ℝ) ≤ src.outer.law.toFiniteLaw.prob (· ∈ K) at hK
    simp [he] at hK
    norm_num at hK
  let γ : K → src.gamma.Label := fun j => (hreps j).choose
  have hγ (j : K) : Sum.inl (j.val,γ j) ∈ U := (hreps j).choose_spec
  let j₀ : K := ⟨hKne.choose,hKne.choose_spec⟩
  let u₀ : U := ⟨Sum.inl (j₀.val,γ j₀),hγ j₀⟩
  have hz : 0 < z := by
    have hp : 0 < (2 : ℝ)*(2 : ℝ)^t*ρ := by positivity
    linarith
  let p₀ : Fin (2^t) := ⟨0,Nat.two_pow_pos t⟩
  have hVne : V.Nonempty := by
    by_contra hn
    have he : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hh := hrow p₀
    simp [he] at hh
    linarith
  let v₀ : V := ⟨hVne.choose,hVne.choose_spec⟩
  let φ : (Fin (2^t) × src.inner.Label) → V := fun a =>
    if h : (Sum.inl a : Row (I := I) src) ∈ V then ⟨Sum.inl a,h⟩ else v₀
  let ψ : src.outer.Label → U := fun j =>
    if h : j ∈ K then ⟨Sum.inl (j,γ ⟨j,h⟩),hγ ⟨j,h⟩⟩ else u₀
  let Pfull : Protocol (Fin (2^t) × src.inner.Label) src.outer.Label Bool :=
    NPCC.Protocol.pullback φ ψ P
  let Rows : Fin (2^t) → Set src.inner.Label :=
    fun p => {x | (Sum.inl (p,x) : Row (I := I) src) ∈ V}
  have hcost' : Pfull.cost ≤ d+t := by simpa [Pfull] using hcost
  have heval : ∀ p, ∀ x ∈ Rows p, ∀ j ∈ K,
      Pfull.eval (p,x) j = Sources.T src R x (src.outer.decode j p) := by
    intro p x hx j hj
    have hφ : φ (p,x) = ⟨Sum.inl (p,x),hx⟩ := by
      have hm : (Sum.inl (p,x) : Row (I := I) src) ∈ V := hx
      simp [φ,hm]
    have hψ : ψ j = ⟨Sum.inl (j,γ ⟨j,hj⟩),hγ ⟨j,hj⟩⟩ := by simp [ψ,hj]
    simp only [Pfull,NPCC.Protocol.pullback_eval,hφ,hψ]
    rw [hcompute ⟨Sum.inl (p,x),hx⟩ ⟨Sum.inl (j,γ ⟨j,hj⟩),hγ ⟨j,hj⟩⟩]
    rfl
  obtain ⟨hpref,dom,hmass,hsmall,hlarge⟩ := V38Fin2Exact.separation
    src.inner.law ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law)
    (Sources.T src R) src.outer.law.toFiniteLaw src.outer.decode
    (indexed_outer_eight_wise src hD) Rows K d ρ z ht hd hρ hscale hprofile
    (by simpa [Rows] using hrow) hgap hK Pfull hcost' heval
  have hcode (p : Fin (2^t)) (x : src.inner.Label)
      (hx : (Sum.inl (p,x) : Row (I := I) src) ∈ V) :
      NPCC.Protocol.prefixCodeRaw t Pfull (p,x) =
        NPCC.Protocol.prefixCodeRaw t P ⟨Sum.inl (p,x),hx⟩ := by
    simp only [Pfull,PrefixPullback.prefixCodeRaw_pullback]
    simp [φ,hx]
  have hfibre (p w : Fin (2^t)) :
      (fun x => x ∈ Rows p ∧ NPCC.Protocol.prefixCodeRaw t Pfull (p,x) = w) =
      (fun x => x ∈ retainedIndexedPrefixFibre src P p w) := by
    funext x
    apply propext
    constructor
    · rintro ⟨hx,hw⟩
      exact ⟨hx,by rw [← hcode p x hx]; exact hw⟩
    · rintro ⟨hx,hw⟩
      exact ⟨hx,by rw [hcode p x hx]; exact hw⟩
  refine ⟨(SourceProtocolPrefixTree.complete_pullback_iff φ ψ t P).mp hpref,
    dom,?_,?_,?_⟩
  · intro w
    simpa only [hfibre] using hmass w
  · intro w j hj
    simpa only [hfibre] using hsmall w j hj
  · intro w
    simpa only [hfibre] using hlarge w

#print axioms outer_projection_mass
#print axioms retained_outer_mass_and_representatives
#print axioms indexed_outer_eight_wise
#print axioms indexed_two_threshold_separation

end CurrentAdditive.V38IndexedTwoTag
