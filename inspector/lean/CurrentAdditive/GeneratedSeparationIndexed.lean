import CurrentAdditive.GeneratedSeparationDominant
import CurrentAdditive.IndexedProfileConditioning
import CurrentAdditive.DeterministicIndexedTemplates

/-! The exact Appendix I separation on the generated first matrix `M₁`.
Gamma's finite labels remain the column inputs, even when two labels decode
to the same head word. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Workspace.Types.Protocol
open CurrentAdditive.GeneratedSeparation

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {q₂ s t : ℕ} [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := 2^t) (q₂ := q₂) (s := s) μX μY)

theorem M₁_head_eight_wise :
    IsDWise 8 src.gamma.law.toFiniteLaw
      (fun γ i => Paper2.SourceMatrix.head (gammaWord src γ) i)
      μY.toFiniteLaw := by
  have h := (headCodeSource src).exactLaw
  intro u hu A
  have hcard : u.card ≤ 8192 := by omega
  simpa [headCodeSource, gammaWord, Paper2.SourceMatrix.head] using
    h u hcard A

/-- The protocol is the actual generated `M₁`, in raw orientation, with a
complete Alice prefix and a strict mass bijection at the final parts. -/
theorem M₁_generated_separation
    (R₀ : X → Y → Bool)
    (Rows : Fin (2^t) → Set X) (K : Set src.gamma.Label)
    (d : ℕ) (ρ z : ℝ) (ht : 1 ≤ t) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hprofile : RestrictionProfile R₀ μX.toFiniteLaw μY.toFiniteLaw ρ (d : ℤ))
    (hrow : ∀ i : Fin (2^t), z ≤ μX.toFiniteLaw.prob (· ∈ Rows i))
    (hgap : 2 * ((2^t : ℕ) : ℝ) * ρ < z)
    (hK : (18/25 : ℝ) ≤ src.gamma.law.toFiniteLaw.prob (· ∈ K))
    (P : Protocol (Fin (2^t) × X) src.gamma.Label Bool)
    (hcost : P.cost ≤ d+t)
    (heval : ∀ i : Fin (2^t), ∀ x ∈ Rows i, ∀ γ ∈ K,
      P.eval (i,x) γ = M₁ src R₀ (i,x) γ) :
    Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix t P ∧
    ∃ dom : Fin (2^t) ≃ Fin (2^t),
      ∀ j, z - (2^t-1 : ℕ) * (2*ρ) <
          partMass μX.toFiniteLaw P Rows j (dom j) ∧
        (∀ i, i ≠ dom j → partMass μX.toFiniteLaw P Rows j i < 2*ρ) := by
  apply generated_source_separation μX μY R₀ src.gamma.law.toFiniteLaw
    (fun γ i => Paper2.SourceMatrix.head (gammaWord src γ) i)
    (M₁_head_eight_wise src) Rows K d ρ z ht hd hρ hprofile hrow hgap hK
    P hcost
  intro i x hx γ hγ
  simpa only [M₁_entry] using heval i x hx γ hγ

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.M₁_generated_separation

private theorem nonempty_of_positive_probability {A : Type*} [Fintype A]
    (law : FiniteLaw A) (U : Set A)
    (h : 0 < law.prob (· ∈ U)) : U.Nonempty := by
  by_contra hn
  have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  subst U
  simp at h

/-- The same conclusion for a protocol whose input types are exactly the
retained row and indexed-column subtypes. `φ` selects a genuine retained row
outside the rectangle and is the identity on every retained row; hence the
displayed prefix masses are those of the given subtype protocol itself. -/
theorem M₁_retained_protocol_separation
    (R₀ : X → Y → Bool)
    (U : Set (Fin (2^t) × X)) (K : Set src.gamma.Label)
    (d : ℕ) (ρ z : ℝ) (ht : 1 ≤ t) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hprofile : RestrictionProfile R₀ μX.toFiniteLaw μY.toFiniteLaw ρ (d : ℤ))
    (hrow : ∀ i : Fin (2^t), z ≤ μX.toFiniteLaw.prob (fun x => (i,x) ∈ U))
    (hgap : 2 * ((2^t : ℕ) : ℝ) * ρ < z)
    (hK : (18/25 : ℝ) ≤ src.gamma.law.toFiniteLaw.prob (· ∈ K))
    (P : Protocol U K Bool)
    (hcost : P.cost ≤ d+t)
    (hcompute : P.Computes (fun a γ => M₁ src R₀ a.1 γ.1)) :
    ∃ φ : (Fin (2^t) × X) → U,
      (∀ a (ha : a ∈ U), φ a = ⟨a,ha⟩) ∧
      Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix t P ∧
      ∃ RU : Finset U, (∀ a, a ∈ RU) ∧
        Paper2.SourceProtocolPrefixTree.EveryPrefixBranchActive RU t P ∧
      ∃ dom : Fin (2^t) ≃ Fin (2^t),
        ∀ j, z - (2^t-1 : ℕ) * (2*ρ) <
            μX.toFiniteLaw.prob (fun x => (dom j,x) ∈ U ∧
              NPCC.Protocol.prefixCodeRaw t P (φ (dom j,x)) = j) ∧
          (∀ i, i ≠ dom j →
            μX.toFiniteLaw.prob (fun x => (i,x) ∈ U ∧
              NPCC.Protocol.prefixCodeRaw t P (φ (i,x)) = j) < 2*ρ) := by
  classical
  let i₀ : Fin (2^t) := ⟨0, Nat.two_pow_pos t⟩
  have hz : 0 < z := by
    have hp : 0 < (2 : ℝ) * ((2^t : ℕ) : ℝ) * ρ := by positivity
    linarith
  have hU : U.Nonempty := by
    have hpos : 0 < μX.toFiniteLaw.prob (fun x => (i₀,x) ∈ U) :=
      lt_of_lt_of_le hz (hrow i₀)
    obtain ⟨x,hx⟩ := nonempty_of_positive_probability μX.toFiniteLaw
      {x | (i₀,x) ∈ U} hpos
    exact ⟨(i₀,x),hx⟩
  have hKne : K.Nonempty :=
    nonempty_of_positive_probability src.gamma.law.toFiniteLaw K
      (lt_of_lt_of_le (by norm_num) hK)
  let a₀ : U := ⟨hU.choose,hU.choose_spec⟩
  let γ₀ : K := ⟨hKne.choose,hKne.choose_spec⟩
  let φ : (Fin (2^t) × X) → U :=
    fun a => if h : a ∈ U then ⟨a,h⟩ else a₀
  let ψ : src.gamma.Label → K :=
    fun γ => if h : γ ∈ K then ⟨γ,h⟩ else γ₀
  let Pfull : Protocol (Fin (2^t) × X) src.gamma.Label Bool :=
    NPCC.Protocol.pullback φ ψ P
  let Rows : Fin (2^t) → Set X := fun i => {x | (i,x) ∈ U}
  have hrow' : ∀ i : Fin (2^t), z ≤ μX.toFiniteLaw.prob (· ∈ Rows i) := hrow
  have hcost' : Pfull.cost ≤ d+t := by simpa [Pfull] using hcost
  have heval : ∀ i : Fin (2^t), ∀ x ∈ Rows i, ∀ γ ∈ K,
      Pfull.eval (i,x) γ = M₁ src R₀ (i,x) γ := by
    intro i x hx γ hγ
    have hxU : (i,x) ∈ U := hx
    have hφ : φ (i,x) = ⟨(i,x),hxU⟩ := by simp [φ,hxU]
    have hψ : ψ γ = ⟨γ,hγ⟩ := by simp [ψ,hγ]
    simp only [Pfull, NPCC.Protocol.pullback_eval, hφ, hψ]
    exact hcompute ⟨(i,x),hx⟩ ⟨γ,hγ⟩
  obtain ⟨hpfull, dom, hdom⟩ := M₁_generated_separation src R₀ Rows K
    d ρ z ht hd hρ hprofile hrow' hgap hK Pfull hcost' heval
  have hp : Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix t P :=
    (Paper2.SourceProtocolPrefixTree.complete_pullback_iff φ ψ t P).mp hpfull
  have hmass (j i : Fin (2^t)) :
      partMass μX.toFiniteLaw Pfull Rows j i =
      μX.toFiniteLaw.prob (fun x => (i,x) ∈ U ∧
        NPCC.Protocol.prefixCodeRaw t P (φ (i,x)) = j) := by
    unfold partMass
    congr 1
    funext x
    simp only [Rows, Set.mem_setOf_eq]
    rw [show NPCC.Protocol.prefixCodeRaw t Pfull (i,x) =
      NPCC.Protocol.prefixCodeRaw t P (φ (i,x)) from
      Paper2.PrefixPullback.prefixCodeRaw_pullback φ ψ t P (i,x)]
  have hpositive : 0 < z - (2^t-1 : ℕ) * (2*ρ) := by
    have hnat : 2^t-1 ≤ 2^t := Nat.sub_le _ _
    have hreal : (((2^t-1 : ℕ) : ℝ)) ≤ (((2^t : ℕ) : ℝ)) := by
      exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_right hreal (by linarith : 0 ≤ 2*ρ)
    nlinarith
  have hall : ∀ j : Fin (2^t),
      ∃ a ∈ (Finset.univ : Finset U),
        NPCC.Protocol.prefixCodeRaw t P a = j := by
    intro j
    have hh := (hdom j).1
    rw [hmass] at hh
    have hpos : 0 < μX.toFiniteLaw.prob (fun x =>
        (dom j,x) ∈ U ∧
          NPCC.Protocol.prefixCodeRaw t P (φ (dom j,x)) = j) := by
      linarith
    obtain ⟨x,hx⟩ := nonempty_of_positive_probability μX.toFiniteLaw
      {x | (dom j,x) ∈ U ∧
        NPCC.Protocol.prefixCodeRaw t P (φ (dom j,x)) = j} hpos
    exact ⟨φ (dom j,x), Finset.mem_univ _, hx.2⟩
  have hactive :=
    Paper2.SourceProtocolPrefixTree.active_branches_of_complete_and_all_codes
      (Finset.univ : Finset U) t P hp hall
  refine ⟨φ, ?_, hp, Finset.univ, (fun a => Finset.mem_univ a), hactive,
    dom, ?_⟩
  · intro a ha
    simp [φ,ha]
  · intro j
    have hh := hdom j
    rw [hmass] at hh
    refine ⟨hh.1, ?_⟩
    intro i hi
    simpa only [hmass] using hh.2 i hi

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.M₁_retained_protocol_separation

/-- The generated matrix `A` is the literal transpose of `M₁`. Its source
separation is read in raw orientation by swapping the given protocol, so the
first `t` messages are Bob messages in `A`'s displayed orientation. -/
theorem A_retained_protocol_separation
    (R₀ : X → Y → Bool)
    (U : Set (Fin (2^t) × X)) (K : Set src.gamma.Label)
    (d : ℕ) (ρ z : ℝ) (ht : 1 ≤ t) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hprofile : RestrictionProfile R₀ μX.toFiniteLaw μY.toFiniteLaw ρ (d : ℤ))
    (hrow : ∀ i : Fin (2^t), z ≤ μX.toFiniteLaw.prob (fun x => (i,x) ∈ U))
    (hgap : 2 * ((2^t : ℕ) : ℝ) * ρ < z)
    (hK : (18/25 : ℝ) ≤ src.gamma.law.toFiniteLaw.prob (· ∈ K))
    (P : Protocol K U Bool)
    (hcost : P.cost ≤ d+t)
    (hcompute : P.Computes (fun γ a => A src R₀ γ.1 a.1)) :
    ∃ φ : (Fin (2^t) × X) → U,
      (∀ a (ha : a ∈ U), φ a = ⟨a,ha⟩) ∧
      Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix t (NPCC.Protocol.swap P) ∧
      ∃ RU : Finset U, (∀ a, a ∈ RU) ∧
        Paper2.SourceProtocolPrefixTree.EveryPrefixBranchActive RU t (NPCC.Protocol.swap P) ∧
      ∃ dom : Fin (2^t) ≃ Fin (2^t),
        ∀ j, z - (2^t-1 : ℕ) * (2*ρ) <
            μX.toFiniteLaw.prob (fun x => (dom j,x) ∈ U ∧
              NPCC.Protocol.prefixCodeRaw t (NPCC.Protocol.swap P) (φ (dom j,x)) = j) ∧
          (∀ i, i ≠ dom j →
            μX.toFiniteLaw.prob (fun x => (i,x) ∈ U ∧
              NPCC.Protocol.prefixCodeRaw t (NPCC.Protocol.swap P) (φ (i,x)) = j) < 2*ρ) := by
  apply M₁_retained_protocol_separation src R₀ U K d ρ z ht hd hρ
    hprofile hrow hgap hK (NPCC.Protocol.swap P)
  · simpa using hcost
  · intro a γ
    simpa only [NPCC.Protocol.eval_swap, A] using hcompute γ a

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.A_retained_protocol_separation

end CurrentAdditive.DeterministicIndexedMatrix.Sources
