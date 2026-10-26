import CurrentAdditive.GeneratedSeparationIndexed
import CurrentAdditive.DeterministicIndexedMatrix

/-! Actual indexed `N` template-row and fixed-tail specialization of the
source separation. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Workspace.Types.Protocol
open CurrentAdditive.GeneratedSeparation

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ t : ℕ} [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂)
    (s := 2^t) μX μY)

theorem outer_eight_wise :
    IsDWise 8 src.outer.law.toFiniteLaw src.outer.decode
      (((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw) := by
  intro J hJ E
  exact src.outer.exactLaw J (by omega) E

omit [Fintype I] in
theorem fixedTail_template_entry
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin (2^t)))
    (ξ₀ : Paper2.SourceMatrix.Tail (2^t) Y)
    (p : Fin (2^t)) (z : src.inner.Label) (js : src.outer.Label) :
    B src R₀ activity ξ₀ (.inl (p,z)) (.fixedTail js) =
      T src R₀ z (src.outer.decode js p) := by
  rfl

private theorem positive_mass_nonempty {A : Type*} [Fintype A]
    (law : FiniteLaw A) (U : Set A)
    (h : 0 < law.prob (· ∈ U)) : U.Nonempty := by
  by_contra hn
  have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  subst U
  simp at h

/-- On the actual generated matrix's retained template rows and fixed-tail
columns, the first `t` messages of any depth-`d+t` raw protocol are Alice's.
The dominant mass is measured on the original inner source labels, and the
part label is evaluated by the original protocol on a surviving row input. -/
theorem B_template_fixedTail_separation
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin (2^t)))
    (ξ₀ : Paper2.SourceMatrix.Tail (2^t) Y)
    (V : Set (Row (I := I) src)) (U : Set (Column src))
    (d : ℕ) (ρ z : ℝ) (ht : 1 ≤ t) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hprofile : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw)
      ρ (d : ℤ))
    (hrow : ∀ p : Fin (2^t), z ≤ src.inner.law.toFiniteLaw.prob
      (fun z => (Sum.inl (p,z) : Row (I := I) src) ∈ V))
    (hgap : 2 * ((2^t : ℕ) : ℝ) * ρ < z)
    (hK : (18/25 : ℝ) ≤ src.outer.law.toFiniteLaw.prob
      (fun js => (Column.fixedTail js : Column src) ∈ U))
    (P : Protocol V U Bool)
    (hcost : P.cost ≤ d+t)
    (hcompute : P.Computes (fun a c => B src R₀ activity ξ₀ a.1 c.1)) :
    ∃ Φ : (Fin (2^t) × src.inner.Label) → V,
      (∀ p z (h : (Sum.inl (p,z) : Row (I := I) src) ∈ V),
        Φ (p,z) = ⟨.inl (p,z),h⟩) ∧
      Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix t P ∧
      ∃ RV : Finset V, (∀ a, a ∈ RV) ∧
        Paper2.SourceProtocolPrefixTree.EveryPrefixBranchActive RV t P ∧
      ∃ dom : Fin (2^t) ≃ Fin (2^t),
        ∀ j, z - (2^t-1 : ℕ) * (2*ρ) <
            src.inner.law.toFiniteLaw.prob (fun z =>
              (Sum.inl (dom j,z) : Row (I := I) src) ∈ V ∧
                NPCC.Protocol.prefixCodeRaw t P (Φ (dom j,z)) = j) ∧
          (∀ i, i ≠ dom j →
            src.inner.law.toFiniteLaw.prob (fun z =>
              (Sum.inl (i,z) : Row (I := I) src) ∈ V ∧
                NPCC.Protocol.prefixCodeRaw t P (Φ (i,z)) = j) < 2*ρ) := by
  classical
  let Vt : Set (Fin (2^t) × src.inner.Label) :=
    {a | (Sum.inl a : Row (I := I) src) ∈ V}
  let Uf : Set src.outer.Label :=
    {js | (Column.fixedTail js : Column src) ∈ U}
  let Rows : Fin (2^t) → Set src.inner.Label := fun p =>
    {z | (Sum.inl (p,z) : Row (I := I) src) ∈ V}
  have hz : 0 < z := by
    have hp : 0 < (2 : ℝ) * ((2^t : ℕ) : ℝ) * ρ := by positivity
    linarith
  let p₀ : Fin (2^t) := ⟨0, Nat.two_pow_pos t⟩
  have hVt : Vt.Nonempty := by
    have hpos : 0 < src.inner.law.toFiniteLaw.prob (· ∈ Rows p₀) :=
      lt_of_lt_of_le hz (hrow p₀)
    obtain ⟨z,hz⟩ := positive_mass_nonempty src.inner.law.toFiniteLaw
      (Rows p₀) hpos
    exact ⟨(p₀,z),hz⟩
  have hUf : Uf.Nonempty :=
    positive_mass_nonempty src.outer.law.toFiniteLaw Uf
      (lt_of_lt_of_le (by norm_num) hK)
  let rowEmbed : Vt → V := fun a => ⟨.inl a.1,a.property⟩
  let colEmbed : Uf → U := fun js => ⟨.fixedTail js.1,js.property⟩
  let Pt : Protocol Vt Uf Bool := NPCC.Protocol.pullback rowEmbed colEmbed P
  let a₀ : Vt := ⟨hVt.choose,hVt.choose_spec⟩
  let js₀ : Uf := ⟨hUf.choose,hUf.choose_spec⟩
  let φ : (Fin (2^t) × src.inner.Label) → Vt :=
    fun a => if h : a ∈ Vt then ⟨a,h⟩ else a₀
  let ψ : src.outer.Label → Uf :=
    fun js => if h : js ∈ Uf then ⟨js,h⟩ else js₀
  let Pfull : Protocol (Fin (2^t) × src.inner.Label) src.outer.Label Bool :=
    NPCC.Protocol.pullback φ ψ Pt
  have hcost' : Pfull.cost ≤ d+t := by simpa [Pfull,Pt] using hcost
  have heval : ∀ p : Fin (2^t), ∀ z ∈ Rows p, ∀ js ∈ Uf,
      Pfull.eval (p,z) js = T src R₀ z (src.outer.decode js p) := by
    intro p z hz js hjs
    have ha : (p,z) ∈ Vt := hz
    have hφ : φ (p,z) = ⟨(p,z),ha⟩ := by simp [φ,ha]
    have hψ : ψ js = ⟨js,hjs⟩ := by simp [ψ,hjs]
    simp only [Pfull,Pt, NPCC.Protocol.pullback_eval,hφ,hψ]
    rw [hcompute (rowEmbed ⟨(p,z),ha⟩) (colEmbed ⟨js,hjs⟩)]
    exact fixedTail_template_entry src R₀ activity ξ₀ p z js
  obtain ⟨hpfull, dom, hdom⟩ := generated_source_separation
    src.inner.law ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law)
    (T src R₀) src.outer.law.toFiniteLaw src.outer.decode
    (outer_eight_wise src) Rows Uf d ρ z ht hd hρ hprofile
    (by simpa [Rows] using hrow) hgap (by simpa [Uf] using hK)
    Pfull hcost' heval
  have hpt : Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix t Pt :=
    (Paper2.SourceProtocolPrefixTree.complete_pullback_iff φ ψ t Pt).mp hpfull
  have hp : Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix t P :=
    (Paper2.SourceProtocolPrefixTree.complete_pullback_iff rowEmbed colEmbed t P).mp hpt
  let Φ : (Fin (2^t) × src.inner.Label) → V := rowEmbed ∘ φ
  have hmass (j i : Fin (2^t)) :
      partMass src.inner.law.toFiniteLaw Pfull Rows j i =
      src.inner.law.toFiniteLaw.prob (fun z =>
        (Sum.inl (i,z) : Row (I := I) src) ∈ V ∧
          NPCC.Protocol.prefixCodeRaw t P (Φ (i,z)) = j) := by
    unfold partMass
    congr 1
    funext z
    simp only [Rows, Set.mem_setOf_eq]
    rw [show NPCC.Protocol.prefixCodeRaw t Pfull (i,z) =
      NPCC.Protocol.prefixCodeRaw t Pt (φ (i,z)) from
      Paper2.PrefixPullback.prefixCodeRaw_pullback φ ψ t Pt (i,z)]
    rw [Paper2.PrefixPullback.prefixCodeRaw_pullback rowEmbed colEmbed t P (φ (i,z))]
    rfl
  have hpositive : 0 < z - (2^t-1 : ℕ) * (2*ρ) := by
    have hnat : 2^t-1 ≤ 2^t := Nat.sub_le _ _
    have hreal : (((2^t-1 : ℕ) : ℝ)) ≤ (((2^t : ℕ) : ℝ)) := by
      exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_right hreal (by linarith : 0 ≤ 2*ρ)
    nlinarith
  have hall : ∀ j : Fin (2^t),
      ∃ a ∈ (Finset.univ : Finset V),
        NPCC.Protocol.prefixCodeRaw t P a = j := by
    intro j
    have hh := (hdom j).1
    rw [hmass] at hh
    have hpos : 0 < src.inner.law.toFiniteLaw.prob (fun z =>
        (Sum.inl (dom j,z) : Row (I := I) src) ∈ V ∧
          NPCC.Protocol.prefixCodeRaw t P (Φ (dom j,z)) = j) := by
      linarith
    obtain ⟨z,hz⟩ := positive_mass_nonempty src.inner.law.toFiniteLaw
      {z | (Sum.inl (dom j,z) : Row (I := I) src) ∈ V ∧
        NPCC.Protocol.prefixCodeRaw t P (Φ (dom j,z)) = j} hpos
    exact ⟨Φ (dom j,z), Finset.mem_univ _, hz.2⟩
  have hactive :=
    Paper2.SourceProtocolPrefixTree.active_branches_of_complete_and_all_codes
      (Finset.univ : Finset V) t P hp hall
  refine ⟨Φ, ?_, hp, Finset.univ, (fun a => Finset.mem_univ a), hactive,
    dom, ?_⟩
  · intro p z h
    have hv : (p,z) ∈ Vt := h
    simp [Φ,φ,hv,rowEmbed]
  · intro j
    have hh := hdom j
    rw [hmass] at hh
    refine ⟨hh.1, ?_⟩
    intro i hi
    simpa only [hmass] using hh.2 i hi

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.B_template_fixedTail_separation

end CurrentAdditive.DeterministicIndexedMatrix.Sources
