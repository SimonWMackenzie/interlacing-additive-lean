import CurrentAdditive.GeneratedOwnerTwoStream
import CurrentAdditive.IndexedProfileRung

/-! Owner-to-owner W obstruction with the actual generated A/T profiles. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
  {w : ℕ} (streams : InternalStreams src μI w)

/-- The profile inputs used by the literal W consumer are produced by
the same generated source and public schedule. Only the preceding
pair-bin averaging and owner support estimates remain hypotheses. -/
theorem owner_to_owner_W_lower_from_schedule
    (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (i j : Fin w) (p r : Fin s)
    (U : Set (InternalLabel src streams))
    (Vrows : Set (Fin w × Column src))
    (d a b : ℕ) (ρ x τ : ℝ)
    (hd : 3 ≤ d) (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hρ : 0 < ρ) (hx : 0 < x) (hx1 : x ≤ 1) (hτ : 0 < τ)
    (hDbase : D R₀ = d)
    (hp : RestrictionProfile R₀ μX.toFiniteLaw μY.toFiniteLaw ρ (d : ℤ))
    (hwidthA : q₁ ≤ 2^a) (hwidthT : q₂ ≤ 2^b)
    (hscaleA : ∀ j : Fin 3, (2 : ℝ)^(a-j.val) * ρ < 1)
    (hscaleT : ∀ j : Fin 3, (2 : ℝ)^(b-j.val) * x < 1)
    (hscaleN : ∀ j : Fin 3, (2 : ℝ)^(a-j.val) * x < 1)
    (hbudgetA : ∀ j : Fin 3,
      (((2^((a-j.val)-1)+1) +
        CurrentAdditive.conditioningExceptionCountR 1024 x τ : ℕ) : ℝ) *
        (1-(2 : ℝ)^(a-j.val)*ρ) ≤
          (q₁ : ℝ) *
            ((3/5 : ℝ)*(1/2 : ℝ)^j.val-(2 : ℝ)^(a-j.val)*ρ))
    (hbudgetT : ∀ j : Fin 3,
      (((2^((b-j.val)-1)+1) +
        CurrentAdditive.conditioningExceptionCountR 1024 x τ : ℕ) : ℝ) *
        (1-(2 : ℝ)^(b-j.val)*x) ≤
          (q₂ : ℝ) *
            ((3/5 : ℝ)*(1/2 : ℝ)^j.val-(2 : ℝ)^(b-j.val)*x))
    (hbudgetN : ∀ j : Fin 3,
      (((2^((a-j.val)-1)+1) +
        CurrentAdditive.conditioningExceptionCountR 1024 x τ : ℕ) : ℝ) *
        (1-(2 : ℝ)^(a-j.val)*x) ≤
          (s : ℝ) *
            (((((3/5 : ℝ)*(1/2 : ℝ)^j.val)-(1-255/256))/(255/256)) -
              (2 : ℝ)^(a-j.val)*x))
    (hq : q₂ = 2^b) (hs : s = 2^a)
    (pairMass ε δ : ℝ)
    (hPair : pairMass ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob
        (· ∈ ownerPairImage src streams U i j p r))
    (hMargin : 49/64+2*s*x < pairMass)
    (hOther : ∀ b' ≠ p, 2*s*x ≤ src.inner.law.toFiniteLaw.prob
      (fun z => ∃ t ∈ U,
        streams.metadataStream.decode t.1 i = .inl b' ∧
        streams.selectorStream.decode t.2.2 i = z))
    (hO : 1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob
      (fun o => (i, .ordinary o) ∈ Vrows))
    (hF : δ ≤
      (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
        (fun f => (j, .diagonal f) ∈ Vrows))
    (hδ : δ ≤ 1)
    (hslack : 2*q₂*x+5*ε+2/q₂ ≤ δ)
    (hsmall : 2*s*x ≤ 1/8) (hpairsmall : 2*q₂*x ≤ 1/8) :
    d+a+b+a+1 ≤ Compression.restrictionD
      (W src streams R₀ activity ξ₀) U Vrows := by
  have hprofiles := generated_profiles_from_schedule src μI R₀ activity ξ₀
    d a b ρ x τ hd ha hb hρ hx hx1 hτ hDbase hp
    hwidthA hwidthT hscaleA hscaleT hscaleN
    hbudgetA hbudgetT hbudgetN
  have hA := hprofiles.2.1
  have hT := hprofiles.2.2.2.1
  exact owner_to_owner_W_lower_fixed_bins src streams R₀ activity ξ₀
    i j p r U Vrows (d+a) b a (by omega) hq hs x hx (by norm_num)
    hA hT pairMass ε δ hPair hMargin hOther hO hF hδ hslack
    hsmall hpairsmall

#print axioms owner_to_owner_W_lower_from_schedule

end CurrentAdditive.DeterministicIndexedMatrix.Sources
