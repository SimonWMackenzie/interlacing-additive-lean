import CurrentAdditive.GeneratedTwoStreamObstruction
import Paper2.TwoStreamOriginalInputs

set_option maxHeartbeats 5000000

/-! Appendix I `det:two-stream` on original generated input labels. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.TwoStreamRawRows Paper2.TwoStreamOriginalInputs
open Paper2.TwoStreamInitial Workspace.Types.Protocol

variable {X Y Rw F E : Type*}
  [Fintype X] [Fintype Y] [Fintype Rw] [Fintype F] [Fintype E]
  [DecidableEq E] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- A short protocol on the original retained rows and columns is
impossible. The distinguished paired event and each ordinary bin are
constructed from the original inputs; no iid law is asserted for either
complete decoded source vector. -/
theorem two_stream_image_short_protocol_impossible
    (R₀ : X → Y → Bool)
    (M : Rw → ((src.outer.Label × src.gamma.Label) ⊕ F) → Bool)
    (H ell a : ℕ) (hH : 2 ≤ H) (hq : q₂ = 2^ell) (hs : s = 2^a)
    (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hA : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (hT : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (κE : FiniteLaw E)
    (bin : Rw → Fin s) (selector : Rw → src.inner.Label)
    (ψ : F → J src)
    (hordinary : ∀ row c, M row (.inl c) =
      T src R₀ (selector row) (src.outer.decode c.1 (bin row)))
    (ι : E → Rw) (ζ : E → src.inner.Label × src.inner.Label)
    (hζ : κE.PushesTo
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw) ζ)
    (star : Fin s) (P0 : Finset E) (R : Set Rw)
    (O : Set (src.outer.Label × src.gamma.Label)) (G : Set F)
    (hι : ∀ e ∈ P0, ι e ∈ R)
    (hstar : ∀ e ∈ P0,
      bin (ι e) = star ∧ selector (ι e) = (ζ e).1)
    (hforeign : ∀ e ∈ P0, ∀ f,
      M (ι e) (.inr f) = T src R₀ (ζ e).2 (ψ f))
    (hpair : 2*s*x ≤ src.inner.law.toFiniteLaw.prob
      (· ∈ (fun e => (ζ e).1) '' (P0 : Set E)))
    (hrow : ∀ i ≠ star, 2*s*x ≤ src.inner.law.toFiniteLaw.prob
      (fun z => ∃ r ∈ R, bin r = i ∧ selector r = z))
    (hretain : ∀ P' : Finset E, P' ⊆ P0 →
      SourceSupportStep.mass κE (P0 \ P') < 2*s*x →
      (49/64 : ℝ) ≤
        (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob
          (· ∈ ζ '' (P' : Set E)))
    (ε δ : ℝ)
    (hO : 1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob (· ∈ O))
    (hF : δ ≤
      (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
        (· ∈ ψ '' G)) (hδ : δ ≤ 1)
    (hslack : 2*q₂*x + 5*ε + 2/q₂ ≤ δ)
    (hsmall : 2*s*x ≤ 1/8) (hpairsmall : 2*q₂*x ≤ 1/8)
    (P : Protocol R (retainedColumns O G) Bool)
    (hP : P.Computes (fun r c => M r.val c.val))
    (hcost : P.cost ≤ H+ell+a) : False := by
  classical
  let μS := src.inner.law.toFiniteLaw
  letI : Nonempty E := κE.nonempty
  letI : Nonempty Rw := ⟨ι (Classical.choice inferInstance)⟩
  let default : src.inner.Label := Classical.choice μS.nonempty
  let σ := firstSelector ζ selector default
  let input := rawInput ι
  let supports := initialSupport star P0 (binRows R bin)
  have hspos : 0 < s := by rw [hs]; positivity
  have htpos : (0 : ℝ) < 2*s*x := by positivity
  have hP0 : P0.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hz : src.inner.law.toFiniteLaw.prob
        (· ∈ (fun e => (ζ e).1) '' (P0 : Set E)) = 0 := by simp [he]
    rw [hz] at hpair
    linarith
  obtain ⟨e, he⟩ := hP0
  let row0 : R := ⟨ι e, hι e he⟩
  have hdense := (ordinary_density (ordinaryLaw src).toFiniteLaw O q₂
    (NeZero.pos q₂) x ε δ hx.le hO hδ hslack).2.2
  obtain ⟨c, hc⟩ := columns_nonempty_of_mass
    (ordinaryLaw src).toFiniteLaw O G (by linarith)
  let col0 : retainedColumns O G := ⟨c, hc⟩
  let init := initial R O G row0 col0 P star supports
  have hbin' : ∀ i, ∀ w ∈ supports i, bin (input w) = i :=
    supports_bin R bin ι star P0 (fun e he => (hstar e he).1)
  have hreach' : ∀ i, ∀ w ∈ supports i, input w ∈ R :=
    supports_retained R bin ι star P0 hι
  have hsel' : ∀ i, ∀ w ∈ supports i,
      σ w = selector (input w) :=
    supports_selector R bin ι ζ selector default star P0
      (fun e he => (hstar e he).2)
  have hmass' : ∀ i, SourceSupportSchedule.floor s x 0 ≤
      ProjectedSupportStep.mass μS σ (supports i) := by
    simpa only [SourceSupportSchedule.floor_zero] using
      supports_floor μS R bin ζ selector default star P0 (2*s*x)
        hpair hrow
  have hretain' := retention_transfer κE μS ζ selector default P0
    (2*s*x) hretain
  have hforeign' : ∀ w ∈ supports star, ∀ f,
      M (input w) (.inr f) =
        T src R₀ (jointSelector ζ selector default w).2 (ψ f) :=
    supports_foreign R bin ι ζ selector default star P0
      (fun r f => M r (.inr f)) (fun z f => T src R₀ z (ψ f)) hforeign
  have hpush : (pairedLaw (Rw := Rw) κE).PushesTo
      (μS.prod μS) (jointSelector ζ selector default) :=
    pairedLaw_pushes κE μS ζ selector default hζ
  apply no_short_generated_two_stream src R₀ M
    H ell a hH hq hs x hx hD hA hT (pairedLaw κE)
    bin selector ψ hordinary (jointSelector ζ selector default)
    hpush σ rfl input star init
    rfl rfl (fun i _ => hbin' i) (fun i _ => hsel' i)
    (fun i _ => hreach' i) (fun i _ => hmass' i)
    O G ?_ hforeign' ?_ ε δ hO hF hδ hslack ?_
    hpairsmall ?_
  · exact ambientProtocol_computesOn M R O G row0 col0 P hP
  · simpa only [init, initial, supports, initialSupport_star,
      SourceSupportSchedule.floor_zero] using hretain'
  · simpa only [SourceSupportSchedule.floor_zero] using hsmall
  · simpa only [init, initial, ambientProtocol_cost] using hcost

/-- Cost lower bound for the original retained generated two-stream
matrix, with all protocol and frontier states constructed internally. -/
theorem generated_two_stream_image_restriction_lower
    (R₀ : X → Y → Bool)
    (M : Rw → ((src.outer.Label × src.gamma.Label) ⊕ F) → Bool)
    (H ell a : ℕ) (hH : 2 ≤ H) (hq : q₂ = 2^ell) (hs : s = 2^a)
    (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hA : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (hT : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (κE : FiniteLaw E)
    (bin : Rw → Fin s) (selector : Rw → src.inner.Label)
    (ψ : F → J src)
    (hordinary : ∀ row c, M row (.inl c) =
      T src R₀ (selector row) (src.outer.decode c.1 (bin row)))
    (ι : E → Rw) (ζ : E → src.inner.Label × src.inner.Label)
    (hζ : κE.PushesTo
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw) ζ)
    (star : Fin s) (P0 : Finset E) (R : Set Rw)
    (O : Set (src.outer.Label × src.gamma.Label)) (G : Set F)
    (hι : ∀ e ∈ P0, ι e ∈ R)
    (hstar : ∀ e ∈ P0,
      bin (ι e) = star ∧ selector (ι e) = (ζ e).1)
    (hforeign : ∀ e ∈ P0, ∀ f,
      M (ι e) (.inr f) = T src R₀ (ζ e).2 (ψ f))
    (hpair : 2*s*x ≤ src.inner.law.toFiniteLaw.prob
      (· ∈ (fun e => (ζ e).1) '' (P0 : Set E)))
    (hrow : ∀ i ≠ star, 2*s*x ≤ src.inner.law.toFiniteLaw.prob
      (fun z => ∃ r ∈ R, bin r = i ∧ selector r = z))
    (hretain : ∀ P' : Finset E, P' ⊆ P0 →
      SourceSupportStep.mass κE (P0 \ P') < 2*s*x →
      (49/64 : ℝ) ≤
        (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob
          (· ∈ ζ '' (P' : Set E)))
    (ε δ : ℝ)
    (hO : 1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob (· ∈ O))
    (hF : δ ≤
      (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
        (· ∈ ψ '' G)) (hδ : δ ≤ 1)
    (hslack : 2*q₂*x + 5*ε + 2/q₂ ≤ δ)
    (hsmall : 2*s*x ≤ 1/8) (hpairsmall : 2*q₂*x ≤ 1/8) :
    H+ell+a+1 ≤ Compression.restrictionD M R (retainedColumns O G) := by
  classical
  by_contra hn
  obtain ⟨P, hcost, hP⟩ := Nat.sInf_mem
    (Workspace.UpperBound.AchievableCosts_nonempty
      (fun (r : R) (c : retainedColumns O G) => M r.val c.val))
  apply two_stream_image_short_protocol_impossible src R₀ M
    H ell a hH hq hs x hx hD hA hT κE bin selector ψ
    hordinary ι ζ hζ star P0 R O G hι hstar hforeign
    hpair hrow hretain ε δ hO hF hδ hslack hsmall hpairsmall P hP
  change P.cost = Compression.restrictionD M R (retainedColumns O G) at hcost
  omega

#print axioms two_stream_image_short_protocol_impossible
#print axioms generated_two_stream_image_restriction_lower

end CurrentAdditive.DeterministicIndexedMatrix.Sources
