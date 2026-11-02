import CurrentAdditive.V39IndexedProfiles
import CurrentAdditive.V39GeneratedProfileGuards
import CurrentAdditive.V39IndexedOwnerObstructions

/-! Selected v39 `res:alignment`, the profile branch only. The actual
two-family column law is used, and conditioning is on the whole retained
tuple event before any reference blocks are chosen. -/

namespace CurrentAdditive.V39IndexedInternalProfile

open Paper2 Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open scoped BigOperators

theorem exception_count_eight (θ : ℝ) (hθ : 0 < θ) :
    8 ≤ V38Moments.exceptionCount θ 1 := by
  have hε : 0 < V38Moments.epsilon θ 1 := by
    unfold V38Moments.epsilon
    exact lt_min (by norm_num) (mul_pos (by positivity) (Real.rpow_pos_of_pos hθ _))
  have hi : 0 < (2 : ℝ)^(20 : ℕ)*(V38Moments.epsilon θ 1)^(-(2 : ℝ))*
      θ^(-(1 : ℝ)/512) := by positivity
  have hc := Nat.ceil_pos.mpr hi
  unfold V38Moments.exceptionCount
  omega

/-- The source's exception budget itself forces enough copies for the
integer block selection; no larger public width premise is added. -/
theorem width_of_exception_budget (w : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (he : V38Moments.exceptionCount θ 1 ≤ w/128) : 256 ≤ w := by
  have hcount := exception_count_eight θ hθ
  omega

theorem internal_population_budgets (w a : ℕ) (x θ : ℝ)
    (ha : 2 ≤ a) (hw : w=2^a) (hx : 0 < x) (hθ : 0 < θ)
    (he : V38Moments.exceptionCount θ 1 ≤ w/128)
    (hwx : (w : ℝ)*x < 1/256) :
    ∀ j : Fin 2,
      (((2^((a-j.val)-1)+1)+V38Moments.exceptionCount θ 1 : ℕ) : ℝ)*
        (1-(2 : ℝ)^(a-j.val)*x) ≤
        (w : ℝ)*(SourceProfilesReference.templateThreshold ((3/5 : ℝ)*(1/2 : ℝ)^j.val)-
          (2 : ℝ)^(a-j.val)*x) := by
  have hwidth : 256 ≤ w := width_of_exception_budget w θ hθ he
  have hwR : (w : ℝ)=(2 : ℝ)^a := by rw [hw,Nat.cast_pow,Nat.cast_ofNat]
  have hpos : (0 : ℝ) < w := by rw [hwR]; positivity
  have heMul : V38Moments.exceptionCount θ 1*128 ≤ w :=
    (Nat.le_div_iff_mul_le (by norm_num)).mp he
  have heR : (V38Moments.exceptionCount θ 1 : ℝ) ≤ (w : ℝ)/128 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<128)).2
    exact_mod_cast heMul
  have hhalf : (2 : ℝ)^(a-1)=(w : ℝ)/2 := by
    rw [hwR]
    have hsuc : a=(a-1)+1 := by omega
    conv_rhs => rw [hsuc,pow_succ]
    ring
  intro j
  apply V39GeneratedProfileGuards.budget_of_population w (a-j.val) w
    (V38Moments.exceptionCount θ 1) x
    (SourceProfilesReference.templateThreshold ((3/5 : ℝ)*(1/2 : ℝ)^j.val))
    (by have hj:=j.isLt; omega) hwidth
    (by rw [hwR]; exact V39FullScheduleGuards.half_power_bound a (by omega) j)
    heR hx.le
  fin_cases j
  · norm_num only [Fin.val_zero,Nat.sub_zero,pow_zero,mul_one]
    rw [← hwR]
    have hm : (9/16 : ℝ) ≤ SourceProfilesReference.templateThreshold (3/5)-(w : ℝ)*x := by
      norm_num [SourceProfilesReference.templateThreshold]
      linarith
    have hh := mul_le_mul_of_nonneg_left hm hpos.le
    nlinarith only [hh]
  · norm_num only [Fin.val_one,pow_one]
    rw [hhalf]
    have hm : (9/32 : ℝ) ≤
        SourceProfilesReference.templateThreshold ((3/5)*(1/2))-((w : ℝ)/2)*x := by
      norm_num [SourceProfilesReference.templateThreshold]
      linarith
    have hh := mul_le_mul_of_nonneg_left hm hpos.le
    nlinarith only [hh]

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} (streams : InternalStreams src μI w)
  (ν : PositiveRationalLaw (Row (I := I) src))

open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V39IndexedTwoFamilyRun

def ordinarySelected (U : Set (Fin w × V38IndexedTwoTag.Column src)) :
    Set (Fin w × (src.outer.Label × src.gamma.Label)) :=
  fun z => (z.1,Sum.inl z.2) ∈ U

theorem ordinary_selected_mass
    (U : Set (Fin w × V38IndexedTwoTag.Column src)) (β : ℝ)
    (hU : β ≤ ((PositiveRationalLaw.uniform (Fin w)).prod
      (V38IndexedTwoTag.law src)).toFiniteLaw.prob (· ∈ U)) :
    SourceProfilesReference.templateThreshold β ≤
      ((PositiveRationalLaw.uniform (Fin w)).prod
        (ordinaryLaw src)).toFiniteLaw.prob (· ∈ ordinarySelected src U) := by
  classical
  let σ := (PositiveRationalLaw.uniform (Fin w)).toFiniteLaw
  let χ := (V38IndexedTwoTag.law src).toFiniteLaw
  let ο := (ordinaryLaw src).toFiniteLaw
  have hpoint (i : Fin w) : χ.prob (fun Z => (i,Z) ∈ U) ≤
      (255/256 : ℝ)*ο.prob (fun Z => (i,Sum.inl Z) ∈ U)+1/256 := by
    have hs := V38IndexedTwoTag.prob_split src (fun Z => (i,Z) ∈ U)
    have hd := (diagonalLaw src).toFiniteLaw.prob_le_one
      (fun Z => (i,Sum.inr Z) ∈ U)
    dsimp only [χ,ο]
    rw [hs]
    simp only [ordinaryLaw,diagonalLaw] at *
    linarith
  have hsum : (∑ i : Fin w, σ.weight i*χ.prob (fun Z => (i,Z) ∈ U)) ≤
      (255/256 : ℝ)*(∑ i : Fin w, σ.weight i*ο.prob (fun Z => (i,Sum.inl Z) ∈ U))+1/256 := by
    calc
      _ ≤ ∑ i : Fin w, σ.weight i*((255/256 : ℝ)*ο.prob
          (fun Z => (i,Sum.inl Z) ∈ U)+1/256) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hpoint i) (σ.nonneg i)
      _ = _ := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        simp_rw [mul_left_comm (σ.weight _) (255/256 : ℝ)]
        rw [← Finset.mul_sum,← Finset.sum_mul,σ.total]
        ring
  have hp := FiniteLaw.prod_prob σ χ (fun i Z => (i,Z) ∈ U)
  have ho := FiniteLaw.prod_prob σ ο (fun i Z => (i,Sum.inl Z) ∈ U)
  rw [PositiveRationalLaw.toFiniteLaw_prod] at hU ⊢
  change β ≤ (σ.prod χ).prob (fun z => (z.1,z.2) ∈ U) at hU
  change SourceProfilesReference.templateThreshold β ≤
    (σ.prod ο).prob (fun z => (z.1,Sum.inl z.2) ∈ U)
  rw [hp] at hU
  rw [ho]
  unfold SourceProfilesReference.templateThreshold
  linarith

noncomputable def tupleCodeSource
    (hwise : IsDWise 8192 streams.law.toFiniteLaw
      (InternalStreams.decode src streams) ν.toFiniteLaw) :
    CodeSource 8192 w (Row (I := I) src) ν where
  Label := InternalLabel src streams
  finite := inferInstance
  decEq := inferInstance
  law := streams.law
  decode := InternalStreams.decode src streams
  exactLaw := hwise

def W (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y) :
    InternalLabel src streams → (Fin w × V38IndexedTwoTag.Column src) → Bool :=
  fun t row => V38IndexedTwoTag.matrix src R₀ activity ξ₀ row.2
    (InternalStreams.decode src streams t row.1)

theorem profile
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (H a : ℕ) (x θ : ℝ) (hH : 2 ≤ H) (ha : 2 ≤ a) (hw : w=2^a)
    (hx : 0 < x) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (he : V38Moments.exceptionCount θ 1 ≤ w/128)
    (hwx : (w : ℝ)*x < 1/256)
    (hwise : IsDWise 8192 streams.law.toFiniteLaw
      (InternalStreams.decode src streams) ν.toFiniteLaw)
    (hp : V38RestrictionProfiles.TwoThresholdProfile (Nref src R₀ activity ξ₀)
      (ordinaryLaw src).toFiniteLaw ν.toFiniteLaw x (H : ℤ)) :
    V38RestrictionProfiles.TwoThresholdProfile (W src streams R₀ activity ξ₀)
      streams.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin w)).prod (V38IndexedTwoTag.law src)).toFiniteLaw
      θ ((H+a : ℕ) : ℤ) := by
  classical
  have hbudget := internal_population_budgets w a x θ ha hw hx hθ he hwx
  have hwR : (w : ℝ)=(2 : ℝ)^a := by rw [hw,Nat.cast_pow,Nat.cast_ofNat]
  intro j Y' U hY hU
  let Uo := ordinarySelected src U
  have hUo := ordinary_selected_mass src U ((3/5 : ℝ)*(1/2 : ℝ)^j.val) hU
  have hscale : (2 : ℝ)^(a-j.val)*x < 1 := by
    have hpow : (2 : ℝ)^(a-j.val) ≤ w := by
      rw [hwR]
      exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le a j.val)
    have hm := mul_le_mul_of_nonneg_right hpow hx.le
    linarith
  have hc := V39IndexedProfiles.codeSource_rung
    (ordinaryLaw src) ν (Nref src R₀ activity ξ₀)
    (tupleCodeSource src streams ν hwise) Uo Y' H (a-j.val) x
    (SourceProfilesReference.templateThreshold ((3/5 : ℝ)*(1/2 : ℝ)^j.val)) θ 1
    (by have hj:=j.isLt; omega) hH hx hscale hp hUo (hbudget j)
    hθ hθ1 hY (by norm_num)
  let M := fun (row : Fin w × (src.outer.Label × src.gamma.Label))
    (t : InternalLabel src streams) =>
      Nref src R₀ activity ξ₀ row.2 (InternalStreams.decode src streams t row.1)
  change H+(a-j.val) ≤ Compression.restrictionD M Uo Y' at hc
  have htrans : Compression.restrictionD M Uo Y' =
      Compression.restrictionD
        (fun (t : InternalLabel src streams) (row : Fin w × (src.outer.Label × src.gamma.Label)) =>
          W src streams R₀ activity ξ₀ t (row.1,Sum.inl row.2)) Y' Uo :=
    (SourceProjection.restrictionD_transpose M Uo Y').symm
  rw [htrans] at hc
  have hmap := SourceProjection.restrictionD_map_le (W src streams R₀ activity ξ₀) id
    (fun row : Fin w × (src.outer.Label × src.gamma.Label) => (row.1,Sum.inl row.2))
    Y' U Y' Uo (by intro t ht; exact ht) (by intro row hr; exact hr)
  have hl := hc.trans hmap
  exact_mod_cast (show (H : ℤ)+a-j.val ≤
    (Compression.restrictionD (W src streams R₀ activity ξ₀) Y' U : ℤ) by omega)

end CurrentAdditive.V39IndexedInternalProfile

#print axioms CurrentAdditive.V39IndexedInternalProfile.ordinary_selected_mass
#print axioms CurrentAdditive.V39IndexedInternalProfile.tupleCodeSource
#print axioms CurrentAdditive.V39IndexedInternalProfile.profile
