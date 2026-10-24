import CurrentAdditive.IndexedProfilePopulation
import CurrentAdditive.IndexedProfileConditioning
import CurrentAdditive.RareBoostCanonicalSharp
import Paper2.AModelTape

/-! Appendix I `det:profiles`: one actual indexed matrix rung. The sole
analytic input is the proved conditioned-source total-variation bound; the
protocol lower bound is `rareboost_canonical_sharp`. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.SourcePopulation
open Workspace.Types.CommComplexity

theorem profile_full_cost
    {X Z : Type*} [Fintype X] [Fintype Z]
    (μ : FiniteLaw X) (ν : FiniteLaw Z) (F : X → Z → Bool)
    (x : ℝ) (d : ℕ) (hx : x ≤ 1)
    (hp : RestrictionProfile F μ ν x (d : ℤ)) :
    d ≤ D F := by
  have hrow : x ≤ μ.prob (· ∈ (Set.univ : Set X)) := by
    simpa using hx
  have hcol : (3/5 : ℝ) * (1/2 : ℝ)^(0:ℕ) ≤
      ν.prob (· ∈ (Set.univ : Set Z)) := by
    simp
    norm_num
  have hl := hp (0 : Fin 3) Set.univ Set.univ hrow hcol
  have hu := Paper2.SourceProfilesInner.restrictionD_le F Set.univ Set.univ
  have hcast : (d : ℤ) ≤ (D F : ℤ) := by
    have hzero : ((0 : Fin 3).val : ℤ) = 0 := rfl
    simp only [hzero, sub_zero] at hl
    exact hl.trans (Int.ofNat_le.mpr hu)
  exact_mod_cast hcast

theorem indexed_profile_rung
    {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]
    [DecidableEq X] [DecidableEq Z]
    {q : ℕ} [NeZero q]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    (decode : S → Fin q → Z)
    (hwise : IsDWise (8*1024) source decode ν.toFiniteLaw)
    (U : Set (Fin q × X)) (W : Set S)
    (E : Finset (Fin q))
    (d a : ℕ) (x β v ε : ℝ)
    (ha : 1 ≤ a) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x < 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hU : β ≤ ((PositiveRationalLaw.uniform (Fin q)).prod μ).toFiniteLaw.prob
      (· ∈ U))
    (hbudget : (((2^(a-1)+1) + E.card : ℕ) : ℝ) *
      (1 - (2 : ℝ)^a * x) ≤ (q : ℝ) * (β - (2 : ℝ)^a * x))
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hW : v ≤ source.prob (· ∈ W))
    (hεpos : 0 < ε)
    (hεcap : ε ≤ (2 : ℝ)^(-20 : ℤ) / 1024 * v^((1 : ℝ)/256))
    (hTV : ∀ J : Finset (Fin q), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      CurrentAdditive.projectionTV
        (CurrentAdditive.condition source (· ∈ W) (hv.trans_le hW))
        ν.toFiniteLaw decode J ≤ ε) :
    d+a ≤ Paper2.Compression.restrictionD
      (fun row col => F row.2 (decode col row.1)) U W := by
  classical
  obtain ⟨e, houtside, hmass⟩ :=
    select_avoiding_exceptions μ q (2^(a-1)+1) U E β
      ((2 : ℝ)^a * x) hscale hU hbudget
  let Good : Finset (Fin q) := Finset.univ.image e
  have hcount : 2^(a-1)+1 ≤ Good.card := by
    simp [Good, Finset.card_image_of_injective _ e.injective]
  have hgoodOut : ∀ i ∈ Good, i ∉ E := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact houtside j
  let Rows : Fin q → Set X := fun i => {u | (i,u) ∈ U}
  have hrow : ∀ i ∈ Good, (2 : ℝ)^a * x ≤
      μ.toFiniteLaw.prob (· ∈ Rows i) := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hmass j
  have hcond : (1/2 : ℝ) ≤
      source.prob (· ∈ W) / source.prob (· ∈ W) := by
    have hwpos := hv.trans_le hW
    rw [div_self (ne_of_gt hwpos)]
    norm_num
  have hlower := CurrentAdditive.ArbitraryPrefix.rareboost_canonical_sharp
    μ ν F source decode hwise Good E Rows W W d a x v ε
    ha hd hx hscale.le hprofile hcount hgoodOut hrow
    hv hv1 hW (Set.Subset.rfl) hcond hεpos hεcap hTV
  have hsub : Set.MapsTo id
      (CurrentAdditive.ArbitraryPrefix.rowRectangle Good Rows) U := by
    intro row hrow'
    change row.1 ∈ Good ∧ row.2 ∈ Rows row.1 at hrow'
    exact hrow'.2
  exact hlower.trans
    (Paper2.SourceProjection.restrictionD_map_le
      (fun row col => F row.2 (decode col row.1)) id id
      U W (CurrentAdditive.ArbitraryPrefix.rowRectangle Good Rows) W
      hsub (fun _ h => h))

/-- A complete rung for one actual indexed source: the exceptional set and
the selected good blocks are now constructed from the retained rectangle. -/
theorem codeSource_profile_rung
    {X Z : Type*} [Fintype X] [Fintype Z]
    [DecidableEq X] [DecidableEq Z]
    {q : ℕ} [NeZero q]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (src : CodeSource 8192 q Z ν)
    (U : Set (Fin q × X)) (W : Set src.Label)
    (d a : ℕ) (x β v τ : ℝ)
    (ha : 1 ≤ a) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x < 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hU : β ≤ ((PositiveRationalLaw.uniform (Fin q)).prod μ).toFiniteLaw.prob
      (· ∈ U))
    (hbudget : (((2^(a-1)+1) +
        CurrentAdditive.conditioningExceptionCountR 1024 v τ : ℕ) : ℝ) *
      (1 - (2 : ℝ)^a * x) ≤ (q : ℝ) * (β - (2 : ℝ)^a * x))
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hW : v ≤ src.law.toFiniteLaw.prob (· ∈ W))
    (hτ : 0 < τ) :
    d+a ≤ Paper2.Compression.restrictionD
      (fun row col => F row.2 (src.decode col row.1)) U W := by
  obtain ⟨E, hEcard, hTV⟩ :=
    codeSource_conditioning_witness ν src W v τ hv hW hτ
  have hbudgetE : (((2^(a-1)+1) + E.card : ℕ) : ℝ) *
      (1 - (2 : ℝ)^a * x) ≤ (q : ℝ) * (β - (2 : ℝ)^a * x) := by
    have hn : 2^(a-1)+1+E.card ≤
        2^(a-1)+1+CurrentAdditive.conditioningExceptionCountR 1024 v τ := by
      omega
    have hnR : (((2^(a-1)+1) + E.card : ℕ) : ℝ) ≤
        (((2^(a-1)+1) +
          CurrentAdditive.conditioningExceptionCountR 1024 v τ : ℕ) : ℝ) := by
      exact_mod_cast hn
    nlinarith
  apply indexed_profile_rung μ ν F src.law.toFiniteLaw src.decode
    src.exactLaw U W E d a x β v
    (CurrentAdditive.conditioningEpsilonR 1024 v τ)
    ha hd hx hscale hprofile hU hbudgetE hv hv1 hW
  · exact CurrentAdditive.conditioningEpsilonR_pos (by norm_num) hv hτ
  · exact codeSource_epsilon_cap v τ
  · exact hTV

/-- Appendix I `det:profiles`, first full three-level profile on the actual
indexed transpose `A`. The guards are numerical statements about the public
schedule; all source, conditioning and protocol reasoning is discharged. -/
theorem Sources.A_profile_from_schedule
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (R : X → Y → Bool) (d a : ℕ) (ρ x τ : ℝ)
    (hd : 2 ≤ d) (ha : 3 ≤ a) (hρ : 0 < ρ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hτ : 0 < τ)
    (hp : RestrictionProfile R μX.toFiniteLaw μY.toFiniteLaw ρ (d : ℤ))
    (hscale : ∀ j : Fin 3, (2 : ℝ)^(a-j.val) * ρ < 1)
    (hbudget : ∀ j : Fin 3,
      (((2^((a-j.val)-1)+1) +
        CurrentAdditive.conditioningExceptionCountR 1024 x τ : ℕ) : ℝ) *
          (1 - (2 : ℝ)^(a-j.val) * ρ) ≤
        (q₁ : ℝ) *
          ((3/5 : ℝ) * (1/2 : ℝ)^j.val -
            (2 : ℝ)^(a-j.val) * ρ)) :
    RestrictionProfile (Sources.A src R)
      src.gamma.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
      x ((d+a : ℕ) : ℤ) := by
  intro j W U hW hU
  let β : ℝ := (3/5 : ℝ) * (1/2 : ℝ)^j.val
  have hajn : 1 ≤ a-j.val := by omega
  have hβpos : 0 < β := by
    dsimp [β]
    positivity
  have hcost := codeSource_profile_rung μX μY R
    (Sources.headCodeSource src) U W d (a-j.val) ρ β x τ
    hajn hd hρ (hscale j) hp hU (hbudget j)
    hx (by simpa using hx1) hW hτ
  have hentry : (fun row col =>
      R row.2 ((Sources.headCodeSource src).decode col row.1)) =
      Sources.M₁ src R := by
    funext row col
    rfl
  rw [hentry] at hcost
  have htrans : Paper2.Compression.restrictionD (Sources.A src R) W U =
      Paper2.Compression.restrictionD (Sources.M₁ src R) U W := by
    exact Paper2.SourceProjection.restrictionD_transpose _ U W
  have hcostA : d+(a-j.val) ≤
      Paper2.Compression.restrictionD (Sources.A src R) W U := by
    rw [htrans]
    exact hcost
  have hcast : (((d+a : ℕ) : ℤ) - j.val) ≤
      (Paper2.Compression.restrictionD (Sources.A src R) W U : ℤ) := by
    omega
  exact hcast

/-- Appendix I `det:profiles`, second three-level profile on the actual
indexed template matrix `T`, using the proved profile of `A` as its base. -/
theorem Sources.T_profile_from_schedule
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (R : X → Y → Bool) (H₁ a : ℕ) (x τ : ℝ)
    (hd : 2 ≤ H₁) (ha : 3 ≤ a) (hx : 0 < x)
    (hx1 : x ≤ 1) (hτ : 0 < τ)
    (hp : RestrictionProfile (Sources.A src R)
      src.gamma.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
      x (H₁ : ℤ))
    (hscale : ∀ j : Fin 3, (2 : ℝ)^(a-j.val) * x < 1)
    (hbudget : ∀ j : Fin 3,
      (((2^((a-j.val)-1)+1) +
        CurrentAdditive.conditioningExceptionCountR 1024 x τ : ℕ) : ℝ) *
          (1 - (2 : ℝ)^(a-j.val) * x) ≤
        (q₂ : ℝ) *
          ((3/5 : ℝ) * (1/2 : ℝ)^j.val -
            (2 : ℝ)^(a-j.val) * x)) :
    RestrictionProfile (Sources.T src R)
      src.inner.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₂)).prod
        src.gamma.law).toFiniteLaw)
      x ((H₁+a : ℕ) : ℤ) := by
  intro j W U hW hU
  let β : ℝ := (3/5 : ℝ) * (1/2 : ℝ)^j.val
  have hajn : 1 ≤ a-j.val := by omega
  have hcost := codeSource_profile_rung src.gamma.law
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μX)
    (Sources.A src R) src.inner U W H₁ (a-j.val) x β x τ
    hajn hd hx (hscale j) hp hU (hbudget j)
    hx (by simpa using hx1) hW hτ
  have hentry : (fun row col =>
      Sources.A src R row.2 (src.inner.decode col row.1)) =
      fun row col => Sources.T src R col row := by
    funext row col
    rfl
  rw [hentry] at hcost
  have htrans : Paper2.Compression.restrictionD (Sources.T src R) W U =
      Paper2.Compression.restrictionD
        (fun row col => Sources.T src R col row) U W := by
    exact Paper2.SourceProjection.restrictionD_transpose _ U W
  have hcostT : H₁+(a-j.val) ≤
      Paper2.Compression.restrictionD (Sources.T src R) W U := by
    rw [htrans]
    exact hcost
  have hcast : (((H₁+a : ℕ) : ℤ) - j.val) ≤
      (Paper2.Compression.restrictionD (Sources.T src R) W U : ℤ) := by
    omega
  exact hcast

/-- Forgetting the independent tail of an ordinary indexed column can only
increase the mass of its image under the original outer-label law. -/
theorem Sources.ordinary_outer_image_mass
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (W : Set (src.outer.Label × src.gamma.Label)) :
    (ordinaryLaw src).toFiniteLaw.prob (· ∈ W) ≤
      src.outer.law.toFiniteLaw.prob (· ∈ Prod.fst '' W) := by
  have hpush : (ordinaryLaw src).toFiniteLaw.PushesTo
      src.outer.law.toFiniteLaw Prod.fst := by
    intro E
    simpa [ordinaryLaw, PositiveRationalLaw.toFiniteLaw_prod] using
      Paper2.AModel.prod_prob_fst src.outer.law.toFiniteLaw
        src.gamma.law.toFiniteLaw E
  exact Paper2.FiniteLaw.prob_le_image _ _ _ hpush W

/-- Appendix I `det:profiles`, the ordinary reference profile of the actual
generated matrix. The independent tail is forgotten only after a surviving
original ordinary column has been selected as representative. -/
theorem Sources.Nref_profile_from_schedule
    {G V A X Y : Type*} [Fintype G] [Fintype V] [Fintype A]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (μI : PositiveRationalLaw (G × (V ⊕ A)))
    (R : X → Y → Bool)
    (activity : (G × (V ⊕ A)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (H₂ a : ℕ) (x τ : ℝ)
    (hd : 2 ≤ H₂) (ha : 3 ≤ a) (hx : 0 < x)
    (hx1 : x ≤ 1) (hτ : 0 < τ)
    (hp : RestrictionProfile (Sources.T src R)
      src.inner.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₂)).prod
        src.gamma.law).toFiniteLaw)
      x (H₂ : ℤ))
    (hscale : ∀ j : Fin 3, (2 : ℝ)^(a-j.val) * x < 1)
    (hbudget : ∀ j : Fin 3,
      (((2^((a-j.val)-1)+1) +
        CurrentAdditive.conditioningExceptionCountR 1024 x τ : ℕ) : ℝ) *
          (1 - (2 : ℝ)^(a-j.val) * x) ≤
        (s : ℝ) *
          (((((3/5 : ℝ) * (1/2 : ℝ)^j.val) - (1 - 255/256)) /
            (255/256)) - (2 : ℝ)^(a-j.val) * x)) :
    RestrictionProfile (Sources.Nref src R activity ξ₀)
      (ordinaryLaw src).toFiniteLaw
      (rowLaw src μI).toFiniteLaw x ((H₂+a : ℕ) : ℤ) := by
  intro j W U hW hU
  let β : ℝ := (3/5 : ℝ) * (1/2 : ℝ)^j.val
  let β' : ℝ := (β - (1 - 255/256)) / (255/256)
  let Ut : Set (Fin s × src.inner.Label) := fun pz => Sum.inl pz ∈ U
  let Wout : Set src.outer.Label := Prod.fst '' W
  have hajn : 1 ≤ a-j.val := by omega
  have hUt : β' ≤ (templateRowLaw src).toFiniteLaw.prob (· ∈ Ut) := by
    simpa only [β', β, Ut] using Sources.template_retained src μI U
      ((3/5 : ℝ) * (1/2 : ℝ)^j.val) hU
  have hWout : x ≤ src.outer.law.toFiniteLaw.prob (· ∈ Wout) :=
    hW.trans (Sources.ordinary_outer_image_mass src W)
  have hcost := codeSource_profile_rung src.inner.law
    ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law)
    (Sources.T src R) src.outer Ut Wout H₂ (a-j.val) x β' x τ
    hajn hd hx (hscale j) hp hUt (hbudget j)
    hx (by simpa using hx1) hWout hτ
  have htransfer : Paper2.Compression.restrictionD
      (fun pz js => Sources.T src R pz.2 (src.outer.decode js pz.1))
      Ut Wout ≤
      Paper2.Compression.restrictionD
        (fun k Z => Sources.Nref src R activity ξ₀ Z k) U W := by
    exact Paper2.SourceProjection.restrictionD_projected_le
      (fun k Z => Sources.Nref src R activity ξ₀ Z k)
      (fun pz js => Sources.T src R pz.2 (src.outer.decode js pz.1))
      Sum.inl Prod.fst U W Ut (by intro pz hpz; exact hpz)
      (by intro pz hpz Z hZ; rfl)
  have htrans : Paper2.Compression.restrictionD
      (fun k Z => Sources.Nref src R activity ξ₀ Z k) U W =
      Paper2.Compression.restrictionD
        (Sources.Nref src R activity ξ₀) W U :=
    (Paper2.SourceProjection.restrictionD_transpose _ U W).symm
  have hcostN : H₂+(a-j.val) ≤
      Paper2.Compression.restrictionD
        (Sources.Nref src R activity ξ₀) W U := by
    exact hcost.trans (htransfer.trans_eq htrans)
  have hcast : (((H₂+a : ℕ) : ℤ) - j.val) ≤
      (Paper2.Compression.restrictionD
        (Sources.Nref src R activity ξ₀) W U : ℤ) := by
    omega
  exact hcast

/-- The first two exact whole-matrix costs follow from their checked profiles
and the actual selector protocols. -/
theorem Sources.A_exact_from_profile
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {D₀ q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := D₀) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (R : X → Y → Bool) (d a : ℕ) (x : ℝ)
    (hD : D R = d) (hx : x ≤ 1) (hwidth : q₁ ≤ 2^a)
    (hp : RestrictionProfile (Sources.A src R)
      src.gamma.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
      x ((d+a : ℕ) : ℤ)) :
    D (Sources.A src R) = d+a := by
  apply Nat.le_antisymm
  · have hclog : Nat.clog 2 q₁ ≤ a :=
      (Nat.clog_le_iff_le_pow (by decide)).2 hwidth
    calc
      D (Sources.A src R) = D (Sources.M₁ src R) := Sources.A_D_eq_M₁ src R
      _ ≤ Nat.clog 2 q₁ + D R := Sources.M₁_D_le src R
      _ ≤ d+a := by omega
  · exact profile_full_cost src.gamma.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
      (Sources.A src R) x (d+a) hx hp

theorem Sources.T_exact_from_profile
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {D₀ q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := D₀) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (R : X → Y → Bool) (H₁ a : ℕ) (x : ℝ)
    (hA : D (Sources.A src R) = H₁) (hx : x ≤ 1)
    (hwidth : q₂ ≤ 2^a)
    (hp : RestrictionProfile (Sources.T src R)
      src.inner.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₂)).prod
        src.gamma.law).toFiniteLaw)
      x ((H₁+a : ℕ) : ℤ)) :
    D (Sources.T src R) = H₁+a := by
  apply Nat.le_antisymm
  · have hclog : Nat.clog 2 q₂ ≤ a :=
      (Nat.clog_le_iff_le_pow (by decide)).2 hwidth
    calc
      D (Sources.T src R) ≤ Nat.clog 2 q₂ + D (Sources.A src R) :=
        Sources.T_D_le src R
      _ ≤ H₁+a := by omega
  · exact profile_full_cost src.inner.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₂)).prod
        src.gamma.law).toFiniteLaw)
      (Sources.T src R) x (H₁+a) hx hp

/-- Appendix I `det:profiles` assembled on one and the same generated source
triple. The three sets of remaining hypotheses are numerical schedule guards;
the exact matrix, law, restriction, and conditioning arguments are internal. -/
theorem Sources.generated_profiles_from_schedule
    {G V A X Y : Type*} [Fintype G] [Fintype V] [Fintype A]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (μI : PositiveRationalLaw (G × (V ⊕ A)))
    (R : X → Y → Bool)
    (activity : (G × (V ⊕ A)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (d a b : ℕ) (ρ x τ : ℝ)
    (hd : 3 ≤ d) (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hρ : 0 < ρ) (hx : 0 < x) (hx1 : x ≤ 1) (hτ : 0 < τ)
    (hD : D R = d)
    (hp : RestrictionProfile R μX.toFiniteLaw μY.toFiniteLaw ρ (d : ℤ))
    (hwidthA : q₁ ≤ 2^a) (hwidthT : q₂ ≤ 2^b)
    (hscaleA : ∀ j : Fin 3, (2 : ℝ)^(a-j.val) * ρ < 1)
    (hscaleT : ∀ j : Fin 3, (2 : ℝ)^(b-j.val) * x < 1)
    (hscaleN : ∀ j : Fin 3, (2 : ℝ)^(a-j.val) * x < 1)
    (hbudgetA : ∀ j : Fin 3,
      (((2^((a-j.val)-1)+1) +
        CurrentAdditive.conditioningExceptionCountR 1024 x τ : ℕ) : ℝ) *
          (1 - (2 : ℝ)^(a-j.val) * ρ) ≤
        (q₁ : ℝ) *
          ((3/5 : ℝ) * (1/2 : ℝ)^j.val -
            (2 : ℝ)^(a-j.val) * ρ))
    (hbudgetT : ∀ j : Fin 3,
      (((2^((b-j.val)-1)+1) +
        CurrentAdditive.conditioningExceptionCountR 1024 x τ : ℕ) : ℝ) *
          (1 - (2 : ℝ)^(b-j.val) * x) ≤
        (q₂ : ℝ) *
          ((3/5 : ℝ) * (1/2 : ℝ)^j.val -
            (2 : ℝ)^(b-j.val) * x))
    (hbudgetN : ∀ j : Fin 3,
      (((2^((a-j.val)-1)+1) +
        CurrentAdditive.conditioningExceptionCountR 1024 x τ : ℕ) : ℝ) *
          (1 - (2 : ℝ)^(a-j.val) * x) ≤
        (s : ℝ) *
          (((((3/5 : ℝ) * (1/2 : ℝ)^j.val) - (1 - 255/256)) /
            (255/256)) - (2 : ℝ)^(a-j.val) * x)) :
    D (Sources.M₁ src R) = d+a ∧
    RestrictionProfile (Sources.A src R)
      src.gamma.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
      x ((d+a : ℕ) : ℤ) ∧
    D (Sources.T src R) = d+a+b ∧
    RestrictionProfile (Sources.T src R)
      src.inner.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw)
      x ((d+a+b : ℕ) : ℤ) ∧
    RestrictionProfile (Sources.Nref src R activity ξ₀)
      (ordinaryLaw src).toFiniteLaw (rowLaw src μI).toFiniteLaw
      x ((d+a+b+a : ℕ) : ℤ) := by
  have hA := Sources.A_profile_from_schedule src R d a ρ x τ
    (by omega) ha hρ hx hx1 hτ hp hscaleA hbudgetA
  have hAexact := Sources.A_exact_from_profile src R d a x hD hx1 hwidthA hA
  have hMexact : D (Sources.M₁ src R) = d+a := by
    rw [← Sources.A_D_eq_M₁ src R]
    exact hAexact
  have hT := Sources.T_profile_from_schedule src R (d+a) b x τ
    (by omega) hb hx hx1 hτ hA hscaleT hbudgetT
  have hTexact := Sources.T_exact_from_profile src R (d+a) b x
    hAexact hx1 hwidthT hT
  have hN := Sources.Nref_profile_from_schedule src μI R activity ξ₀
    (d+a+b) a x τ (by omega) ha hx hx1 hτ
    (by simpa only [Nat.add_assoc] using hT) hscaleN hbudgetN
  refine ⟨hMexact, hA, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hTexact
  · simpa only [Nat.add_assoc] using hT
  · simpa only [Nat.add_assoc] using hN

end CurrentAdditive.DeterministicIndexedMatrix
