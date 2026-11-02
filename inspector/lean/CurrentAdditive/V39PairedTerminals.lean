import CurrentAdditive.V38Fin2Exact
import CurrentAdditive.GeneratedPairedScalar

/-! Current two-threshold paired-selector terminal bounds. The old scalar
projection and source-law identity are reused; amplification is the reviewed
Fin 2 exact provider. Both tags at the same coordinate remain distinct. -/

namespace CurrentAdditive.V39PairedTerminals

open Paper2 Paper2.SourceProjection Paper2.PairedSelectorCapacityFibre
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.ArbitraryPrefix
open Workspace.Types.CommComplexity Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem paired_coordinate_cost
    (R₀ : X → Y → Bool) (H : ℕ) (x : ℝ)
    (hD : 1 ≤ D)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (b : Bool × Fin q₂)
    (K : Set (src.inner.Label × src.inner.Label))
    (W : Set src.gamma.Label)
    (C : Set ((Bool × Fin q₂) × src.gamma.Label))
    (hC : ∀ γ ∈ W, (b, γ) ∈ C)
    (hK : (49/64 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K))
    (hW : x ≤ src.gamma.law.toFiniteLaw.prob (· ∈ W)) :
    H ≤ Compression.restrictionD
      (fun z c => pairedIndexed src R₀ z (c.1.1, (c.1.2, c.2))) K C := by
  classical
  let p : (src.inner.Label × src.inner.Label) → Fin q₁ × X :=
    fun z => taggedDecode src z b
  let M : (src.inner.Label × src.inner.Label) →
      ((Bool × Fin q₂) × src.gamma.Label) → Bool :=
    fun z c => pairedIndexed src R₀ z (c.1.1, (c.1.2, c.2))
  let F : src.gamma.Label → (src.inner.Label × src.inner.Label) → Bool :=
    fun γ z => M z (b, γ)
  have himage : (3/5 : ℝ) ≤
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw.prob
        (· ∈ p '' K) := by
    have hmass := FiniteLaw.prob_le_image _ _ _
      (pair_tagged_coordinate_pushes src hD b) K
    linarith
  have hfirst := (V38RestrictionProfiles.twoThresholdProfile_iff _ _ _ _ _).mp hprofile |>.1
  have hbase : H ≤ Compression.restrictionD (A src R₀) W (p '' K) := by
    exact_mod_cast hfirst W (p '' K) hW himage
  have hproj : Compression.restrictionD (A src R₀) W (p '' K) ≤
      Compression.restrictionD F W K := by
    apply restrictionD_projected_le F (A src R₀) id p W K W
      (by intro _ h; exact h)
    intro γ _ z _
    rfl
  have htrans : Compression.restrictionD F W K =
      Compression.restrictionD (fun z γ => F γ z) K W :=
    (restrictionD_transpose F W K).symm
  have hmap : Compression.restrictionD (fun z γ => F γ z) K W ≤
      Compression.restrictionD M K C := by
    simpa only [F] using restrictionD_map_le M
      (fun z : src.inner.Label × src.inner.Label => z)
      (fun γ : src.gamma.Label => (b, γ))
      K C K W
      (by intro z hz; exact hz) hC
  exact hbase.trans (hproj.trans (htrans.le.trans hmap))

theorem selected_paired_exact_lower
    (R₀ : X → Y → Bool) (d a n : ℕ) (x : ℝ)
    (hD : 8 ≤ D) (ha : 1 ≤ a) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (d : ℤ))
    (e : Fin n → Bool × Fin q₂) (he : Function.Injective e)
    (hcount : 2^(a-1)+1 ≤ n)
    (Rows : Fin n → Set src.gamma.Label)
    (hrow : ∀ i : Fin n,
      (2 : ℝ)^a*x ≤ src.gamma.law.toFiniteLaw.prob (· ∈ Rows i))
    (K : Set (src.inner.Label × src.inner.Label))
    (hK : (9/25 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K)) :
    d+a ≤ Compression.restrictionD
      (fun (u : Fin n × src.gamma.Label) z =>
        pairedIndexed src R₀ z ((e u.1).1, ((e u.1).2, u.2)))
      (rowRectangle Finset.univ Rows) K := by
  have hwiseD := dwise_comp_injective D
    (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw)
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
    (taggedDecode src) (pair_tagged_exact src) e he
  have hwise8 : IsDWise 8
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw)
      (fun z (i : Fin n) => taggedDecode src z (e i))
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw := by
    intro J hJ E
    exact hwiseD J (hJ.trans hD) E
  have hcount' : 2^(a-1)+1 ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa using hcount
  have hrow' : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (2 : ℝ)^a*x ≤ src.gamma.law.toFiniteLaw.prob (· ∈ Rows i) := by
    intro i _
    exact hrow i
  simpa only [pairedIndexed_entry] using
    V38Fin2Exact.exactboost src.gamma.law
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX)
      (A src R₀)
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw)
      (fun z (i : Fin n) => taggedDecode src z (e i))
      hwise8 Finset.univ Rows K d a x ha hd hx hscale hprofile
      hcount' hrow' hK

theorem selected_paired_alice_cost
    (R₀ : X → Y → Bool) (d a n : ℕ) (x : ℝ)
    (hD : 8 ≤ D) (ha : 1 ≤ a) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (d : ℤ))
    (e : Fin n → Bool × Fin q₂) (he : Function.Injective e)
    (hcount : 2^(a-1)+1 ≤ n)
    (Rows : Fin n → Set src.gamma.Label)
    (hrow : ∀ i : Fin n,
      (2 : ℝ)^a*x ≤ src.gamma.law.toFiniteLaw.prob (· ∈ Rows i))
    (K : Set (src.inner.Label × src.inner.Label))
    (hK : (49/64 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K))
    (C : Set ((Bool × Fin q₂) × src.gamma.Label))
    (hRows : ∀ i : Fin n, ∀ γ ∈ Rows i, (e i, γ) ∈ C)
    (query : K → Bool) (left right : Protocol K C Bool)
    (hP : (Protocol.aNode query left right).Computes
      (fun z c => pairedIndexed src R₀ z.val
        (c.val.1.1, (c.val.1.2, c.val.2)))) :
    d+a+1 ≤ (Protocol.aNode query left right).cost := by
  classical
  let M : (src.inner.Label × src.inner.Label) →
      ((Bool × Fin q₂) × src.gamma.Label) → Bool :=
    fun z c => pairedIndexed src R₀ z (c.1.1, (c.1.2, c.2))
  let b := heavyRowBit
    (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw) K query
  let K' := SourceSupportCapacity.rowFibre K query b
  have hK' : (9/25 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K') := by
    have ht := heavy_rowFibre_mass
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw)
      K query (49/128 : ℝ) (by linarith)
    change (49/128 : ℝ) ≤ _ at ht
    linarith
  have hl := selected_paired_exact_lower src R₀ d a n x hD ha hd hx
    hscale hprofile e he hcount Rows hrow K' hK'
  have hsel : Compression.restrictionD
      (fun (u : Fin n × src.gamma.Label) z =>
        pairedIndexed src R₀ z ((e u.1).1, ((e u.1).2, u.2)))
      (rowRectangle Finset.univ Rows) K' ≤
      Compression.restrictionD (fun c z => M z c) C K' := by
    simpa only [M] using SourceProjection.restrictionD_map_le
      (fun c z => M z c)
      (fun u : Fin n × src.gamma.Label => (e u.1, u.2))
      (fun z : src.inner.Label × src.inner.Label => z)
      C K' (rowRectangle Finset.univ Rows) K'
      (by
        intro u hu
        exact hRows u.1 u.2 (by simpa only [rowRectangle, Finset.mem_univ,
          true_and] using hu))
      (by intro z hz; exact hz)
  have htrans : Compression.restrictionD (fun c z => M z c) C K' =
      Compression.restrictionD M K' C :=
    SourceProjection.restrictionD_transpose M K' C
  have hchild : Compression.restrictionD M K' C + 1 ≤
      (Protocol.aNode query left right).cost :=
    rowFibre_restrictionD_add_one_le M K C query left right hP b
  omega

end CurrentAdditive.V39PairedTerminals

#print axioms CurrentAdditive.V39PairedTerminals.paired_coordinate_cost
#print axioms CurrentAdditive.V39PairedTerminals.selected_paired_exact_lower
#print axioms CurrentAdditive.V39PairedTerminals.selected_paired_alice_cost
