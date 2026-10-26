import CurrentAdditive.IndexedProfilePopulation
import CurrentAdditive.ConditioningGeneralComplete

/-! Appendix I `det:profiles`: exceptional positions for an actual indexed
source label set. The event remains a subset of original labels; conditioning
does not replace it with a new independent product source. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2

/-- Reindex exact bounded-wise marginals along an injective coordinate map.
The source labels and their law are untouched. -/
theorem isDWise_reindex
    {I J Z S : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype Z] [Fintype S]
    (D : ℕ) (source : FiniteLaw S) (μ : FiniteLaw Z)
    (decode : S → J → Z) (e : I → J) (he : Function.Injective e)
    (hwise : IsDWise D source decode μ) :
    IsDWise D source (fun s i => decode s (e i)) μ := by
  classical
  intro u hu A
  let t : Finset J := u.image e
  let f : u → t := fun i =>
    ⟨e i.val, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    exact he (congrArg Subtype.val h)
  have ht : t.card ≤ D := by
    rw [show t.card = u.card from Finset.card_image_of_injective u he]
    exact hu
  have h := hwise t ht (fun y : t → Z => A (fun i => y (f i)))
  have hpi := FiniteLaw.pi_prob_restrict (fun _ : t => μ) f hf A
  calc
    source.prob (fun s => A (fun i : u => decode s (e i.val))) =
        (FiniteLaw.pi (fun _ : t => μ)).prob
          (fun y => A (fun i => y (f i))) := by
      simpa only [f] using h
    _ = (FiniteLaw.pi (fun _ : u => μ)).prob A := by
      simpa only using hpi

/-- The first `q₁` head coordinates of Gamma form another exact source on
the same original index set and with the same rational weights. -/
def Sources.headCodeSource
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) :
    CodeSource 8192 q₁ Y μY := by
  let e : Fin q₁ → Fin (q₁+s+1) := fun i => ⟨i.val, by omega⟩
  have he : Function.Injective e := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin (q₁+s+1) => k.val) h)
  exact {
    Label := src.gamma.Label
    finite := src.gamma.finite
    decEq := src.gamma.decEq
    law := src.gamma.law
    decode := fun z i => src.gamma.decode z (e i)
    exactLaw := isDWise_reindex 8192 src.gamma.law.toFiniteLaw
      μY.toFiniteLaw src.gamma.decode e he src.gamma.exactLaw
  }

/-- Apply the proved 8192-wise conditioning theorem to a `CodeSource`. -/
theorem codeSource_conditioning_witness
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {q : ℕ} (μ : PositiveRationalLaw Z)
    (src : CodeSource 8192 q Z μ)
    (W : Set src.Label) (v τ : ℝ)
    (hv : 0 < v)
    (hW : v ≤ src.law.toFiniteLaw.prob (· ∈ W))
    (hτ : 0 < τ) :
    ∃ E : Finset (Fin q),
      E.card ≤ CurrentAdditive.conditioningExceptionCountR 1024 v τ ∧
      ∀ J : Finset (Fin q),
        J ⊆ Finset.univ \ E → J.card ≤ 8 →
          CurrentAdditive.projectionTV
            (CurrentAdditive.condition src.law.toFiniteLaw (· ∈ W)
              (hv.trans_le hW))
            μ.toFiniteLaw src.decode J ≤
              CurrentAdditive.conditioningEpsilonR 1024 v τ := by
  simpa using CurrentAdditive.conditioning_exceptional_coordinates_R
    (R := 1024) (by norm_num) (by norm_num)
    src.law.toFiniteLaw μ.toFiniteLaw src.decode (· ∈ W)
    v τ hv hW hτ src.exactLaw

/-- The manuscript epsilon cap, specialized to `R=1024`. -/
theorem codeSource_epsilon_cap (v τ : ℝ) :
    CurrentAdditive.conditioningEpsilonR 1024 v τ ≤
      (2 : ℝ)^(-20 : ℤ) / 1024 * v^((1 : ℝ)/256) := by
  unfold CurrentAdditive.conditioningEpsilonR
  have h := min_le_right τ
    (((2 : ℝ)^(-(20 : ℝ))) / (1024 : ℕ) * v^((4 : ℝ) / 1024))
  convert h using 1; norm_num

/-- This combines source conditioning with the actual retained population.
The only schedule premise is a numerical count using the displayed
exceptional-coordinate allowance. -/
theorem codeSource_select_conditioned_blocks
    {X Z : Type*} [Fintype X] [Fintype Z]
    [DecidableEq X] [DecidableEq Z]
    {q : ℕ} [NeZero q]
    (μX : PositiveRationalLaw X) (μZ : PositiveRationalLaw Z)
    (src : CodeSource 8192 q Z μZ)
    (U : Set (Fin q × X)) (W : Set src.Label)
    (n : ℕ) (β t v τ : ℝ)
    (ht : t < 1) (hv : 0 < v) (hτ : 0 < τ)
    (hU : β ≤ ((PositiveRationalLaw.uniform (Fin q)).prod μX).toFiniteLaw.prob
      (· ∈ U))
    (hW : v ≤ src.law.toFiniteLaw.prob (· ∈ W))
    (hbudget : ((n + CurrentAdditive.conditioningExceptionCountR 1024 v τ : ℕ) : ℝ) *
      (1 - t) ≤ (q : ℝ) * (β - t)) :
    ∃ (E : Finset (Fin q)) (e : Fin n ↪ Fin q),
      E.card ≤ CurrentAdditive.conditioningExceptionCountR 1024 v τ ∧
      (∀ j, e j ∉ E) ∧
      (∀ j, t ≤ μX.toFiniteLaw.prob (fun x => (e j,x) ∈ U)) ∧
      (∀ J : Finset (Fin q), J ⊆ Finset.univ \ E → J.card ≤ 8 →
        CurrentAdditive.projectionTV
          (CurrentAdditive.condition src.law.toFiniteLaw (· ∈ W)
            (hv.trans_le hW))
          μZ.toFiniteLaw src.decode J ≤
            CurrentAdditive.conditioningEpsilonR 1024 v τ) := by
  obtain ⟨E, hEcard, hTV⟩ :=
    codeSource_conditioning_witness μZ src W v τ hv hW hτ
  have hbudgetE : ((n + E.card : ℕ) : ℝ) * (1 - t) ≤
      (q : ℝ) * (β - t) := by
    have hmon : n + E.card ≤ n + CurrentAdditive.conditioningExceptionCountR 1024 v τ := by
      omega
    have hmonR : ((n + E.card : ℕ) : ℝ) ≤
        ((n + CurrentAdditive.conditioningExceptionCountR 1024 v τ : ℕ) : ℝ) := by
      exact_mod_cast hmon
    nlinarith
  obtain ⟨e, hout, hrow⟩ :=
    select_avoiding_exceptions μX q n U E β t ht hU hbudgetE
  exact ⟨E, e, hEcard, hout, hrow, hTV⟩

end CurrentAdditive.DeterministicIndexedMatrix
