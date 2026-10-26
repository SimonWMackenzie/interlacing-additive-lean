import CurrentAdditive.GeneratedOwnerRowJoint
import CurrentAdditive.InjectiveProjectionTVCompatible
import CurrentAdditive.ConditioningGeneralComplete

/-! Appendix I:670--677, good conditional pair projections for actual
retained indexed W tuples and the original product row law. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix

private def pairToFin2 {A : Type*} (z : A × A) : Fin 2 → A :=
  fun k => if k.val = 0 then z.1 else z.2

private def fin2ToPair {A : Type*} (v : Fin 2 → A) : A × A :=
  (v 0, v 1)

private def pairFin2Equiv {A : Type*} : (A × A) ≃ (Fin 2 → A) where
  toFun := pairToFin2
  invFun := fin2ToPair
  left_inv z := by cases z; rfl
  right_inv v := by
    funext k
    fin_cases k <;> rfl

private theorem pair_prod_eq_iid2 {A : Type*} [Fintype A]
    (μ : FiniteLaw A) (B : Set (A × A)) :
    (μ.prod μ).prob (· ∈ B) =
      (μ.iid 2).prob (fun v => fin2ToPair v ∈ B) := by
  classical
  unfold FiniteLaw.prob
  apply Fintype.sum_equiv pairFin2Equiv
  intro z
  have hw : (μ.prod μ).weight z = (μ.iid 2).weight (pairFin2Equiv z) := by
    rcases z with ⟨a,b⟩
    simp [FiniteLaw.prod, FiniteLaw.iid,
      pairFin2Equiv, pairToFin2]
  have hz : fin2ToPair (pairFin2Equiv z) = z :=
    pairFin2Equiv.left_inv z
  change (if z ∈ B then (μ.prod μ).weight z else 0) =
    (if fin2ToPair (pairFin2Equiv z) ∈ B then
      (μ.iid 2).weight (pairFin2Equiv z) else 0)
  rw [hz, hw]

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))

/-- A good conditional pair projection forces the *original* product-row
mass of the actual U pair image to be at least 0.99. Conditioning is only
used to certify inclusion of U's pair image, not to declare U independent. -/
theorem owner_good_pair_image_of_projectionTV
    {w : ℕ} (streams : InternalStreams src μI w)
    (U Yevent : Set (InternalLabel src streams))
    (hYU : Yevent ⊆ U)
    (hY : 0 < streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (i j : Fin w) (hij : i ≠ j)
    (ε : ℝ) (hε : ε ≤ 1/100)
    (hTV : CurrentAdditive.projectionTV
      (CurrentAdditive.condition streams.law.toFiniteLaw
        (· ∈ Yevent) hY)
      (rowLaw src μI).toFiniteLaw
      (InternalStreams.decode src streams)
      (Finset.univ.image (fun k : Fin 2 => if k.val = 0 then i else j)) ≤ ε) :
    (99 / 100 : ℝ) ≤
      ((rowLaw src μI).toFiniteLaw.prod
        (rowLaw src μI).toFiniteLaw).prob
          (· ∈ (fun t =>
            (InternalStreams.decode src streams t i,
             InternalStreams.decode src streams t j)) '' U) := by
  classical
  let ν := streams.law.toFiniteLaw
  let μ := (rowLaw src μI).toFiniteLaw
  let e : Fin 2 → Fin w := fun k => if k.val = 0 then i else j
  let B : Set (Row (I := G × (V ⊕ Aux)) src ×
      Row (I := G × (V ⊕ Aux)) src) :=
    (fun t => (InternalStreams.decode src streams t i,
      InternalStreams.decode src streams t j)) '' U
  have he : Function.Injective e := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · rfl
    · exact (hij (by simpa [e] using hkl)).elim
    · exact (hij (by simpa [e] using hkl.symm)).elim
    · rfl
  have hcontain (t : InternalLabel src streams) (ht : t ∈ Yevent) :
      (InternalStreams.decode src streams t i,
       InternalStreams.decode src streams t j) ∈ B :=
    ⟨t, hYU ht, rfl⟩
  have hconditional :
      (CurrentAdditive.condition ν (· ∈ Yevent) hY).prob
        (fun t => B (InternalStreams.decode src streams t i,
          InternalStreams.decode src streams t j)) = 1 := by
    rw [CurrentAdditive.condition_prob_event_eq_div]
    have heq : ν.prob (fun t => t ∈ Yevent ∧
        B (InternalStreams.decode src streams t i,
          InternalStreams.decode src streams t j)) =
        ν.prob (· ∈ Yevent) := by
      congr 1
      funext t
      apply propext
      exact ⟨And.left, fun ht => ⟨ht, hcontain t ht⟩⟩
    rw [heq]
    exact div_self (ne_of_gt hY)
  have htv := CurrentAdditive.injective_projectionTV_event_abs
    (CurrentAdditive.condition ν (· ∈ Yevent) hY) μ
    (InternalStreams.decode src streams) e he ε hTV
    (fun v => fin2ToPair v ∈ B)
  have hpoint : (fun t => fin2ToPair (fun k =>
      InternalStreams.decode src streams t (e k)) ∈ B) =
      (fun t => B (InternalStreams.decode src streams t i,
        InternalStreams.decode src streams t j)) := by
    funext t
    rfl
  rw [hpoint, hconditional] at htv
  have hprod := pair_prod_eq_iid2 μ B
  rw [← hprod] at htv
  have hh := (abs_le.mp htv).2
  linarith

#print axioms owner_good_pair_image_of_projectionTV

/-- For the literal independent-stream source, the manuscript's conditioning
theorem selects all but its stated exceptional coordinates. Every distinct
remaining pair has at least `0.99` original product-row image mass in the
actual retained tuple set. The retained set itself is not given a product law. -/
theorem owner_good_pairs_from_conditioning
    {w : ℕ} (streams : InternalStreams src μI w)
    (U Yevent : Set (InternalLabel src streams))
    (hYU : Yevent ⊆ U)
    (v τ : ℝ)
    (hv : 0 < v)
    (hvY : v ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hτ : 0 < τ)
    (hD : 8 * 1024 ≤ D)
    (hε : CurrentAdditive.conditioningEpsilonR 1024 v τ ≤ 1 / 100) :
    ∃ E : Finset (Fin w),
      E.card ≤ CurrentAdditive.conditioningExceptionCountR 1024 v τ ∧
      ∀ i j : Fin w, i ≠ j → i ∉ E → j ∉ E →
        (99 / 100 : ℝ) ≤
          ((rowLaw src μI).toFiniteLaw.prod
            (rowLaw src μI).toFiniteLaw).prob
              (· ∈ (fun t =>
                (InternalStreams.decode src streams t i,
                 InternalStreams.decode src streams t j)) '' U) := by
  classical
  have hwise : IsDWise (8 * 1024) streams.law.toFiniteLaw
      (InternalStreams.decode src streams) (rowLaw src μI).toFiniteLaw := by
    intro J hJ A
    exact (internal_streams_row_dwise src μI streams) J (by omega) A
  obtain ⟨E, hEcard, hTV⟩ :=
    CurrentAdditive.conditioning_exceptional_coordinates_R
      (by decide : Even 1024) (by decide : 8 ≤ 1024)
      streams.law.toFiniteLaw (rowLaw src μI).toFiniteLaw
      (InternalStreams.decode src streams) (· ∈ Yevent)
      v τ hv hvY hτ hwise
  refine ⟨E, hEcard, ?_⟩
  intro i j hij hi hj
  let e : Fin 2 → Fin w := fun k => if k.val = 0 then i else j
  have he_mem (k : Fin 2) : e k ∉ E := by
    fin_cases k <;> simp [e, hi, hj]
  have hsubset : Finset.univ.image e ⊆ (Finset.univ : Finset (Fin w)) \ E := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    simp [he_mem k]
  have hcard : (Finset.univ.image e).card ≤ 8 := by
    calc
      (Finset.univ.image e).card ≤ (Finset.univ : Finset (Fin 2)).card :=
        Finset.card_image_le
      _ = 2 := by decide
      _ ≤ 8 := by omega
  exact owner_good_pair_image_of_projectionTV src μI streams U Yevent
    hYU (lt_of_lt_of_le hv hvY) i j hij
    (CurrentAdditive.conditioningEpsilonR 1024 v τ) hε
    (hTV (Finset.univ.image e) hsubset hcard)

#print axioms owner_good_pairs_from_conditioning

end CurrentAdditive.DeterministicIndexedMatrix.Sources
