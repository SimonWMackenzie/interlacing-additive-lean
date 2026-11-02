import CurrentAdditive.IndexedOwnerConditionedRunProd
import CurrentAdditive.DeterministicParameters

/-! The public Appendix I schedule supplies the numerical inputs of the
original indexed owner initializer. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open CurrentAdditive.DeterministicParameters
open Paper2 Paper2.ReferenceCertificates Paper2.ReferenceCertificateTree
  Paper2.ReferenceOwners Workspace.Types.Protocol

theorem indexed_owner_public_scale
    (L Δ n m C : ℕ) (γ : ℚ)
    (hadm : Admissible L Δ n m C γ)
    (a : ℕ) (ha : a ≤ 2*L) :
    (2 : ℝ)^a * (x L : ℝ) ≤ 1 := by
  have hpowN : 2^a ≤ w L := by
    rw [w_eq_pow]
    exact Nat.pow_le_pow_right (by decide) ha
  have hpow : (2 : ℝ)^a ≤ (w L : ℝ) := by exact_mod_cast hpowN
  have hx : (0 : ℝ) ≤ (x L : ℝ) := (x_real_pos L).le
  have hmul := mul_le_mul_of_nonneg_right hpow hx
  have hwx : (w L : ℝ) * (x L : ℝ) ≤ 1 / 10000 := by
    have hh : (((w L : ℚ) * x L : ℚ) : ℝ) ≤
        (((1 / 10000 : ℚ) : ℝ)) := Rat.cast_le.mpr hadm.w_x
    norm_num at hh ⊢
    exact hh
  linarith

theorem indexed_owner_public_margin
    (L Δ n m C : ℕ) (γ : ℚ)
    (hadm : Admissible L Δ n m C γ) :
    2 * (w L : ℝ) * (x L : ℝ) +
      (η L Δ γ : ℝ) / (16 * (127 / 128 : ℝ)) < 1 := by
  have hh : (((2 * (w L : ℚ) * x L +
      η L Δ γ / (16 * (127 / 128 : ℚ)) : ℚ)) : ℝ) <
      ((1 : ℚ) : ℝ) := Rat.cast_lt.mpr hadm.owner_gap
  norm_num at hh ⊢
  exact hh

theorem indexed_owner_public_row_threshold
    (L Δ : ℕ) (γ : ℚ) :
    (δU L Δ γ : ℝ) =
      (η L Δ γ : ℝ) / (16 * (w L : ℝ)) := by
  simp [δU, Rat.cast_div, Rat.cast_mul]

/-- The real-valued tree capacity ceiling is bounded by the public rational
owner reserve at any larger exceptional-coordinate count. -/
theorem indexed_exceptionBudget_le_rational_ceiling
    (e k : ℕ) (he : e ≤ k) :
    exceptionBudget e ≤ Nat.ceil ((16 * (k : ℚ)) / 7) := by
  have hnum : (16 * (e : ℝ)) / 7 ≤ (16 * (k : ℝ)) / 7 := by
    have her : (e : ℝ) ≤ k := by exact_mod_cast he
    linarith
  have hQ : (16 * (k : ℚ)) / 7 ≤
      (Nat.ceil ((16 * (k : ℚ)) / 7) : ℚ) := Nat.le_ceil _
  have hR : (16 * (k : ℝ)) / 7 ≤
      (Nat.ceil ((16 * (k : ℚ)) / 7) : ℝ) := by
    have hh : (((16 * (k : ℚ)) / 7 : ℚ) : ℝ) ≤
        ((Nat.ceil ((16 * (k : ℚ)) / 7) : ℚ) : ℝ) :=
      Rat.cast_le.mpr hQ
    norm_num at hh ⊢
    exact hh
  unfold exceptionBudget
  exact Nat.ceil_le.mpr (hnum.trans hR)

theorem indexed_exceptionBudget_le_ownerException
    (L Δ : ℕ) (γ : ℚ) (e : ℕ)
    (he : e ≤ CurrentAdditive.conditioningExceptionCountR 1024
      (θ L : ℝ) ((η L Δ γ : ℝ)/2)) :
    exceptionBudget e ≤ ownerException L Δ γ := by
  have hcount : CurrentAdditive.conditioningExceptionCountR 1024
      (θ L : ℝ) ((η L Δ γ : ℝ)/2) =
      CurrentAdditive.conditioningExceptionCount (θ L : ℝ)
        (((η L Δ γ / 2 : ℚ) : ℝ)) := by
    simp only [Rat.cast_div, Rat.cast_ofNat]
    rfl
  rw [hcount] at he
  simpa [ownerException] using indexed_exceptionBudget_le_rational_ceiling
    e (CurrentAdditive.conditioningExceptionCount (θ L : ℝ)
      (((η L Δ γ / 2 : ℚ) : ℝ))) he

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))

/-- The public schedule instantiates all owner-initializer numerical guards.
The retained tuple event still needs only mass at least the public `θ`. -/
theorem indexed_owner_scheduled_conditioned_run
    (L Δ n m C : ℕ) (γ : ℚ)
    (hL : 1 ≤ L) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hadm : Admissible L Δ n m C γ)
    (streams : InternalStreams src μI (w L))
    (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Fin (w L) × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (P : Protocol Yevent R Bool) (H : ℕ) (hd : 2 ≤ H)
    (hprofile : RestrictionProfile
      (Nref src R₀ activity ξ₀)
      (ordinaryLaw src).toFiniteLaw (rowLaw src μI).toFiniteLaw
      (x L : ℝ) (H : ℤ))
    (hR : 1 - (δU L Δ γ : ℝ) ≤
      (indexedFirstRowLaw src (w_pos L)).prob (· ∈ R))
    (hY : (θ L : ℝ) ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hP : P.Computes (fun t row => W src streams R₀ activity ξ₀ t.val row.val))
    (hPcost : P.cost ≤ H + 2*L) :
    ∃ E : Finset (Fin (w L)),
      E.card ≤ CurrentAdditive.conditioningExceptionCountR 1024
        (θ L : ℝ) ((η L Δ γ : ℝ)/2) ∧
      exceptionBudget E.card ≤ ownerException L Δ γ ∧
      (∀ J : Finset (Fin (w L)),
        J ⊆ Finset.univ \ E → J.card ≤ 8 →
        projectionTV
          (condition streams.law.toFiniteLaw (· ∈ Yevent)
            (lt_of_lt_of_le (by exact_mod_cast theta_pos L) hY))
          (rowLaw src μI).toFiniteLaw
          (InternalStreams.decode src streams) J ≤
            CurrentAdditive.conditioningEpsilonR 1024
              (θ L : ℝ) ((η L Δ γ : ℝ)/2)) ∧
      ∃ row0 : R, ∃ col0 : Yevent,
        ∃ st : State (Fin (w L) × Column src)
          (streams.metadataStream.Label ×
            (streams.baseStream.Label × streams.selectorStream.Label))
          (Fin (w L)) (src.outer.Label × src.gamma.Label),
          st = indexedInitialState src streams R Yevent row0 col0 P E (2*L) ∧
          (let T := run (ordinaryLaw src).toFiniteLaw
            (referenceInput src)
            (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ)) 0 (2*L) st
          let F := fun z : T.Leaves => (T.state z).family
          let final := fun z : T.Leaves => (T.route z).length = 2*L
          2^(2*L) - exceptionBudget E.card ≤ (ownerNodes F final).card ∧
            exceptionalCapacity F final
              (fun z => 2^((2*L)-(T.route z).length)) ≤
              exceptionBudget E.card) := by
  have hη : (0 : ℝ) < (η L Δ γ : ℝ) := by
    exact_mod_cast eta_pos L Δ γ hΔ hγ
  have hθ : (0 : ℝ) < (θ L : ℝ) := by
    exact_mod_cast theta_pos L
  have hR' : 1 - (η L Δ γ : ℝ) / (16 * (w L : ℝ)) ≤
      (indexedFirstRowLaw src (by rw [w_eq_pow]; positivity)).prob
        (· ∈ R) := by
    simpa [indexed_owner_public_row_threshold L Δ γ] using hR
  obtain ⟨E, hE, hTV, row0, col0, st, hst, hcapacity⟩ :=
    indexed_owner_conditioned_run src μI streams R₀ activity ξ₀
    R Yevent P (2*L) H (η L Δ γ : ℝ) (x L : ℝ) (θ L : ℝ)
    (w_eq_pow L) (by omega) hd (x_real_pos L) hη hθ
    (fun a ha => indexed_owner_public_scale L Δ n m C γ hadm a ha)
    hprofile hR' (indexed_owner_public_margin L Δ n m C γ hadm)
    hY hP hPcost
  exact ⟨E, hE, indexed_exceptionBudget_le_ownerException L Δ γ E.card hE,
    hTV, row0, col0, st, hst, hcapacity⟩

#print axioms indexed_owner_public_scale
#print axioms indexed_owner_public_margin
#print axioms indexed_owner_public_row_threshold
#print axioms indexed_exceptionBudget_le_ownerException
#print axioms indexed_owner_scheduled_conditioned_run

end CurrentAdditive.DeterministicIndexedMatrix.Sources
