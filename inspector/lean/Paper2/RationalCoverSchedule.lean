import Paper2.SourceRationalSchedule
import Paper2.RestorationPublicCovers
import Paper2.ReferenceOwners

/-!
# Exact rational forms of the remaining Appendix C cover checks

The source rational schedule already supplies eta, delta_U, and public Q.
This file replaces only the remaining real ceilings and comparison in the
restoration cover/exceptional-mass checks by exact rational calculations.
-/

namespace Paper2.RationalCoverSchedule

open SourceProfileParameters SourceRationalScheduleScratch

/-- The exact rational ceiling for v12 `B₁=⌈(bθ+1)/η⌉`. -/
def B1 (Q : ℕ) (η : ℚ) : ℕ :=
  Nat.ceil (((RestorationCoverParameters.b Q + 1 : ℕ) : ℚ) / η)

theorem B1_real (Q : ℕ) (η : ℚ) :
    B1 Q η = RestorationCoverParameters.B1 Q (η : ℝ) := by
  have hc : Nat.ceil (((((RestorationCoverParameters.b Q + 1 : ℕ) : ℚ) / η : ℚ) : ℝ)) =
      Nat.ceil (((RestorationCoverParameters.b Q + 1 : ℕ) : ℚ) / η) := by
    rw [← Int.ceil_toNat, ← Int.ceil_toNat, Rat.ceil_cast]
  unfold B1 RestorationCoverParameters.B1
  rw [← hc]
  congr 1
  push_cast
  rfl

/-- The exact `e₀`, retaining the small-set dyadic offset in the owner. -/
def e0 (Q : ℕ) (η : ℚ) : ℕ :=
  RestorationCovers.exceptionBudget
    (RestorationCoverParameters.B0 Q) (B1 Q η)
    (RestorationCoverParameters.B2 Q)
    (RestorationCoverParameters.tExponent Q)

theorem e0_real (Q : ℕ) (η : ℚ) :
    e0 Q η = RestorationPublicCovers.e0 Q (η : ℝ) := by
  simp only [e0, RestorationPublicCovers.e0, B1_real]

/-- The exact exceptional-destination ceiling `E=⌈16e₀/7⌉`. -/
def E (Q : ℕ) (η : ℚ) : ℕ :=
  Nat.ceil ((16 * (e0 Q η : ℚ)) / 7)

theorem E_real (Q : ℕ) (η : ℚ) :
    E Q η = ReferenceOwners.exceptionBudget
      (RestorationPublicCovers.e0 Q (η : ℝ)) := by
  have hc : Nat.ceil (((16 * (e0 Q η : ℚ) / 7 : ℚ) : ℝ)) =
      Nat.ceil ((16 * (e0 Q η : ℚ)) / 7) := by
    rw [← Int.ceil_toNat, ← Int.ceil_toNat, Rat.ceil_cast]
  unfold E ReferenceOwners.exceptionBudget
  rw [← hc, ← e0_real]
  congr 1
  push_cast
  rfl

/-- Decidable integer form of the Appendix C exceptional-count test. -/
def quarterCheck (w Q : ℕ) (η : ℚ) : Prop := 4 * E Q η ≤ w

instance (w Q : ℕ) (η : ℚ) : Decidable (quarterCheck w Q η) :=
  by unfold quarterCheck; infer_instance

theorem quarterCheck_real (w Q : ℕ) (η : ℚ) :
    quarterCheck w Q η ↔
      4 * ReferenceOwners.exceptionBudget
        (RestorationPublicCovers.e0 Q (η : ℝ)) ≤ w := by
  simp only [quarterCheck, E_real]

/-- `K_*=1024 μ B₂(r+2)s`, where the frozen source fixes `μ=1/256`. -/
def Kstar (L r Q : ℕ) : ℚ :=
  1024 * (1 / 256) * RestorationCoverParameters.B2 Q *
    (r + 2) * width L

theorem Kstar_real (L r Q : ℕ) :
    (Kstar L r Q : ℝ) =
      1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
        (r + 2) * width L := by
  simp only [Kstar, Rat.cast_mul, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_add]

/-- Decidable rational version of the actual Appendix C `K_*E` test. -/
def kCheck (L r w Q : ℕ) (η : ℚ) : Prop :=
  Kstar L r Q * E Q η ≤ η * w / 16

instance (L r w Q : ℕ) (η : ℚ) : Decidable (kCheck L r w Q η) :=
  by unfold kCheck; infer_instance

theorem kCheck_real (L r w Q : ℕ) (η : ℚ) :
    kCheck L r w Q η ↔
      (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
        (r + 2) * width L) *
      ReferenceOwners.exceptionBudget (RestorationPublicCovers.e0 Q (η : ℝ)) ≤
        (η : ℝ) * w / 16 := by
  unfold kCheck
  rw [← Kstar_real, ← E_real]
  exact_mod_cast (Iff.rfl :
    Kstar L r Q * E Q η ≤ η * w / 16 ↔
      Kstar L r Q * E Q η ≤ η * w / 16)

variable {V Edges : Type*} [Fintype V] [Nonempty V] [Fintype Edges]

theorem source_B1_real (L Q : ℕ) (γ : ℚ) (Δ : ℕ) :
    B1 Q (eta (V := V) (E := Edges) L γ Δ) =
      RestorationCoverParameters.B1 Q
        (SourceSurvivingCollisions.deletionAllowance (V := V) (E := Edges)
          (γ : ℝ) Δ (width L)) := by
  rw [B1_real, eta_cast]

/-- Bind the rational cover count to the actual graph-source allowance. -/
theorem source_e0_real (L Q : ℕ) (γ : ℚ) (Δ : ℕ) :
    e0 Q (eta (V := V) (E := Edges) L γ Δ) =
      RestorationPublicCovers.e0 Q
        (SourceSurvivingCollisions.deletionAllowance (V := V) (E := Edges)
          (γ : ℝ) Δ (width L)) := by
  rw [e0_real, eta_cast]

theorem source_E_real (L Q : ℕ) (γ : ℚ) (Δ : ℕ) :
    E Q (eta (V := V) (E := Edges) L γ Δ) =
      ReferenceOwners.exceptionBudget (RestorationPublicCovers.e0 Q
        (SourceSurvivingCollisions.deletionAllowance (V := V) (E := Edges)
          (γ : ℝ) Δ (width L))) := by
  rw [E_real, eta_cast]

theorem source_quarterCheck_real (L w Q : ℕ) (γ : ℚ) (Δ : ℕ) :
    quarterCheck w Q (eta (V := V) (E := Edges) L γ Δ) ↔
      4 * ReferenceOwners.exceptionBudget (RestorationPublicCovers.e0 Q
        (SourceSurvivingCollisions.deletionAllowance (V := V) (E := Edges)
          (γ : ℝ) Δ (width L))) ≤ w := by
  rw [quarterCheck_real, eta_cast]

/-- The rational calculation is exactly the real guard consumed by
restoration, with no assumption that the guard passes. -/
theorem source_kCheck_real (L r w Q : ℕ) (γ : ℚ) (Δ : ℕ) :
    kCheck L r w Q (eta (V := V) (E := Edges) L γ Δ) ↔
      (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
        (r + 2) * width L) *
      ReferenceOwners.exceptionBudget (RestorationPublicCovers.e0 Q
        (SourceSurvivingCollisions.deletionAllowance (V := V) (E := Edges)
          (γ : ℝ) Δ (width L))) ≤
        SourceSurvivingCollisions.deletionAllowance (V := V) (E := Edges)
          (γ : ℝ) Δ (width L) * w / 16 := by
  rw [kCheck_real, eta_cast]

end Paper2.RationalCoverSchedule

#print axioms Paper2.RationalCoverSchedule.B1_real
#print axioms Paper2.RationalCoverSchedule.e0_real
#print axioms Paper2.RationalCoverSchedule.E_real
#print axioms Paper2.RationalCoverSchedule.quarterCheck_real
#print axioms Paper2.RationalCoverSchedule.kCheck_real
#print axioms Paper2.RationalCoverSchedule.source_B1_real
#print axioms Paper2.RationalCoverSchedule.source_quarterCheck_real
#print axioms Paper2.RationalCoverSchedule.source_kCheck_real
