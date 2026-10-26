import CurrentAdditive.QuarticSourceAmplifierLower
import Paper2.SourceIteration

/-!
# Finite NO induction on the actual recursive graph source

Every successor step invokes the checked finite NO amplifier theorem on
the preceding actual matrix and positive rational law pair. Public
finite guards remain explicit; no generic desired amplifier certificate
is supplied to this induction.
-/

namespace Paper2.SourceIterationLower

open SourceMatrix SourceLawBinding SourceProfileParameters SourceDeficiency
  SourceSurvivingCollisions Workspace.Types.CommComplexity

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Exact NO cost and unchanged three-rung profile at every finite stage
of the specified seed/graph construction and its actual recursive laws. -/
theorem selected_no_iteration27
    {V E : Type} [Fintype V] [Nonempty V] [Fintype E]
    (L : ℕ) (hL : 16 ≤ L)
    (order : SourceConstruction.Items (width L) V ≃
      Fin (Fintype.card (SourceConstruction.Items (width L) V)))
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (rep Δ : ℕ) (hΔ : 0 < Δ)
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) E * rep)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (hscale : 4 * (width L : ℝ) ^ 2 * rho L ≤ 1)
    (hcountSource : 8 * (width L : ℝ) * (width L - 2 : ℕ) ≤
      witnessDensity γ * outerWidth L / 16)
    (w r Q q : ℕ) [NeZero w] [NeZero Q]
    (hw : w = 2 ^ r) (hw2 : 2 ≤ w) (hQ : Q = 2 ^ q)
    (ηq : ℚ)
    (hηq : (ηq : ℝ) = deletionAllowance (V := V) (E := E) γ Δ (width L))
    (hquarter : CurrentAdditive.QuarticSchedule.quarterCheck27Prop w Q ηq)
    (hsmall : 2 * (w : ℝ) ^ 2 * x L ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) /
        (16 * (127 / 128 : ℝ)))
    (hfirst : 4 * (1 / 256 : ℝ) * w * outerWidth L * x L ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) / 32)
    (hlast : 4 * (1 / 256 : ℝ) * w / outerWidth L ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) / 32)
    (hKcheck :
      (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
        (r + 2) * width L) *
      CurrentAdditive.QuarticSchedule.E27 Q ηq ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) * w / 16)
    (hxsmall : ((w : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1)
    (hstar : 4 * RestorationCoverParameters.tStar Q ≤ w)
    (hsmallwx : (w : ℝ) * x L ≤ 1 / 10000)
    (hmargin : 2 * w * x L +
      deletionAllowance (V := V) (E := E) γ Δ (width L) /
        (16 * (127 / 128 : ℝ)) < 1)
    (hbridge : 80 * (L : ℝ) ≤ (Q : ℝ) *
      (deletionAllowance (V := V) (E := E) γ Δ (width L) /
        (16 * (w : ℝ))))
    (ξ : SourceIteration.FixedTails L (width L) (width L - 2)
      (outerWidth L) w Q V) (k : ℕ) :
    let h := exponent L + outerExponent L + exponent L + r + q
    let H := LookupSeed.exponent L + 1 + k * (h + 1)
    let μ₀ := LookupSeed.rowLaw (LookupSeed.width L)
    let ν₀ := LookupSeed.columnLaw (LookupSeed.width L)
      (Nat.two_pow_pos (LookupSeed.exponent L))
    let laws := RecursiveSampling.laws (V := V) (q₁ := width L - 2)
      (q₂ := outerWidth L) (s := width L) (w := w) (Q := Q)
      (SourceProfiles.width_ge_four L) μ₀ ν₀
    D (SourceIteration.matrix (q₁ := width L - 2)
      L order edge (by have := SourceProfiles.width_ge_four L; omega)
      rep hq ξ k) = H ∧
    RestrictionProfile
      (SourceIteration.matrix (q₁ := width L - 2)
        L order edge (by have := SourceProfiles.width_ge_four L; omega)
        rep hq ξ k)
      (laws k).1.toFiniteLaw (laws k).2.toFiniteLaw (rho L) (H : ℤ) := by
  classical
  letI : NeZero w := ⟨by rw [hw]; positivity⟩
  letI : NeZero Q := ⟨by rw [hQ]; positivity⟩
  let μ₀ := LookupSeed.rowLaw (LookupSeed.width L)
  let ν₀ := LookupSeed.columnLaw (LookupSeed.width L)
    (Nat.two_pow_pos (LookupSeed.exponent L))
  let laws := RecursiveSampling.laws (V := V) (q₁ := width L - 2)
    (q₂ := outerWidth L) (s := width L) (w := w) (Q := Q)
    (SourceProfiles.width_ge_four L) μ₀ ν₀
  let h := exponent L + outerExponent L + exponent L + r + q
  let Fk := SourceIteration.matrix (q₁ := width L - 2)
    L order edge (by have := SourceProfiles.width_ge_four L; omega) rep hq ξ
  have hseed := LookupSeed.selected_seed_finite L
  have hd0 : 3 ≤ LookupSeed.exponent L + 1 := by
    have hwidth := LookupSeed.width_admissible L
    have h2 : 2 ^ (LookupSeed.exponent L) = LookupSeed.width L := rfl
    by_contra hn
    have he : LookupSeed.exponent L ≤ 1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) he
    rw [h2] at hp
    omega
  induction k with
  | zero =>
    change D (LookupSeed.matrix (LookupSeed.width L)) = _ ∧
      RestrictionProfile (LookupSeed.matrix (LookupSeed.width L))
        μ₀.toFiniteLaw ν₀.toFiniteLaw (rho L) _
    constructor
    · simpa only [Nat.zero_mul, Nat.add_zero] using hseed.1
    · simpa only [μ₀, ν₀, rho, Nat.zero_mul, Nat.add_zero,
        Nat.cast_add, Nat.cast_one] using hseed.2.1
  | succ k ih =>
    let dk := LookupSeed.exponent L + 1 + k * (h + 1)
    let Ck := dk + exponent L + outerExponent L + exponent L + 1
    have hdk : 3 ≤ dk := by dsimp [dk]; omega
    have hCk : 4 ≤ Ck := by dsimp [Ck]; omega
    have hCeq : Ck - 1 = dk + exponent L + outerExponent L + exponent L := by
      dsimp [Ck]
    have hprevD : D (Fk k) = dk := ih.1
    have hprevP : RestrictionProfile (Fk k)
        (laws k).1.toFiniteLaw (laws k).2.toFiniteLaw (rho L) (dk : ℤ) := ih.2
    have hstep := SourceAmplifierLower.source_successor_no_cost_profile27
      (laws k).1 (laws k).2 (Fk k) L dk hdk hprevD hprevP
      hinner houter hwide href order edge loopless rep Δ hΔ hq hdegree
      γ hγ hE gap hscale hcountSource (ξ k)
      w r Q q Ck hw hw2 hQ hCk hCeq ηq hηq hquarter hsmall hfirst hlast
      hKcheck hxsmall hstar hsmallwx hmargin (by omega : 1 ≤ L) hbridge
    have hlaws := SourceAmplifierLower.successor_laws_match_recursive27 (V := V)
      (laws k).1 (laws k).2 L w Q
    have hnum : dk + (exponent L + outerExponent L + exponent L + r + q) + 1 =
        LookupSeed.exponent L + 1 + (k + 1) * (h + 1) := by
      dsimp [dk, h]
      simp only [Nat.succ_mul]
      omega
    change D (Fk (k + 1)) = _ ∧ RestrictionProfile (Fk (k + 1))
      (laws (k + 1)).1.toFiniteLaw (laws (k + 1)).2.toFiniteLaw (rho L) _
    constructor
    · change D (SourceMatrix.successor (Fk k)
        (SourceConstruction.activity order edge
          (by have := SourceProfiles.width_ge_four L; omega) rep hq)
        (ξ k) w Q) = _
      have hstepD := hstep.1
      rw [← hnum]
      exact hstepD
    · have hstepP := hstep.2
      have hrowlaw : (laws (k + 1)).1.toFiniteLaw =
          ((FiniteLaw.uniformFin w (NeZero.pos w)).prod
            (matrixRowLaw (laws k).2 (width L - 2) (outerWidth L)
              (width L)).toFiniteLaw).iid Q := by
        simpa only [laws, RecursiveSampling.laws] using hlaws.1
      have hcollaw : (laws (k + 1)).2.toFiniteLaw =
          (FiniteLaw.uniformFin Q (NeZero.pos Q)).prod
            ((matrixColumnLaw (V := V) (laws k).1 (width L - 2)
              (outerWidth L) (width L) (SourceProfiles.width_ge_four L)).toFiniteLaw.iid w) := by
        simpa only [laws, RecursiveSampling.laws] using hlaws.2
      rw [hrowlaw, hcollaw, ← hnum]
      exact hstepP

end Paper2.SourceIterationLower

#print axioms Paper2.SourceIterationLower.selected_no_iteration27
