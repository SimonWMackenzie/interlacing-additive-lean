import CurrentAdditive.QuarticSourceAmplifierFullScope
import CurrentAdditive.QuarticScheduleGuards

/-! Full source quantifier scope at graph-only actual v27 parameters. -/

namespace Paper2.SourceAmplifierScheduledFullScope

open SourceMatrix SourceLawBinding SourceProfileParameters SourceDeficiency
  SourceSurvivingCollisions Workspace.Types.CommComplexity RankLeaves
open CurrentAdditive.RandomizedSchedule

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩
local instance (n : ℕ) [NeZero n] : Nonempty (Fin n) :=
  Fin.pos_iff_nonempty.mp (NeZero.pos n)

theorem scheduled_source_successor_joint27
    {n m : ℕ} [NeZero n] (hn : 0 < n)
    {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (L : ℕ)
    (order : SourceConstruction.Items (width L) (Fin n) ≃
      Fin (Fintype.card (SourceConstruction.Items (width L) (Fin n))))
    (edge : Fin m → Bool → Fin n)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (Δ : ℕ) (hΔ : 0 < Δ)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℚ) (hγ : 0 < γ) (hm : 0 < m)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (ξ₀ : Tail (width L) Y) :
    let rep := SourceRepetitionScratch.sourceRep L (Fin m)
    let w := width27 L
    let Q := Q27 (V := Fin n) (E := Fin m) L γ Δ
    let h := overhead27 (V := Fin n) (E := Fin m) L Δ γ
    let S := SourceMatrix.successor (q₁ := width L - 2) F
      (SourceConstruction.activity order edge
        (by have := SourceProfiles.width_ge_four L; omega) rep
        (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep L (Fin m) hc.1))
      ξ₀ w Q
    D S ≤ D F + h + 1 ∧
    (∀ colour : Fin n → Fin 3,
      (∀ e, colour (edge e false) ≠ colour (edge e true)) →
      D S ≤ D F + h) ∧
    (realMatrix S).rank ≤ 2 ^ h * (realMatrix F).rank ∧
    (∀ d : ℕ, 3 ≤ d → D F = d →
      RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ) →
      (∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
        ((Finset.univ.filter (fun e => colour (edge e false) =
          colour (edge e true))).card : ℝ)) →
      D S = d + h + 1 ∧
      RestrictionProfile S
        (((FiniteLaw.uniformFin w (by unfold w width27; positivity)).prod
          (matrixRowLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw).iid Q)
        ((FiniteLaw.uniformFin Q (by exact RestorationPublicQScratch.publicQ_pos _ _)).prod
          ((matrixColumnLaw (V := Fin n) μ (width L - 2) (outerWidth L)
            (width L) (SourceProfiles.width_ge_four L)).toFiniteLaw.iid w))
        (rho L) ((d + h + 1 : ℕ) : ℤ)) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let G := CurrentAdditive.QuarticScheduleGuards.guards_of_checks27
    (n := n) (m := m) L Δ γ hγ hΔ hm hc
  let rep := SourceRepetitionScratch.sourceRep L (Fin m)
  have hrep : 1 ≤ rep := SourceRepetitionScratch.sourceRep_pos L (Fin m) hc.1
  let hq := SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep L (Fin m) hc.1
  have hγR : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hjoint := SourceAmplifierFullScope.source_successor_full_scope27
    μ ν F L G.hinner G.houter G.hwide G.href
    order edge loopless rep Δ hrep hΔ hq hdegree hincident
    (γ : ℝ) hγR (by simpa using hm) G.hscale G.hcountSource ξ₀
    (width27 L) (4 * RestorationWidthScheduleScratch.ell L)
    (Q27 (V := Fin n) (E := Fin m) L γ Δ)
    (q27 (V := Fin n) (E := Fin m) L γ Δ)
    G.hw G.hw2 G.hQ
    (SourceRationalScheduleScratch.eta (V := Fin n) (E := Fin m) L γ Δ)
    G.hηq G.hquarter G.hsmall G.hfirst G.hlast
    (by simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using G.hKcheck)
    G.hxsmall G.hstar G.hsmallwx G.hmargin
    (by exact le_trans (by decide : 1 ≤ 16) G.hL) G.hbridge
  simpa only [overhead27, Fintype.card_fin] using hjoint

#print axioms scheduled_source_successor_joint27

end Paper2.SourceAmplifierScheduledFullScope
