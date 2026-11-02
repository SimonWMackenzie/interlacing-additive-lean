import CurrentAdditive.LiteralFirstProductionV35
import CurrentAdditive.IndexedGraphUpper

/-! The finite source-data part of the v35 first-passing schedule.  The old
`IndexedSemanticIteration.Schedule` bundled an unrelated 2004 cutoff into its
record.  The actual source indexing requires only these three fields. -/

namespace FiniteV35Continuation

open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.PublicScheduleExactAdmissibility
open CurrentAdditive.PublicScheduleLiteralFirstPassing

structure LiteralSourceSchedule (V E : Type*) [Fintype V] [Fintype E]
    (L : ℕ) where
  item_large : 3 ≤ s L
  order : Paper2.SourceConstruction.Items (s L) V ≃
    Fin (Fintype.card (Paper2.SourceConstruction.Items (s L) V))
  rep : ℕ
  repetition : q₂ L = Paper2.SourceItems.sourceQ0 (Fin (4*s L)) E * rep

theorem repetition_of_graph_width
    {V E : Type*} [Fintype V] [Fintype E]
    (L Δ C : ℕ) (γ : ℚ)
    (hadm : Admissible L Δ (Fintype.card V) (Fintype.card E) C γ) :
    ∃ rep : ℕ, q₂ L =
      Paper2.SourceItems.sourceQ0 (Fin (4*s L)) E * rep := by
  let k := Nat.clog 2 (12*s L*Fintype.card E)
  have hcard : Fintype.card
      (Paper2.SourceItems.Coord (Fin (4*s L)) E) =
        12*s L*Fintype.card E := by
    rw [Paper2.SourceItems.card_coord]
    simp only [Fintype.card_fin]
    ring
  have hq₀ : Paper2.SourceItems.sourceQ0 (Fin (4*s L)) E = 2^k := by
    dsimp [Paper2.SourceItems.sourceQ0,
      Paper2.SourcePadding.powTwoCeil, k]
    rw [hcard]
  have hle : 2^k ≤ 2^(4*L) := by
    simpa only [k, hq₀, CurrentAdditive.DeterministicParameters.q₂_eq_pow]
      using hadm.graph_width
  have hk : k ≤ 4*L :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle
  have hdiv : Paper2.SourceItems.sourceQ0 (Fin (4*s L)) E ∣ q₂ L := by
    rw [hq₀, CurrentAdditive.DeterministicParameters.q₂_eq_pow]
    exact pow_dvd_pow 2 hk
  exact ⟨q₂ L / Paper2.SourceItems.sourceQ0 (Fin (4*s L)) E,
    (Nat.mul_div_cancel' hdiv).symm⟩

theorem literal_source_schedule_of_admissible
    {V E : Type*} [Fintype V] [Fintype E]
    (L Δ C : ℕ) (γ : ℚ)
    (hadm : Admissible L Δ (Fintype.card V) (Fintype.card E) C γ) :
    Nonempty (LiteralSourceSchedule V E L) := by
  obtain ⟨rep, hq⟩ := repetition_of_graph_width L Δ C γ hadm
  exact ⟨{
    item_large := by have hs := hadm.rung_size; omega
    order := Fintype.equivFin _
    rep := rep
    repetition := hq
  }⟩

theorem first_literal_source_schedule
    (v e : ℕ) (Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (he : 0 < e)
    (hcount : 2*e ≤ Δ*v) :
    Nonempty (LiteralSourceSchedule (Fin v) (Fin e)
      (exactPublicLog v e Δ γ)) := by
  let L := exactPublicLog v e Δ γ
  have hadm := (first_literal_production_schedule L v e Δ γ
    hΔ hγ he hcount rfl).2.1
  apply literal_source_schedule_of_admissible L Δ sourceC128Ceil γ
  simpa only [Fintype.card_fin] using hadm

#print axioms repetition_of_graph_width
#print axioms literal_source_schedule_of_admissible
#print axioms first_literal_source_schedule

end FiniteV35Continuation
