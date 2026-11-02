import CurrentAdditive.GeneratedDeficientCount

/-!
The exact `x_cap` threshold transport in v27 `det:near-full`, I:311–324.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceDeficiencyTemplate

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- Under the paper's `x_cap ≤ 1/8`, fewer than `8*q₁` coordinates have
any original base-row block whose actual retained projection is below
`x_cap`. The strict inequality includes exactly the source's threshold. -/
theorem deficient_cap_card_lt
    (hD : 2 ≤ D) (K : Set src.inner.Label)
    (hKmass : (1 / 7 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K))
    (xcap : ℝ) (hxcap : xcap ≤ 1 / 8) :
    (Finset.univ.filter (fun α : Fin q₂ =>
      ∃ r : Fin q₁,
        μX.toFiniteLaw.prob (fun x =>
          projectedAt
            (fun t : Template q₁ q₂ X =>
              ∃ z ∈ K, src.inner.decode z = t) α (r, x)) < xcap)).card <
      8 * q₁ := by
  classical
  let capped : Finset (Fin q₂) := Finset.univ.filter (fun α =>
    ∃ r : Fin q₁, μX.toFiniteLaw.prob (fun x =>
      projectedAt (fun t : Template q₁ q₂ X =>
        ∃ z ∈ K, src.inner.decode z = t) α (r, x)) < xcap)
  let bad : Finset (Fin q₂) := Finset.univ.filter (fun α =>
    Deficient μX (fun t : Template q₁ q₂ X =>
      ∃ z ∈ K, src.inner.decode z = t) α)
  change capped.card < 8 * q₁
  have hsubset : capped ⊆ bad := by
    intro α hα
    obtain ⟨r, hr⟩ := (Finset.mem_filter.mp hα).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨r, lt_of_lt_of_le hr hxcap⟩⟩
  exact (Finset.card_le_card hsubset).trans_lt
    (deficient_coordinate_card_lt src hD K hKmass)

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.deficient_cap_card_lt
