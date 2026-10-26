import CurrentAdditive.GeneratedWAlignmentOwnerCost

/-! Realize a short restriction of the original indexed W by an actual
minimum-cost protocol on precisely its retained subtype inputs. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Workspace.Types.CommComplexity Workspace.Types.Protocol

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

theorem indexed_W_short_protocol_from_restriction
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Fin w × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (H : ℕ)
    (hshort : Paper2.Compression.restrictionD
      (W src streams R₀ activity ξ₀) Yevent R ≤ H) :
    ∃ P : Protocol Yevent R Bool,
      P.cost ≤ H ∧
      P.Computes (fun t row => W src streams R₀ activity ξ₀ t.val row.val) := by
  classical
  let f : Yevent → R → Bool :=
    fun t row => W src streams R₀ activity ξ₀ t.val row.val
  have hne : (AchievableCosts f).Nonempty :=
    Workspace.UpperBound.AchievableCosts_nonempty f
  have hmem : D f ∈ AchievableCosts f := by
    simpa [D] using (Nat.sInf_mem hne)
  obtain ⟨P, hPc, hPcomp⟩ := hmem
  refine ⟨P, ?_, hPcomp⟩
  have hD : D f ≤ H := by
    simpa [f, Paper2.Compression.restrictionD] using hshort
  omega

#print axioms indexed_W_short_protocol_from_restriction

end CurrentAdditive.DeterministicIndexedMatrix.Sources
