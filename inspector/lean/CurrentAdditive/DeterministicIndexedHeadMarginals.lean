import CurrentAdditive.DeterministicIndexedCoordinates

/-! The exact one-position source laws at each of the three nested,
indexed calls of the v27 construction. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.SourceMatrix

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

namespace Sources

theorem gamma_head_pushes (hD : 1 ≤ D) (i : Fin q₁) :
    src.gamma.law.toFiniteLaw.PushesTo μY.toFiniteLaw
      (fun γ => head (gammaWord src γ) i) := by
  simpa only [gammaWord, head] using
    codeSource_coordinate_pushes μY src.gamma hD
      (⟨i, by omega⟩ : Fin (q₁ + s + 1))

theorem inner_position_pushes (hD : 1 ≤ D) (j : Fin q₂) :
    src.inner.law.toFiniteLaw.PushesTo
      (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
      (fun z => src.inner.decode z j) :=
  codeSource_coordinate_pushes _ src.inner hD j

theorem outer_position_pushes (hD : 1 ≤ D) (p : Fin s) :
    src.outer.law.toFiniteLaw.PushesTo
      (((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw)
      (fun js => src.outer.decode js p) :=
  codeSource_coordinate_pushes _ src.outer hD p

end Sources

end CurrentAdditive.DeterministicIndexedMatrix
