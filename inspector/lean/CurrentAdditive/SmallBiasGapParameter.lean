import CurrentAdditive.SmallBiasUniformMatrix

/-!
# Fixed-gap parameter for the finite mathematical v27 matrix

Source: v27 `sections/07-yao.tex`, proof of `yao:main`:
`t=max{4,ceil((g+6)/2)}`. This proves the integer gap calculation and
applies the same matrix theorem. External source reduction and physical
printing are separate from this parameter step.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

/-- Integer form of the source's choice of `t` for requested gap `g`. -/
def v27GapParameter (g : ℕ) : ℕ := max 4 ((g + 7) / 2)

theorem v27GapParameter_ge_four (g : ℕ) : 4 ≤ v27GapParameter g := by
  unfold v27GapParameter
  omega

theorem v27GapParameter_gap (g : ℕ) :
    g ≤ 2 * v27GapParameter g - 6 := by
  unfold v27GapParameter
  omega

/-- For the source's fixed-gap choice, the exact matrix has the YES
budget and an NO bound at least `B+g`. Field size still depends only on
public parameters, and its labelled count has the displayed bound. -/
theorem exists_fixed_gap_v27_field_matrix
    {V E : Type*} [Fintype V]
    (g b : ℕ)
    (edges : E → Fin (2 ^ (v27GapParameter g) *
      2 ^ (v27GapParameter g)) ↪ V)
    (index : E ↪ Fin (2 ^ b)) :
    ∃ d : ℕ, ∃ hd : 0 < d,
      (((2 ^ d) ^ 2 : ℕ) : ℚ) <
        4 * ((2 ^ (v27GapParameter g) * 2 ^ (v27GapParameter g) + 1 : ℕ) : ℚ) ^ 2 *
          ((2 : ℚ) ^
            (12 * 2 ^ (v27GapParameter g) * (v27GapParameter g) +
              3 * (v27GapParameter g) + 1)) ^ 2 *
          ((2 : ℚ) ^ b) ^ (8 * 2 ^ (v27GapParameter g) + 4) ∧
      (∀ colour : V → Fin (2 ^ (v27GapParameter g)),
        (∀ e c, 2 ^ (v27GapParameter g) - 1 ≤
          colourFiberCard (fun i => colour (edges e i)) c) →
        Dalt .alice (matrix (placeEdges edges index)
          (fullSelector (2 ^ ((v27GapParameter g) - 1)) (2 ^ b))
          (indexedFieldWord b (v27GapParameter g) d hd
            (binaryBasis d hd))) ≤
          2 * b + 4 * (v27GapParameter g) + 2) ∧
      ((∀ colour : V → Fin (2 ^ (2 ^ (v27GapParameter g) - 1)),
          ∃ e c, ∀ i, colour (edges e i) = c) →
        (2 * b + 4 * (v27GapParameter g) + 2) + g ≤
          Dalt .alice (matrix (placeEdges edges index)
            (fullSelector (2 ^ ((v27GapParameter g) - 1)) (2 ^ b))
            (indexedFieldWord b (v27GapParameter g) d hd
              (binaryBasis d hd)))) := by
  let t := v27GapParameter g
  obtain ⟨d, hd, hsize, hyes, hno⟩ :=
    exists_uniform_v27_field_matrix b t (v27GapParameter_ge_four g)
      edges index
  refine ⟨d, hd, hsize, hyes, ?_⟩
  intro hn
  have hg := v27GapParameter_gap g
  have ht : 4 ≤ t := v27GapParameter_ge_four g
  have hbound := hno hn
  change (2 * b + 4 * t + 2) + g ≤
    Dalt .alice (matrix (placeEdges edges index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b))
      (indexedFieldWord b t d hd (binaryBasis d hd)))
  omega

#print axioms CurrentAdditive.SmallBias.v27GapParameter_gap
#print axioms CurrentAdditive.SmallBias.exists_fixed_gap_v27_field_matrix

end CurrentAdditive.SmallBias
