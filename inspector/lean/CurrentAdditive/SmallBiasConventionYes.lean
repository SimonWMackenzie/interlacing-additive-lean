import CurrentAdditive.SmallBiasTableSize

/-!
# YES budgets for every v27 communication convention on printed bits

Source: v27 `sections/07-yao.tex`, `yao:comparison` and `yao:bpp`.
The same balanced-colouring Alice-start protocol gives upper bounds for
free starter and receiver output, and transpose transfers it to Bob-start.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

/-- All three convention variants retain the literal YES budget `B` for
the same physical pair-labelled matrix (transposed for Bob-start). -/
theorem balanced_yes_printed_pair_conventions
    {V : Type} {E : Type*} [Fintype V]
    (b t d modulus : ℕ) (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (colour : V → Fin (2 ^ t))
    (hbalanced : ∀ e c, 2 ^ t - 1 ≤
      colourFiberCard (fun i => colour (edges e i)) c) :
    let M := matrix (placeEdges edges index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b))
      (printedPairFieldWord b t d modulus)
    Dfree M ≤ 2 * b + 4 * t + 2 ∧
    Yfree M ≤ 2 * b + 4 * t + 2 ∧
    Dalt .bob (fun y x => M x y) ≤ 2 * b + 4 * t + 2 := by
  dsimp
  let M := matrix (placeEdges edges index)
    (fullSelector (2 ^ (t - 1)) (2 ^ b))
    (printedPairFieldWord b t d modulus)
  have hA : Dalt .alice M ≤ 2 * b + 4 * t + 2 :=
    balanced_yes_printed_pair_field_matrix b t d modulus ht
      edges index colour hbalanced
  obtain ⟨hf, _, hr, _, htrans⟩ :=
    printed_pair_convention_bounds b t d modulus edges index
  change Dfree M ≤ Dalt .alice M at hf
  change Yfree M ≤ Dalt .alice M at hr
  change Dalt .bob (fun y x => M x y) = Dalt .alice M at htrans
  exact ⟨hf.trans hA, hr.trans hA, htrans.le.trans hA⟩

#print axioms CurrentAdditive.SmallBias.balanced_yes_printed_pair_conventions

end CurrentAdditive.SmallBias
