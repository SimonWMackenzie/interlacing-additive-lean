import EthInapproximability.CurrentPaper.MatrixWeightedColumnOuterDecode

/-!
# Four-way protected-row boundary and quotient stages

The current protected construction has full, template, vertex, and auxiliary
row supports.  The first three fixed unary cuts expose the group boundaries;
the final residual belongs to the fourth group.  Group-specific quotient
stages use the actual copy-count divisors supplied in unary.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedRowOuterDecode

open MatrixWeightedArithmetic MatrixIndexQuotient

def fullWidth (X cx : ℕ) := X * cx
def templateWidth (T ct : ℕ) := T * ct
def vertexWidth (V cv : ℕ) := V * cv
def auxiliaryWidth (B cb : ℕ) := B * cb

theorem first_cut_run (X T V B cx ct cv cb : ℕ)
    (i : Fin (X * cx + (T * ct + (V * cv + B * cb)))) :
    ∃ t ≤ 3 * min i.val (X * cx) + 4,
      MatrixUnaryCut.run t
        (MatrixUnaryCut.cfg (some .scan) (false,true)
          (List.replicate i.val true) (List.replicate (X * cx) true) [] []) =
      MatrixUnaryCut.cfg none (decide (X * cx ≤ i.val), false)
        (List.replicate (if i.val < X * cx then i.val else i.val - X * cx) true)
        (List.replicate (X * cx) true) [] [] :=
  MatrixUnaryCut.cut_run _ _

theorem second_cut_run (X T V B cx ct cv cb : ℕ)
    (i : Fin (X * cx + (T * ct + (V * cv + B * cb)))) :
    let residual := i.val - X * cx
    ∃ t ≤ 3 * min residual (T * ct) + 4,
      MatrixUnaryCut.run t
        (MatrixUnaryCut.cfg (some .scan) (false,true)
          (List.replicate residual true) (List.replicate (T * ct) true) [] []) =
      MatrixUnaryCut.cfg none (decide (T * ct ≤ residual), false)
        (List.replicate (if residual < T * ct then residual else residual - T * ct) true)
        (List.replicate (T * ct) true) [] [] :=
  MatrixUnaryCut.cut_run _ _

theorem third_cut_run (X T V B cx ct cv cb : ℕ)
    (i : Fin (X * cx + (T * ct + (V * cv + B * cb)))) :
    let residual := i.val - X * cx - T * ct
    ∃ t ≤ 3 * min residual (V * cv) + 4,
      MatrixUnaryCut.run t
        (MatrixUnaryCut.cfg (some .scan) (false,true)
          (List.replicate residual true) (List.replicate (V * cv) true) [] []) =
      MatrixUnaryCut.cfg none (decide (V * cv ≤ residual), false)
        (List.replicate (if residual < V * cv then residual else residual - V * cv) true)
        (List.replicate (V * cv) true) [] [] :=
  MatrixUnaryCut.cut_run _ _

/-- The full-support branch is the first component of `decodeRow`. -/
theorem full_branch (X T V B cx ct cv cb : ℕ)
    (i : Fin (X * cx + (T * ct + (V * cv + B * cb))))
    (h : i.val < X * cx) :
    decodeRow X T V B cx ct cv cb i =
      .inl (finProdFinEquiv.symm (⟨i.val, h⟩ : Fin (X * cx))) := by
  let x : Fin (X * cx) := ⟨i.val, h⟩
  have hi : i = Fin.castAdd (T * ct + (V * cv + B * cb)) x := Fin.ext rfl
  change (match finSumFinEquiv.symm i with
    | Sum.inl z => Sum.inl (finProdFinEquiv.symm z)
    | Sum.inr z => _) = _
  calc
    (match finSumFinEquiv.symm i with
      | Sum.inl z => Sum.inl (finProdFinEquiv.symm z)
      | Sum.inr z => _) = Sum.inl (finProdFinEquiv.symm x) := by
        rw [hi, finSumFinEquiv_symm_apply_castAdd]
    _ = _ := rfl

/-- The second interval is the template support. -/
theorem template_branch (X T V B cx ct cv cb : ℕ)
    (i : Fin (X * cx + (T * ct + (V * cv + B * cb))))
    (h₁ : X * cx ≤ i.val)
    (h₂ : i.val - X * cx < T * ct) :
    decodeRow X T V B cx ct cv cb i =
      .inr (.inl (finProdFinEquiv.symm
        (⟨i.val - X * cx, h₂⟩ : Fin (T * ct)))) := by
  let rest : Fin (T * ct + (V * cv + B * cb)) :=
    ⟨i.val - X * cx, by have hi := i.isLt; omega⟩
  let x : Fin (T * ct) := ⟨rest.val, h₂⟩
  have hi : i = Fin.natAdd (X * cx) rest := by
    apply Fin.ext
    dsimp [rest]
    omega
  have hr : rest = Fin.castAdd (V * cv + B * cb) x := Fin.ext rfl
  unfold decodeRow
  conv_lhs =>
    rw [hi, finSumFinEquiv_symm_apply_natAdd]
    simp only
    rw [hr, finSumFinEquiv_symm_apply_castAdd]

/-- The third interval is the vertex support. -/
theorem vertex_branch (X T V B cx ct cv cb : ℕ)
    (i : Fin (X * cx + (T * ct + (V * cv + B * cb))))
    (h₁ : X * cx ≤ i.val)
    (h₂ : T * ct ≤ i.val - X * cx)
    (h₃ : i.val - X * cx - T * ct < V * cv) :
    decodeRow X T V B cx ct cv cb i =
      .inr (.inr (.inl (finProdFinEquiv.symm
        (⟨i.val - X * cx - T * ct, h₃⟩ : Fin (V * cv))))) := by
  let rest₁ : Fin (T * ct + (V * cv + B * cb)) :=
    ⟨i.val - X * cx, by have hi := i.isLt; omega⟩
  let rest₂ : Fin (V * cv + B * cb) :=
    ⟨rest₁.val - T * ct, by have hi := rest₁.isLt; omega⟩
  let x : Fin (V * cv) := ⟨rest₂.val, by dsimp [rest₂, rest₁]; exact h₃⟩
  have hi : i = Fin.natAdd (X * cx) rest₁ := by
    apply Fin.ext
    dsimp [rest₁]
    omega
  have hr₁ : rest₁ = Fin.natAdd (T * ct) rest₂ := by
    apply Fin.ext
    dsimp [rest₂, rest₁]
    omega
  have hr₂ : rest₂ = Fin.castAdd (B * cb) x := Fin.ext rfl
  unfold decodeRow
  conv_lhs =>
    rw [hi, finSumFinEquiv_symm_apply_natAdd]
    simp only
    rw [hr₁, finSumFinEquiv_symm_apply_natAdd]
    simp only
    rw [hr₂, finSumFinEquiv_symm_apply_castAdd]

/-- The residual fourth interval is the auxiliary support. -/
theorem auxiliary_branch (X T V B cx ct cv cb : ℕ)
    (i : Fin (X * cx + (T * ct + (V * cv + B * cb))))
    (h₁ : X * cx ≤ i.val)
    (h₂ : T * ct ≤ i.val - X * cx)
    (h₃ : V * cv ≤ i.val - X * cx - T * ct) :
    decodeRow X T V B cx ct cv cb i =
      .inr (.inr (.inr (finProdFinEquiv.symm
        (⟨i.val - X * cx - T * ct - V * cv, by
          omega⟩ : Fin (B * cb))))) := by
  let rest₁ : Fin (T * ct + (V * cv + B * cb)) :=
    ⟨i.val - X * cx, by have hi := i.isLt; omega⟩
  let rest₂ : Fin (V * cv + B * cb) :=
    ⟨rest₁.val - T * ct, by have hi := rest₁.isLt; omega⟩
  let x : Fin (B * cb) :=
    ⟨rest₂.val - V * cv, by have hi := rest₂.isLt; omega⟩
  have hi : i = Fin.natAdd (X * cx) rest₁ := by
    apply Fin.ext
    dsimp [rest₁]
    omega
  have hr₁ : rest₁ = Fin.natAdd (T * ct) rest₂ := by
    apply Fin.ext
    dsimp [rest₂, rest₁]
    omega
  have hr₂ : rest₂ = Fin.natAdd (V * cv) x := by
    apply Fin.ext
    dsimp [x, rest₂, rest₁]
    omega
  unfold decodeRow
  conv_lhs =>
    rw [hi, finSumFinEquiv_symm_apply_natAdd]
    simp only
    rw [hr₁, finSumFinEquiv_symm_apply_natAdd]
    simp only
    rw [hr₂, finSumFinEquiv_symm_apply_natAdd]

/-- Once a branch's residual ordinal is known, this fixed quotient stage
returns the support label and its within-label copy digit. -/
theorem group_split_run (labels copies : ℕ) (i : Fin (labels * copies)) :
    ∃ t ≤ 10 * i.val + 3 * copies + 6,
      run t (cfg (some start) initial
        (List.replicate i.val true) (List.replicate copies true)
        [] [] [] [] [] []) =
      cfg (some clear) initial
        (List.replicate i.val true) (List.replicate copies true)
        [] [] []
        (List.replicate (finProdFinEquiv.symm i).2.val true)
        (List.replicate (finProdFinEquiv.symm i).1.val true) [] := by
  have hc := MatrixWeightedColumnOuterDecode.pair_coordinates labels copies i
  simpa only [hc.1, hc.2] using MatrixIndexSplit.split_run i.val copies

end EthInapproximability.CurrentPaper.MatrixWeightedRowOuterDecode
