import EthInapproximability.CurrentPaper.MatrixWeightedEntryController
import EthInapproximability.CurrentPaper.MatrixWeightedRawRead
import EthInapproximability.CurrentPaper.MatrixWeightedProtectedWriter
import EthInapproximability.CurrentPaper.MatrixWeightedRowOuterDecode

/-!
# Semantic parameters for the literal protected-entry controller

The finite controller consumes unary scalar words, a raw Stage--4 table, and
the public graph-item order word.  This file instantiates those inputs from
the frozen protected construction.  Subsequent address lemmas identify its
eight physical branch outputs with the two typed protected labels.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedEntrySemantic

open Construction MatrixStage4Codes MatrixStage4Digits MatrixWeightedTable
open MatrixWeightedArithmetic MatrixWeightedEntryController WeightedDuplication

variable {rx cy : ℕ}

/-- The actual, transposed-protected-matrix parameters supplied to the fixed
entry controller.  In particular `rawBits` is the literal Stage--4 source
table and `orderBits` serializes the public `ItemOrder`. -/
def actualInput (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx))
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) : Input :=
  { uniform := uniformCopies (Y := Fin cy) a s q
    fullBoundary := Fintype.card (RawColumns a s q (Fin cy)) *
      (182 * Fintype.card (SecondRows a s q (Fin cy)))
    fullDivisor := 182 * Fintype.card (SecondRows a s q (Fin cy))
    diagonalDivisor := 2 * Fintype.card (RawColumns a s q (Fin cy))
    nb := nb
    stagePrefixRows := s * L
    rx := rx
    nv := nv
    rawWidth := cols a s q cy
    wordBase := wordBase a s cy
    cy := cy
    s := s
    binBase := binBase a s q cy
    rowBoundary₁ := Fintype.card (RawRows s L nv nb (Fin rx)) *
      copies (rowSupport (RawRows s L nv nb (Fin rx))
        (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
        (AuxiliaryRows nb (Fin rx))) rowWeight 0
    rowBoundary₂ := Fintype.card (TemplateSupport.{0} s L) *
      copies (rowSupport (RawRows s L nv nb (Fin rx))
        (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
        (AuxiliaryRows nb (Fin rx))) rowWeight 1
    rowBoundary₃ := Fintype.card (VertexRows nv (Fin rx)) *
      copies (rowSupport (RawRows s L nv nb (Fin rx))
        (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
        (AuxiliaryRows nb (Fin rx))) rowWeight 2
    rowDivisor₀ := copies (rowSupport (RawRows s L nv nb (Fin rx))
        (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
        (AuxiliaryRows nb (Fin rx))) rowWeight 0
    rowDivisor₁ := copies (rowSupport (RawRows s L nv nb (Fin rx))
        (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
        (AuxiliaryRows nb (Fin rx))) rowWeight 1
    rowDivisor₂ := copies (rowSupport (RawRows s L nv nb (Fin rx))
        (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
        (AuxiliaryRows nb (Fin rx))) rowWeight 2
    rowDivisor₃ := copies (rowSupport (RawRows s L nv nb (Fin rx))
        (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
        (AuxiliaryRows nb (Fin rx))) rowWeight 3
    rawBits := rawTable R a s q L nv nb hs family order vectors cap
    orderBits := MatrixWeightedRowOrderLookup.orderWord order }

/-- The typed protected labels at writer coordinates. -/
def typedColumnAt (a s q cy : ℕ)
    (x : Fin (Fintype.card (ProtectedColumns a s q (Fin cy)))) :
    ProtectedColumns a s q (Fin cy) :=
  typedColumn (rawColumnCode' a s q cy) (MatrixWeightedTable.diagonalCode a s q cy)
    (uniformCopies (Y := Fin cy) a s q) x

def typedRowAt (s L nv nb rx : ℕ) (order : ItemOrder nv nb)
    (y : Fin (Fintype.card (ProtectedRows s L nv nb (Fin rx)))) :
    ProtectedRows s L nv nb (Fin rx) :=
  typedRow (rawRowCode s L nv nb rx order) (templateCode s L)
    (vertexCode nv rx) (auxiliaryCode nb rx) y

def semanticRow (s L nv nb rx : ℕ) (order : ItemOrder nv nb)
    (y : Fin (Fintype.card (ProtectedRows s L nv nb (Fin rx)))) : ℕ :=
  MatrixWeightedRawRead.sourceRow s L nv nb rx order
    (typedRowAt s L nv nb rx order y)

def semanticColumn (a s q cy : ℕ)
    (x : Fin (Fintype.card (ProtectedColumns a s q (Fin cy)))) : ℕ :=
  MatrixWeightedRawRead.sourceColumn a s q cy (typedColumnAt a s q cy x)

/-- The literal raw-table address corresponding to any in-range writer cell.
This equation is independent of the controller and contains no cell oracle. -/
theorem semantic_raw_bit (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (x : Fin (Fintype.card (ProtectedColumns a s q (Fin cy))))
    (y : Fin (Fintype.card (ProtectedRows s L nv nb (Fin rx)))) :
    (actualInput R a s q L nv nb hs family order vectors cap).rawBits[
      semanticRow s L nv nb rx order y *
        (actualInput R a s q L nv nb hs family order vectors cap).rawWidth +
      semanticColumn a s q cy x]?.getD false =
    MatrixWeightedProtectedWriter.protectedEntry R a s q L nv nb hs
      family order vectors cap x.val y.val := by
  simpa [actualInput, semanticRow, semanticColumn, typedColumnAt, typedRowAt]
    using (MatrixWeightedRawRead.source_lookup R a s q L nv nb hs family
      order vectors cap (typedColumnAt a s q cy x)
      (typedRowAt s L nv nb rx order y)).trans
      (MatrixWeightedProtectedWriter.protectedEntry_inbounds R a s q L nv nb
        hs family order vectors cap x y).symm

private theorem sum_split_left {m n : ℕ} (i : Fin (m + n))
    (hi : i.val < m) :
    finSumFinEquiv.symm i = Sum.inl ⟨i.val, hi⟩ := by
  have h : i = Fin.castAdd n ⟨i.val, hi⟩ := Fin.ext rfl
  calc
    finSumFinEquiv.symm i =
        finSumFinEquiv.symm (Fin.castAdd n ⟨i.val, hi⟩) := congrArg _ h
    _ = Sum.inl ⟨i.val, hi⟩ := finSumFinEquiv_symm_apply_castAdd _

private theorem sum_split_right {m n : ℕ} (i : Fin (m + n))
    (hi : m ≤ i.val) :
    finSumFinEquiv.symm i = Sum.inr ⟨i.val - m, by omega⟩ := by
  have h : i = Fin.natAdd m ⟨i.val - m, by omega⟩ := by
    apply Fin.ext
    simp
    omega
  calc
    finSumFinEquiv.symm i =
        finSumFinEquiv.symm (Fin.natAdd m ⟨i.val - m, by omega⟩) := congrArg _ h
    _ = Sum.inr ⟨i.val - m, by omega⟩ := finSumFinEquiv_symm_apply_natAdd _

private theorem prod_first_val {m n : ℕ} (i : Fin (m * n)) :
    (finProdFinEquiv.symm i).1.val = i.val / n := rfl

private theorem prod_second_val {m n : ℕ} (i : Fin (m * n)) :
    (finProdFinEquiv.symm i).2.val = i.val % n := rfl

/-- The abstract two-support ordinal decoder's full branch has the literal
source-column quotient used by the finite controller. -/
theorem decoded_full_column {M D S : ℕ}
    (i : Fin ((M * (182 * D) + D * (2 * M)) * S))
    (hi : i.val / S < M * (182 * D)) :
    ∃ (j : Fin M) (c : Fin (182 * D)) (u : Fin S),
      MatrixWeightedArithmetic.decodeColumn M D S i = (Sum.inl (j, c), u) ∧
      j.val = (i.val / S) / (182 * D) := by
  let outer := finProdFinEquiv.symm i
  have hout : outer.1.val = i.val / S := prod_first_val i
  let inner : Fin (M * (182 * D)) := ⟨outer.1.val, by omega⟩
  have hsplit : finSumFinEquiv.symm outer.1 = Sum.inl inner :=
    sum_split_left outer.1 (by omega)
  let j := (finProdFinEquiv.symm inner).1
  let c := (finProdFinEquiv.symm inner).2
  refine ⟨j, c, outer.2, ?_, ?_⟩
  · simp only [MatrixWeightedArithmetic.decodeColumn, outer, hsplit]
    rfl
  · simp only [j, prod_first_val, inner, hout]

theorem full_semantic_column (a s q cy : ℕ)
    (x : Fin (Fintype.card (ProtectedColumns a s q (Fin cy))))
    (h : x.val / uniformCopies (Y := Fin cy) a s q <
      Fintype.card (RawColumns a s q (Fin cy)) *
        (182 * Fintype.card (SecondRows a s q (Fin cy)))) :
    semanticColumn a s q cy x =
      (x.val / uniformCopies (Y := Fin cy) a s q) /
        (182 * Fintype.card (SecondRows a s q (Fin cy))) := by
  let M := Fintype.card (RawColumns a s q (Fin cy))
  let D := Fintype.card (SecondRows a s q (Fin cy))
  let S := uniformCopies (Y := Fin cy) a s q
  have hcard : Fintype.card (ProtectedColumns a s q (Fin cy)) =
      (M * (182 * D) + D * (2 * M)) * S := by
    rw [card_columns]
    dsimp [M, D, S]
    ring
  let i : Fin ((M * (182 * D) + D * (2 * M)) * S) := x.cast hcard
  obtain ⟨j, copy, uniform, hdecoded, hj⟩ :=
    decoded_full_column i (by simpa only [i, Fin.val_cast, M, D, S] using h)
  unfold semanticColumn MatrixWeightedRawRead.sourceColumn typedColumnAt
  simp [MatrixWeightedArithmetic.typedColumn, i, hdecoded,
    MatrixWeightedTable.rawColumnCode', M, D, S] at *
  simpa [WeightedDuplication.columnForget, WeightedDuplication.forget,
    WeightedDuplication.columnIncl] using hj

/-- On the second support, the residual quotient is the actual diagonal-row
label consumed by the fixed joint-tail arithmetic machine. -/
theorem decoded_diagonal_column {M D S : ℕ}
    (i : Fin ((M * (182 * D) + D * (2 * M)) * S))
    (hi : M * (182 * D) ≤ i.val / S) :
    ∃ (j : Fin D) (c : Fin (2 * M)) (u : Fin S),
      MatrixWeightedArithmetic.decodeColumn M D S i = (Sum.inr (j, c), u) ∧
      j.val = (i.val / S - M * (182 * D)) / (2 * M) := by
  let outer := finProdFinEquiv.symm i
  have hout : outer.1.val = i.val / S := prod_first_val i
  let inner : Fin (D * (2 * M)) :=
    ⟨outer.1.val - M * (182 * D), by have hh := outer.1.isLt; omega⟩
  have hsplit : finSumFinEquiv.symm outer.1 = Sum.inr inner :=
    sum_split_right outer.1 (by omega)
  let j := (finProdFinEquiv.symm inner).1
  let c := (finProdFinEquiv.symm inner).2
  refine ⟨j, c, outer.2, ?_, ?_⟩
  · simp only [MatrixWeightedArithmetic.decodeColumn, outer, hsplit]
    rfl
  · simp only [j, prod_first_val, inner, hout]

theorem diagonal_semantic_column (a s q cy : ℕ)
    (hcy : 0 < cy) (hbin : 2 ≤ binBase a s q cy)
    (x : Fin (Fintype.card (ProtectedColumns a s q (Fin cy))))
    (h : Fintype.card (RawColumns a s q (Fin cy)) *
      (182 * Fintype.card (SecondRows a s q (Fin cy))) ≤
      x.val / uniformCopies (Y := Fin cy) a s q) :
    semanticColumn a s q cy x =
      MatrixWeightedDiagonalMachine.rawValue
        ((x.val / uniformCopies (Y := Fin cy) a s q -
          Fintype.card (RawColumns a s q (Fin cy)) *
            (182 * Fintype.card (SecondRows a s q (Fin cy)))) /
          (2 * Fintype.card (RawColumns a s q (Fin cy))))
        (wordBase a s cy) cy s (binBase a s q cy) := by
  let M := Fintype.card (RawColumns a s q (Fin cy))
  let D := Fintype.card (SecondRows a s q (Fin cy))
  let S := uniformCopies (Y := Fin cy) a s q
  have hcard : Fintype.card (ProtectedColumns a s q (Fin cy)) =
      (M * (182 * D) + D * (2 * M)) * S := by
    rw [card_columns]
    dsimp [M, D, S]
    ring
  let i : Fin ((M * (182 * D) + D * (2 * M)) * S) := x.cast hcard
  obtain ⟨j, copy, uniform, hdecoded, hj⟩ :=
    decoded_diagonal_column i (by simpa only [i, Fin.val_cast, M, D, S] using h)
  unfold semanticColumn MatrixWeightedRawRead.sourceColumn typedColumnAt
  simp [MatrixWeightedArithmetic.typedColumn, i, hdecoded,
    MatrixWeightedTable.diagonalCode, M, D, S] at *
  -- The copy digit is forgotten; the second-row label is the unique input
  -- to the already checked joint-tail raw-column identity.
  rw [← hj]
  simpa [WeightedDuplication.columnForget, WeightedDuplication.forget,
    WeightedDuplication.columnIncl, MatrixWeightedTable.diagonalCode] using
    (MatrixWeightedDiagonalMachine.rawValue_actual hcy hbin
      ((MatrixWeightedTable.diagonalCode a s q cy).symm
        (Fin.cast (by simp [D, Construction.SecondRows]) j))).symm

/-- The first protected-row support decodes to the raw Stage--4 row ordinal
it represents.  The public `ItemOrder` is already baked into `rawRowCode`. -/
theorem full_semantic_row (s L nv nb rx : ℕ) (order : ItemOrder nv nb)
    (y : Fin (Fintype.card (ProtectedRows s L nv nb (Fin rx))))
    (h : y.val <
      Fintype.card (RawRows s L nv nb (Fin rx)) *
        copies (rowSupport (RawRows s L nv nb (Fin rx))
          (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
          (AuxiliaryRows nb (Fin rx))) rowWeight 0) :
    semanticRow s L nv nb rx order y =
      y.val / copies (rowSupport (RawRows s L nv nb (Fin rx))
        (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
        (AuxiliaryRows nb (Fin rx))) rowWeight 0 := by
  let X := Fintype.card (RawRows s L nv nb (Fin rx))
  let T := Fintype.card (TemplateSupport.{0} s L)
  let V := Fintype.card (VertexRows nv (Fin rx))
  let B := Fintype.card (AuxiliaryRows nb (Fin rx))
  let support := rowSupport (RawRows s L nv nb (Fin rx))
    (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
    (AuxiliaryRows nb (Fin rx))
  let cx := copies support rowWeight 0
  let ct := copies support rowWeight 1
  let cv := copies support rowWeight 2
  let cb := copies support rowWeight 3
  have hcard : Fintype.card (ProtectedRows s L nv nb (Fin rx)) =
      X * cx + (T * ct + (V * cv + B * cb)) := by
    simp only [ProtectedRows, Rows, Carrier, Fintype.card_sigma]
    simp [Fin.sum_univ_succ, Fintype.card_prod, Fintype.card_fin,
      cx, ct, cv, cb, X, T, V, B, support]
  let i : Fin (X * cx + (T * ct + (V * cv + B * cb))) := y.cast hcard
  have hdecoded := MatrixWeightedRowOuterDecode.full_branch
    X T V B cx ct cv cb i (by simpa only [i, Fin.val_cast, X, cx, support] using h)
  unfold semanticRow MatrixWeightedRawRead.sourceRow typedRowAt
  simp [MatrixWeightedArithmetic.typedRow, i, hdecoded,
    MatrixWeightedTable.rawRowCode, X, T, V, B, cx, ct, cv, cb,
    support] at *
  simpa [WeightedDuplication.rowForget, WeightedDuplication.forget,
    WeightedDuplication.rowIncl] using
    (MatrixWeightedColumnOuterDecode.pair_coordinates X cx
      (⟨y.val, by simpa only [X, cx, support] using h⟩ : Fin (X * cx))).1

private theorem template_raw_code (s L nv nb rx : ℕ)
    (order : ItemOrder nv nb) (t : TemplateSupport.{0} s L) :
    (rowCode s L nv nb rx order (Sum.inl t.down)).val =
      (templateCode s L t).val := by
  rfl

private theorem template_row_forget (s L nv nb rx : ℕ)
    (t : TemplateSupport.{0} s L)
    (copy : Fin (copies (rowSupport (RawRows s L nv nb (Fin rx))
      (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
      (AuxiliaryRows nb (Fin rx))) rowWeight 1)) :
    rowForget (fun t : TemplateSupport.{0} s L => Sum.inl t.down)
      (fun v => Sum.inr (Sum.inl v))
      (fun b => Sum.inr (Sum.inr b)) ⟨1, (t, copy)⟩ = Sum.inl t.down := by
  rfl

private theorem vertex_raw_code (s L nv nb rx : ℕ)
    (order : ItemOrder nv nb) (v : VertexRows nv (Fin rx)) :
    (rowCode s L nv nb rx order (Sum.inr (Sum.inl v))).val =
      s * L + (vertexIndex order v.1).val * rx + v.2.val := by
  simp only [MatrixStage4Codes.rowCode, Construction.rawRowEquiv,
    Construction.vertexIndex, finProdFinEquiv_apply_val,
    finSumFinEquiv_apply_right]
  change (Fin.natAdd (s * L)
    (finProdFinEquiv (order (Fin.castAdd nb v.1), v.2))).val = _
  simp [Fin.val_natAdd, finProdFinEquiv_apply_val]
  ring

private theorem auxiliary_raw_code (s L nv nb rx : ℕ)
    (order : ItemOrder nv nb) (b : AuxiliaryRows nb (Fin rx)) :
    (rowCode s L nv nb rx order (Sum.inr (Sum.inr b))).val =
      s * L + (auxiliaryIndex order b.1).val * rx + b.2.val := by
  simp only [MatrixStage4Codes.rowCode, Construction.rawRowEquiv,
    Construction.auxiliaryIndex, finProdFinEquiv_apply_val,
    finSumFinEquiv_apply_right]
  change (Fin.natAdd (s * L)
    (finProdFinEquiv (order (Fin.natAdd nv b.1), b.2))).val = _
  simp [Fin.val_natAdd, finProdFinEquiv_apply_val]
  ring

private theorem vertex_label_first (nv rx : ℕ)
    (z : Fin (Fintype.card (VertexRows nv (Fin rx)))) :
    ((vertexCode nv rx).symm z).1.val = z.val / rx := rfl

private theorem vertex_label_second (nv rx : ℕ)
    (z : Fin (Fintype.card (VertexRows nv (Fin rx)))) :
    ((vertexCode nv rx).symm z).2.val = z.val % rx := rfl

private theorem auxiliary_label_first (nb rx : ℕ)
    (z : Fin (Fintype.card (AuxiliaryRows nb (Fin rx)))) :
    ((auxiliaryCode nb rx).symm z).1.val = z.val / rx := rfl

private theorem auxiliary_label_second (nb rx : ℕ)
    (z : Fin (Fintype.card (AuxiliaryRows nb (Fin rx)))) :
    ((auxiliaryCode nb rx).symm z).2.val = z.val % rx := rfl

private theorem vertex_row_forget (s L nv nb rx : ℕ)
    (v : VertexRows nv (Fin rx))
    (copy : Fin (copies (rowSupport (RawRows s L nv nb (Fin rx))
      (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
      (AuxiliaryRows nb (Fin rx))) rowWeight 2)) :
    rowForget (fun t : TemplateSupport.{0} s L => Sum.inl t.down)
      (fun v => Sum.inr (Sum.inl v))
      (fun b => Sum.inr (Sum.inr b)) ⟨2, (v, copy)⟩ =
      Sum.inr (Sum.inl v) := rfl

private theorem auxiliary_row_forget (s L nv nb rx : ℕ)
    (b : AuxiliaryRows nb (Fin rx))
    (copy : Fin (copies (rowSupport (RawRows s L nv nb (Fin rx))
      (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
      (AuxiliaryRows nb (Fin rx))) rowWeight 3)) :
    rowForget (fun t : TemplateSupport.{0} s L => Sum.inl t.down)
      (fun v => Sum.inr (Sum.inl v))
      (fun b => Sum.inr (Sum.inr b)) ⟨3, (b, copy)⟩ =
      Sum.inr (Sum.inr b) := rfl

theorem template_semantic_row (s L nv nb rx : ℕ) (order : ItemOrder nv nb)
    (y : Fin (Fintype.card (ProtectedRows s L nv nb (Fin rx))))
    (h₁ : Fintype.card (RawRows s L nv nb (Fin rx)) *
      copies (rowSupport (RawRows s L nv nb (Fin rx))
        (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
        (AuxiliaryRows nb (Fin rx))) rowWeight 0 ≤ y.val)
    (h₂ : y.val - Fintype.card (RawRows s L nv nb (Fin rx)) *
      copies (rowSupport (RawRows s L nv nb (Fin rx))
        (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
        (AuxiliaryRows nb (Fin rx))) rowWeight 0 <
      Fintype.card (TemplateSupport.{0} s L) *
        copies (rowSupport (RawRows s L nv nb (Fin rx))
          (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
          (AuxiliaryRows nb (Fin rx))) rowWeight 1) :
    semanticRow s L nv nb rx order y =
      (y.val - Fintype.card (RawRows s L nv nb (Fin rx)) *
        copies (rowSupport (RawRows s L nv nb (Fin rx))
          (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
          (AuxiliaryRows nb (Fin rx))) rowWeight 0) /
        copies (rowSupport (RawRows s L nv nb (Fin rx))
          (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
          (AuxiliaryRows nb (Fin rx))) rowWeight 1 := by
  let X := Fintype.card (RawRows s L nv nb (Fin rx))
  let T := Fintype.card (TemplateSupport.{0} s L)
  let V := Fintype.card (VertexRows nv (Fin rx))
  let B := Fintype.card (AuxiliaryRows nb (Fin rx))
  let support := rowSupport (RawRows s L nv nb (Fin rx))
    (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
    (AuxiliaryRows nb (Fin rx))
  let cx := copies support rowWeight 0
  let ct := copies support rowWeight 1
  let cv := copies support rowWeight 2
  let cb := copies support rowWeight 3
  have hcard : Fintype.card (ProtectedRows s L nv nb (Fin rx)) =
      X * cx + (T * ct + (V * cv + B * cb)) := by
    simp only [ProtectedRows, Rows, Carrier, Fintype.card_sigma]
    simp [Fin.sum_univ_succ, Fintype.card_prod, Fintype.card_fin,
      cx, ct, cv, cb, X, T, V, B, support]
  let i : Fin (X * cx + (T * ct + (V * cv + B * cb))) := y.cast hcard
  have hdecoded := MatrixWeightedRowOuterDecode.template_branch
    X T V B cx ct cv cb i
    (by simpa only [i, Fin.val_cast, X, cx, support] using h₁)
    (by simpa only [i, Fin.val_cast, X, T, cx, ct, support] using h₂)
  let z : Fin (T * ct) := ⟨y.val - X * cx, by
    simpa only [X, T, cx, ct, support] using h₂⟩
  have hj := (MatrixWeightedColumnOuterDecode.pair_coordinates T ct z).1
  unfold semanticRow MatrixWeightedRawRead.sourceRow typedRowAt
  simp [MatrixWeightedArithmetic.typedRow, i, hdecoded,
    X, T, V, B, cx, ct, cv, cb, support]
  rw [template_row_forget, template_raw_code]
  rw [Equiv.apply_symm_apply]
  rfl

theorem vertex_semantic_row (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (y : Fin (Fintype.card (ProtectedRows s L nv nb (Fin rx))))
    (d : Input) (hd : d = actualInput R a s q L nv nb hs family order vectors cap)
    (h₁ : d.rowBoundary₁ ≤ y.val)
    (h₂ : d.rowBoundary₂ ≤ y.val - d.rowBoundary₁)
    (h₃ : y.val - d.rowBoundary₁ - d.rowBoundary₂ < d.rowBoundary₃) :
    ∃ j : Fin (nv + nb),
      j.val = MatrixWeightedEntryController.vertexLabel d y.val / rx ∧
      semanticRow s L nv nb rx order y =
        s * L + (order j).val * rx +
          MatrixWeightedEntryController.vertexLabel d y.val % rx := by
  subst d
  let X := Fintype.card (RawRows s L nv nb (Fin rx))
  let T := Fintype.card (TemplateSupport.{0} s L)
  let V := Fintype.card (VertexRows nv (Fin rx))
  let B := Fintype.card (AuxiliaryRows nb (Fin rx))
  let support := rowSupport (RawRows s L nv nb (Fin rx))
    (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
    (AuxiliaryRows nb (Fin rx))
  let cx := copies support rowWeight 0
  let ct := copies support rowWeight 1
  let cv := copies support rowWeight 2
  let cb := copies support rowWeight 3
  have hcard : Fintype.card (ProtectedRows s L nv nb (Fin rx)) =
      X * cx + (T * ct + (V * cv + B * cb)) := by
    simp only [ProtectedRows, Rows, Carrier, Fintype.card_sigma]
    simp [Fin.sum_univ_succ, Fintype.card_prod, Fintype.card_fin,
      cx, ct, cv, cb, X, T, V, B, support]
  let i : Fin (X * cx + (T * ct + (V * cv + B * cb))) := y.cast hcard
  have h₁' : X * cx ≤ i.val := by
    simpa only [i, Fin.val_cast, X, cx, support, actualInput] using h₁
  have h₂' : T * ct ≤ i.val - X * cx := by
    simpa only [i, Fin.val_cast, X, T, cx, ct, support, actualInput] using h₂
  have h₃' : i.val - X * cx - T * ct < V * cv := by
    simpa only [i, Fin.val_cast, X, T, V, cx, ct, cv, support,
      actualInput] using h₃
  have hdecoded := MatrixWeightedRowOuterDecode.vertex_branch
    X T V B cx ct cv cb i h₁' h₂' h₃'
  let z : Fin (V * cv) := ⟨y.val - X * cx - T * ct, by
    simpa only [i, Fin.val_cast] using h₃'⟩
  let label : Fin V := (finProdFinEquiv.symm z).1
  let v : VertexRows nv (Fin rx) :=
    (vertexCode nv rx).symm (Fin.cast (by simp [V, VertexRows]) label)
  let j : Fin (nv + nb) := Fin.castAdd nb v.1
  refine ⟨j, ?_, ?_⟩
  · simp [j, vertex_label_first, v,
      MatrixWeightedEntryController.vertexLabel, actualInput,
      z, label, X, T, cx, ct, cv, support]
  · unfold semanticRow MatrixWeightedRawRead.sourceRow typedRowAt
    simp [MatrixWeightedArithmetic.typedRow, i, hdecoded,
      X, T, V, B, cx, ct, cv, cb, support]
    rw [vertex_row_forget, vertex_raw_code]
    simp [j, Construction.vertexIndex, v, vertex_label_second,
      MatrixWeightedEntryController.vertexLabel,
      actualInput, z, label, X, T, cx, ct, cv, support]

set_option maxHeartbeats 1000000 in
theorem auxiliary_semantic_row (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (y : Fin (Fintype.card (ProtectedRows s L nv nb (Fin rx))))
    (d : Input) (hd : d = actualInput R a s q L nv nb hs family order vectors cap)
    (h₁ : d.rowBoundary₁ ≤ y.val)
    (h₂ : d.rowBoundary₂ ≤ y.val - d.rowBoundary₁)
    (h₃ : d.rowBoundary₃ ≤ y.val - d.rowBoundary₁ - d.rowBoundary₂) :
    ∃ j : Fin (nv + nb),
      j.val = MatrixWeightedEntryController.auxiliaryLabel d y.val / rx + nv ∧
      semanticRow s L nv nb rx order y =
        s * L + (order j).val * rx +
          MatrixWeightedEntryController.auxiliaryLabel d y.val % rx := by
  subst d
  let X := Fintype.card (RawRows s L nv nb (Fin rx))
  let T := Fintype.card (TemplateSupport.{0} s L)
  let V := Fintype.card (VertexRows nv (Fin rx))
  let B := Fintype.card (AuxiliaryRows nb (Fin rx))
  let support := rowSupport (RawRows s L nv nb (Fin rx))
    (TemplateSupport.{0} s L) (VertexRows nv (Fin rx))
    (AuxiliaryRows nb (Fin rx))
  let cx := copies support rowWeight 0
  let ct := copies support rowWeight 1
  let cv := copies support rowWeight 2
  let cb := copies support rowWeight 3
  have hcard : Fintype.card (ProtectedRows s L nv nb (Fin rx)) =
      X * cx + (T * ct + (V * cv + B * cb)) := by
    simp only [ProtectedRows, Rows, Carrier, Fintype.card_sigma]
    simp [Fin.sum_univ_succ, Fintype.card_prod, Fintype.card_fin,
      cx, ct, cv, cb, X, T, V, B, support]
  let i : Fin (X * cx + (T * ct + (V * cv + B * cb))) := y.cast hcard
  have h₁' : X * cx ≤ i.val := by
    simpa only [i, Fin.val_cast, X, cx, support, actualInput] using h₁
  have h₂' : T * ct ≤ i.val - X * cx := by
    simpa only [i, Fin.val_cast, X, T, cx, ct, support, actualInput] using h₂
  have h₃' : V * cv ≤ i.val - X * cx - T * ct := by
    simpa only [i, Fin.val_cast, X, T, V, cx, ct, cv, support,
      actualInput] using h₃
  have hdecoded := MatrixWeightedRowOuterDecode.auxiliary_branch
    X T V B cx ct cv cb i h₁' h₂' h₃'
  let z : Fin (B * cb) := ⟨y.val - X * cx - T * ct - V * cv, by
    have hi := i.isLt
    have hi' : i.val = y.val := rfl
    omega⟩
  let label : Fin B := (finProdFinEquiv.symm z).1
  let b : AuxiliaryRows nb (Fin rx) :=
    (auxiliaryCode nb rx).symm (Fin.cast (by simp [B, AuxiliaryRows]) label)
  let j : Fin (nv + nb) := Fin.natAdd nv b.1
  refine ⟨j, ?_, ?_⟩
  · simp [j, auxiliary_label_first, b,
      MatrixWeightedEntryController.auxiliaryLabel, actualInput,
      z, label, X, T, V, cx, ct, cv, support]
    exact Nat.add_comm _ _
  · unfold semanticRow MatrixWeightedRawRead.sourceRow typedRowAt
    simp [MatrixWeightedArithmetic.typedRow, i, hdecoded,
      X, T, V, B, cx, ct, cv, cb, support]
    rw [auxiliary_row_forget, auxiliary_raw_code]
    simp [j, Construction.auxiliaryIndex, b, auxiliary_label_second,
      MatrixWeightedEntryController.auxiliaryLabel,
      actualInput, z, label, X, T, V, cx, ct, cv, support]

def rawBit (d : Input) (row col : ℕ) : Bool :=
  d.rawBits[row * d.rawWidth + col]?.getD false

def fullColumnIndex (d : Input) (x : ℕ) : ℕ :=
  (x / d.uniform) / d.fullDivisor

def diagonalColumnIndex (d : Input) (x : ℕ) : ℕ :=
  MatrixWeightedDiagonalMachine.rawValue
    (MatrixWeightedEntryController.diagonalCode d x)
    d.wordBase d.cy d.s d.binBase

def vertexRowIndex (d : Input) (order : ItemOrder d.nv d.nb)
    (j : Fin (d.nv + d.nb)) (y : ℕ) : ℕ :=
  d.stagePrefixRows + (order j).val * d.rx +
    MatrixWeightedEntryController.vertexLabel d y % d.rx

def auxiliaryRowIndex (d : Input) (order : ItemOrder d.nv d.nb)
    (j : Fin (d.nv + d.nb)) (y : ℕ) : ℕ :=
  d.stagePrefixRows + (order j).val * d.rx +
    MatrixWeightedEntryController.auxiliaryLabel d y % d.rx

/-- Exhaustive branch evidence required by the charged entry controller.
Every constructor carries the equality of its *computed* raw table read to
the same protected matrix cell; no semantic callback is postulated. -/
inductive ActualCase (d : Input) (order : ItemOrder d.nv d.nb)
    (x y : ℕ) (target : Bool) : Prop where
  | fullFull
      (hc : x / d.uniform < d.fullBoundary)
      (hr : y < d.rowBoundary₁)
      (hbit : rawBit d (MatrixWeightedEntryController.fullLabel d y)
        (fullColumnIndex d x) = target) : ActualCase d order x y target
  | fullTemplate
      (hc : x / d.uniform < d.fullBoundary)
      (h₁ : d.rowBoundary₁ ≤ y)
      (hr : y - d.rowBoundary₁ < d.rowBoundary₂)
      (hbit : rawBit d (MatrixWeightedEntryController.templateLabel d y)
        (fullColumnIndex d x) = target) : ActualCase d order x y target
  | fullVertex (j : Fin (d.nv + d.nb))
      (hw : 0 < d.rx)
      (hc : x / d.uniform < d.fullBoundary)
      (h₁ : d.rowBoundary₁ ≤ y)
      (h₂ : d.rowBoundary₂ ≤ y - d.rowBoundary₁)
      (hr : y - d.rowBoundary₁ - d.rowBoundary₂ < d.rowBoundary₃)
      (hj : j.val = MatrixWeightedEntryController.vertexLabel d y / d.rx)
      (hbit : rawBit d (vertexRowIndex d order j y)
        (fullColumnIndex d x) = target) : ActualCase d order x y target
  | fullAuxiliary (j : Fin (d.nv + d.nb))
      (hw : 0 < d.rx)
      (hc : x / d.uniform < d.fullBoundary)
      (h₁ : d.rowBoundary₁ ≤ y)
      (h₂ : d.rowBoundary₂ ≤ y - d.rowBoundary₁)
      (h₃ : d.rowBoundary₃ ≤ y - d.rowBoundary₁ - d.rowBoundary₂)
      (hj : j.val = MatrixWeightedEntryController.auxiliaryLabel d y / d.rx + d.nv)
      (hbit : rawBit d (auxiliaryRowIndex d order j y)
        (fullColumnIndex d x) = target) : ActualCase d order x y target
  | diagonalFull
      (hc : d.fullBoundary ≤ x / d.uniform)
      (hr : y < d.rowBoundary₁)
      (hbit : rawBit d (MatrixWeightedEntryController.fullLabel d y)
        (diagonalColumnIndex d x) = target) : ActualCase d order x y target
  | diagonalTemplate
      (hc : d.fullBoundary ≤ x / d.uniform)
      (h₁ : d.rowBoundary₁ ≤ y)
      (hr : y - d.rowBoundary₁ < d.rowBoundary₂)
      (hbit : rawBit d (MatrixWeightedEntryController.templateLabel d y)
        (diagonalColumnIndex d x) = target) : ActualCase d order x y target
  | diagonalVertex (j : Fin (d.nv + d.nb))
      (hw : 0 < d.rx)
      (hc : d.fullBoundary ≤ x / d.uniform)
      (h₁ : d.rowBoundary₁ ≤ y)
      (h₂ : d.rowBoundary₂ ≤ y - d.rowBoundary₁)
      (hr : y - d.rowBoundary₁ - d.rowBoundary₂ < d.rowBoundary₃)
      (hj : j.val = MatrixWeightedEntryController.vertexLabel d y / d.rx)
      (hbit : rawBit d (vertexRowIndex d order j y)
        (diagonalColumnIndex d x) = target) : ActualCase d order x y target
  | diagonalAuxiliary (j : Fin (d.nv + d.nb))
      (hw : 0 < d.rx)
      (hc : d.fullBoundary ≤ x / d.uniform)
      (h₁ : d.rowBoundary₁ ≤ y)
      (h₂ : d.rowBoundary₂ ≤ y - d.rowBoundary₁)
      (h₃ : d.rowBoundary₃ ≤ y - d.rowBoundary₁ - d.rowBoundary₂)
      (hj : j.val = MatrixWeightedEntryController.auxiliaryLabel d y / d.rx + d.nv)
      (hbit : rawBit d (auxiliaryRowIndex d order j y)
        (diagonalColumnIndex d x) = target) : ActualCase d order x y target

set_option maxHeartbeats 1000000 in
theorem actual_cases (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (hcy : 0 < cy) (hbin : 2 ≤ binBase a s q cy) (hrx : 0 < rx)
    (x : Fin (Fintype.card (ProtectedColumns a s q (Fin cy))))
    (y : Fin (Fintype.card (ProtectedRows s L nv nb (Fin rx)))) :
    let d := actualInput R a s q L nv nb hs family order vectors cap
    ActualCase d order x.val y.val
      (MatrixWeightedProtectedWriter.protectedEntry R a s q L nv nb hs
        family order vectors cap x.val y.val) := by
  let d := actualInput R a s q L nv nb hs family order vectors cap
  let target := MatrixWeightedProtectedWriter.protectedEntry R a s q L nv nb hs
    family order vectors cap x.val y.val
  have hsource : rawBit d (semanticRow s L nv nb rx order y)
      (semanticColumn a s q cy x) = target := by
    simpa only [rawBit, d, target] using
      semantic_raw_bit R a s q L nv nb hs family order vectors cap x y
  have hwidth : 0 < d.rx := by simpa only [d, actualInput] using hrx
  by_cases hc : x.val / d.uniform < d.fullBoundary
  · have hcol : semanticColumn a s q cy x = fullColumnIndex d x.val := by
      simpa only [d, actualInput, fullColumnIndex] using
        full_semantic_column a s q cy x (by simpa only [d, actualInput] using hc)
    by_cases h₀ : y.val < d.rowBoundary₁
    · have hrow : semanticRow s L nv nb rx order y =
          MatrixWeightedEntryController.fullLabel d y.val := by
        simpa only [d, actualInput, MatrixWeightedEntryController.fullLabel]
          using full_semantic_row s L nv nb rx order y
            (by simpa only [d, actualInput] using h₀)
      apply ActualCase.fullFull hc h₀
      simpa only [rawBit, ← hrow, ← hcol] using hsource
    · have h₁ : d.rowBoundary₁ ≤ y.val := Nat.le_of_not_gt h₀
      by_cases ht : y.val - d.rowBoundary₁ < d.rowBoundary₂
      · have hrow : semanticRow s L nv nb rx order y =
            MatrixWeightedEntryController.templateLabel d y.val := by
          simpa only [d, actualInput, MatrixWeightedEntryController.templateLabel]
            using template_semantic_row s L nv nb rx order y
              (by simpa only [d, actualInput] using h₁)
              (by simpa only [d, actualInput] using ht)
        apply ActualCase.fullTemplate hc h₁ ht
        simpa only [rawBit, ← hrow, ← hcol] using hsource
      · have h₂ : d.rowBoundary₂ ≤ y.val - d.rowBoundary₁ := Nat.le_of_not_gt ht
        by_cases hv : y.val - d.rowBoundary₁ - d.rowBoundary₂ < d.rowBoundary₃
        · obtain ⟨j, hj, hrow⟩ := vertex_semantic_row R a s q L nv nb hs
            family order vectors cap y d rfl h₁ h₂ hv
          apply ActualCase.fullVertex j hwidth hc h₁ h₂ hv
            (by simpa only [d, actualInput] using hj)
          have hrow' : semanticRow s L nv nb rx order y =
              vertexRowIndex d order j y.val := by
            simpa only [vertexRowIndex, d, actualInput] using hrow
          simpa only [hrow', hcol] using hsource
        · have h₃ : d.rowBoundary₃ ≤ y.val - d.rowBoundary₁ - d.rowBoundary₂ :=
            Nat.le_of_not_gt hv
          obtain ⟨j, hj, hrow⟩ := auxiliary_semantic_row R a s q L nv nb hs
            family order vectors cap y d rfl h₁ h₂ h₃
          apply ActualCase.fullAuxiliary j hwidth hc h₁ h₂ h₃
            (by simpa only [d, actualInput] using hj)
          have hrow' : semanticRow s L nv nb rx order y =
              auxiliaryRowIndex d order j y.val := by
            simpa only [auxiliaryRowIndex, d, actualInput] using hrow
          simpa only [hrow', hcol] using hsource
  · have hc' : d.fullBoundary ≤ x.val / d.uniform := Nat.le_of_not_gt hc
    have hcol : semanticColumn a s q cy x = diagonalColumnIndex d x.val := by
      simpa only [d, actualInput, diagonalColumnIndex,
        MatrixWeightedEntryController.diagonalCode] using
        diagonal_semantic_column a s q cy hcy hbin x
          (by simpa only [d, actualInput] using hc')
    by_cases h₀ : y.val < d.rowBoundary₁
    · have hrow : semanticRow s L nv nb rx order y =
          MatrixWeightedEntryController.fullLabel d y.val := by
        simpa only [d, actualInput, MatrixWeightedEntryController.fullLabel]
          using full_semantic_row s L nv nb rx order y
            (by simpa only [d, actualInput] using h₀)
      apply ActualCase.diagonalFull hc' h₀
      simpa only [rawBit, ← hrow, ← hcol] using hsource
    · have h₁ : d.rowBoundary₁ ≤ y.val := Nat.le_of_not_gt h₀
      by_cases ht : y.val - d.rowBoundary₁ < d.rowBoundary₂
      · have hrow : semanticRow s L nv nb rx order y =
            MatrixWeightedEntryController.templateLabel d y.val := by
          simpa only [d, actualInput, MatrixWeightedEntryController.templateLabel]
            using template_semantic_row s L nv nb rx order y
              (by simpa only [d, actualInput] using h₁)
              (by simpa only [d, actualInput] using ht)
        apply ActualCase.diagonalTemplate hc' h₁ ht
        simpa only [rawBit, ← hrow, ← hcol] using hsource
      · have h₂ : d.rowBoundary₂ ≤ y.val - d.rowBoundary₁ := Nat.le_of_not_gt ht
        by_cases hv : y.val - d.rowBoundary₁ - d.rowBoundary₂ < d.rowBoundary₃
        · obtain ⟨j, hj, hrow⟩ := vertex_semantic_row R a s q L nv nb hs
            family order vectors cap y d rfl h₁ h₂ hv
          apply ActualCase.diagonalVertex j hwidth hc' h₁ h₂ hv
            (by simpa only [d, actualInput] using hj)
          have hrow' : semanticRow s L nv nb rx order y =
              vertexRowIndex d order j y.val := by
            simpa only [vertexRowIndex, d, actualInput] using hrow
          simpa only [hrow', hcol] using hsource
        · have h₃ : d.rowBoundary₃ ≤ y.val - d.rowBoundary₁ - d.rowBoundary₂ :=
            Nat.le_of_not_gt hv
          obtain ⟨j, hj, hrow⟩ := auxiliary_semantic_row R a s q L nv nb hs
            family order vectors cap y d rfl h₁ h₂ h₃
          apply ActualCase.diagonalAuxiliary j hwidth hc' h₁ h₂ h₃
            (by simpa only [d, actualInput] using hj)
          have hrow' : semanticRow s L nv nb rx order y =
              auxiliaryRowIndex d order j y.val := by
            simpa only [auxiliaryRowIndex, d, actualInput] using hrow
          simpa only [hrow', hcol] using hsource


end EthInapproximability.CurrentPaper.MatrixWeightedEntrySemantic
