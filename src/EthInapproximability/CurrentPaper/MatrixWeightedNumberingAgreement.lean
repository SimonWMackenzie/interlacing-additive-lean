import EthInapproximability.CurrentPaper.MatrixTableInterlaceWeightedNumbering

/-!
# Agreement of weighted protected ordinal decoders

The physical 182:2 and four-support quotient decoders must match the
`Iteration.Numbering.weighted` enumerations, not merely produce equinumerous
carriers.  This owner proves that exact coordinate statement.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedNumberingAgreement

open Construction WeightedDuplication MatrixWeightedArithmetic
open MatrixTableInterlaceWeightedNumbering

variable {Ω Δ : Type} [Fintype Ω] [Fintype Δ]

theorem sigma_two_left (m n : ℕ) (i : Fin m) :
    ((finSigmaFinEquiv (n := ![m,n])
      ⟨(0 : Fin 2), i⟩).val) = i.val := by
  simp [finSigmaFinEquiv_apply]

theorem sigma_two_right (m n : ℕ) (i : Fin n) :
    ((finSigmaFinEquiv (n := ![m,n])
      ⟨(1 : Fin 2), i⟩).val) = m + i.val := by
  simp [finSigmaFinEquiv_apply]

private theorem sigma_two_size (m n : ℕ) :
    (∑ j : Fin 2, (![m,n] : Fin 2 → ℕ) j) = m + n := by
  simp

theorem sigma_two_decode_left (m n : ℕ) (i : Fin m) :
    (finSigmaFinEquiv (n := ![m,n])).symm
      ((finSumFinEquiv (Sum.inl i)).cast (sigma_two_size m n).symm) =
      ⟨(0 : Fin 2), i⟩ := by
  apply (finSigmaFinEquiv (n := ![m,n])).injective
  apply Fin.ext
  simp

theorem sigma_two_decode_right (m n : ℕ) (i : Fin n) :
    (finSigmaFinEquiv (n := ![m,n])).symm
      ((finSumFinEquiv (Sum.inr i)).cast (sigma_two_size m n).symm) =
      ⟨(1 : Fin 2), i⟩ := by
  apply (finSigmaFinEquiv (n := ![m,n])).injective
  apply Fin.ext
  simp

theorem sigma_index (k : ℕ) {X : Fin k → Type}
    (e : ∀ i, Iteration.Numbering (X i)) (i : Fin k) (x : X i) :
    (((Iteration.Numbering.sigma e).equiv.symm ⟨i,x⟩).val) =
      (∑ j : Fin i.val, (e (Fin.castLE i.isLt.le j)).size) +
        ((e i).equiv.symm x).val := by
  change ((finSigmaFinEquiv (n := fun j => (e j).size)
    ⟨i, (e i).equiv.symm x⟩).val) = _
  exact finSigmaFinEquiv_apply _

theorem column_left_index (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ)) (S : ℕ)
    (ω : Ω) (c : Fin (copies (columnSupport Ω Δ) columnWeight 0))
    (u : Fin S) :
    ((columnNumbering eΩ eΔ S).equiv.symm (⟨0, (ω,c)⟩,u)).val =
      ((eΩ ω).val * (copies (columnSupport Ω Δ) columnWeight 0) + c.val) *
        S + u.val := by
  change (((Iteration.Numbering.weighted
      (Iteration.Numbering.columnSupport
        ⟨Fintype.card Ω,eΩ.symm⟩ ⟨Fintype.card Δ,eΔ.symm⟩)
      columnWeight).prod (Iteration.Numbering.fin S)).equiv.symm
      (⟨0, (ω,c)⟩,u)).val = _
  rw [Iteration.Numbering.prod_index]
  simp only [Iteration.Numbering.fin, Equiv.refl_symm]
  rw [show Iteration.Numbering.weighted
      (Iteration.Numbering.columnSupport
        ⟨Fintype.card Ω,eΩ.symm⟩ ⟨Fintype.card Δ,eΔ.symm⟩)
      columnWeight = Iteration.Numbering.sigma _ from rfl]
  rw [sigma_index]
  rw [Iteration.Numbering.prod_index]
  simp [Iteration.Numbering.columnSupport, Iteration.Numbering.fin,
    Equiv.refl]
  rfl

theorem sigma_index_zero {X : Fin 2 → Type}
    (e : ∀ i, Iteration.Numbering (X i)) (x : X 0) :
    (((Iteration.Numbering.sigma e).equiv.symm ⟨0,x⟩).val) =
      ((e 0).equiv.symm x).val := by
  rw [sigma_index]
  simp

theorem sigma_index_one {X : Fin 2 → Type}
    (e : ∀ i, Iteration.Numbering (X i)) (x : X 1) :
    (((Iteration.Numbering.sigma e).equiv.symm ⟨1,x⟩).val) =
      (e 0).size + ((e 1).equiv.symm x).val := by
  rw [sigma_index]
  simp

theorem column_right_index (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ)) (S : ℕ)
    (δ : Δ) (c : Fin (copies (columnSupport Ω Δ) columnWeight 1))
    (u : Fin S) :
    ((columnNumbering eΩ eΔ S).equiv.symm (⟨1, (δ,c)⟩,u)).val =
      ((Fintype.card Ω * (copies (columnSupport Ω Δ) columnWeight 0) +
          (eΔ δ).val * (copies (columnSupport Ω Δ) columnWeight 1) + c.val) *
        S + u.val) := by
  change (((Iteration.Numbering.weighted
      (Iteration.Numbering.columnSupport
        ⟨Fintype.card Ω,eΩ.symm⟩ ⟨Fintype.card Δ,eΔ.symm⟩)
      columnWeight).prod (Iteration.Numbering.fin S)).equiv.symm
      (⟨1, (δ,c)⟩,u)).val = _
  rw [Iteration.Numbering.prod_index]
  simp only [Iteration.Numbering.fin, Equiv.refl_symm]
  rw [show Iteration.Numbering.weighted
      (Iteration.Numbering.columnSupport
        ⟨Fintype.card Ω,eΩ.symm⟩ ⟨Fintype.card Δ,eΔ.symm⟩)
      columnWeight = Iteration.Numbering.sigma _ from rfl]
  rw [sigma_index_one]
  rw [Iteration.Numbering.prod_index]
  have he : ((Iteration.Numbering.columnSupport
      ⟨Fintype.card Ω,eΩ.symm⟩ ⟨Fintype.card Δ,eΔ.symm⟩ 1).equiv.symm δ) =
      eΔ δ := by
    rfl
  rw [he]
  simp [Iteration.Numbering.prod, Iteration.Numbering.columnSupport,
    Iteration.Numbering.fin, Equiv.refl]
  change (Fintype.card Ω * copies (columnSupport Ω Δ) columnWeight 0 +
      ((eΔ δ).val * copies (columnSupport Ω Δ) columnWeight 1 + c.val)) *
      S + u.val =
      (Fintype.card Ω * copies (columnSupport Ω Δ) columnWeight 0 +
        (eΔ δ).val * copies (columnSupport Ω Δ) columnWeight 1 + c.val) *
      S + u.val
  rw [add_assoc]

theorem column_left_address (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ)) (S : ℕ)
    (ω : Ω) (c : Fin (copies (columnSupport Ω Δ) columnWeight 0))
    (u : Fin S) :
    (((columnNumbering eΩ eΔ S).equiv.symm (⟨0, (ω,c)⟩,u)).cast
      (by rw [← (columnNumbering eΩ eΔ S).card_eq, card_columns, column_total])) =
      finProdFinEquiv
        (finSumFinEquiv (Sum.inl (finProdFinEquiv
          ((eΩ ω), c.cast (show
              copies (columnSupport Ω Δ) columnWeight 0 =
                182 * Fintype.card Δ by
            have he : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
            simp [copies, columnSupport, columnWeight, he])))), u) := by
  apply Fin.ext
  simp only [Fin.val_cast]
  rw [column_left_index]
  have hc0 : copies (columnSupport Ω Δ) columnWeight 0 =
      182 * Fintype.card Δ := by
    have he : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
    simp [copies, columnSupport, columnWeight, he]
  change ((eΩ ω).val * copies (columnSupport Ω Δ) columnWeight 0 + c.val) *
      S + u.val = u.val + S * (c.val + 182 * Fintype.card Δ * (eΩ ω).val)
  conv_rhs => rw [← hc0]
  ring

theorem typed_column_left (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ)) (S : ℕ)
    (ω : Ω) (c : Fin (copies (columnSupport Ω Δ) columnWeight 0))
    (u : Fin S) :
    typedColumn eΩ eΔ S
      (((columnNumbering eΩ eΔ S).equiv.symm (⟨0, (ω,c)⟩,u)).cast
        (columnNumbering eΩ eΔ S).card_eq.symm) =
      (⟨0, (ω,c)⟩,u) := by
  simp [typedColumn, decodeColumn, column_left_address]

theorem column_right_address (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ)) (S : ℕ)
    (δ : Δ) (c : Fin (copies (columnSupport Ω Δ) columnWeight 1))
    (u : Fin S) :
    (((columnNumbering eΩ eΔ S).equiv.symm (⟨1, (δ,c)⟩,u)).cast
      (by rw [← (columnNumbering eΩ eΔ S).card_eq, card_columns, column_total])) =
      finProdFinEquiv
        (finSumFinEquiv (Sum.inr (finProdFinEquiv
          ((eΔ δ), c.cast (show
              copies (columnSupport Ω Δ) columnWeight 1 =
                2 * Fintype.card Ω by
            have he : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
            simp [copies, columnSupport, columnWeight, he]
            rfl)))), u) := by
  apply Fin.ext
  simp only [Fin.val_cast]
  rw [column_right_index]
  have hc0 : copies (columnSupport Ω Δ) columnWeight 0 =
      182 * Fintype.card Δ := by
    have he : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
    simp [copies, columnSupport, columnWeight, he]
  have hc1 : copies (columnSupport Ω Δ) columnWeight 1 =
      2 * Fintype.card Ω := by
    have he : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
    simp [copies, columnSupport, columnWeight, he]
    rfl
  simp [finProdFinEquiv, finSumFinEquiv]
  conv_rhs => rw [← hc0, ← hc1]
  ring

theorem typed_column_right (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ)) (S : ℕ)
    (δ : Δ) (c : Fin (copies (columnSupport Ω Δ) columnWeight 1))
    (u : Fin S) :
    typedColumn eΩ eΔ S
      (((columnNumbering eΩ eΔ S).equiv.symm (⟨1, (δ,c)⟩,u)).cast
        (columnNumbering eΩ eΔ S).card_eq.symm) =
      (⟨1, (δ,c)⟩,u) := by
  simp [typedColumn, decodeColumn, column_right_address]

theorem typed_column_inverse (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ)) (S : ℕ)
    (z : Columns Ω Δ S) :
    typedColumn eΩ eΔ S
      (((columnNumbering eΩ eΔ S).equiv.symm z).cast
        (columnNumbering eΩ eΔ S).card_eq.symm) = z := by
  rcases z with ⟨⟨tag, pair⟩, u⟩
  fin_cases tag
  · rcases pair with ⟨ω,c⟩
    exact typed_column_left eΩ eΔ S ω c u
  · rcases pair with ⟨δ,c⟩
    exact typed_column_right eΩ eΔ S δ c u

theorem typed_column_eq_numbering (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ)) (S : ℕ)
    (i : Fin (Fintype.card (Columns Ω Δ S))) :
    typedColumn eΩ eΔ S i =
      (columnNumbering eΩ eΔ S).equiv
        (i.cast (columnNumbering eΩ eΔ S).card_eq) := by
  let e := columnNumbering eΩ eΔ S
  have h := typed_column_inverse eΩ eΔ S
    (e.equiv (i.cast e.card_eq))
  simpa [e] using h

variable {X T V B : Type} [Fintype X] [Fintype T] [Fintype V] [Fintype B]

noncomputable def rowNumbering (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B)) :
    Iteration.Numbering (Rows X T V B) :=
  Iteration.Numbering.weighted
    (Iteration.Numbering.rowSupport
      ⟨Fintype.card X,eX.symm⟩ ⟨Fintype.card T,eT.symm⟩
      ⟨Fintype.card V,eV.symm⟩ ⟨Fintype.card B,eB.symm⟩)
    rowWeight

theorem sigma_four_zero {Z : Fin 4 → Type}
    (e : ∀ i, Iteration.Numbering (Z i)) (z : Z 0) :
    (((Iteration.Numbering.sigma e).equiv.symm ⟨0,z⟩).val) =
      ((e 0).equiv.symm z).val := by
  rw [sigma_index]
  simp

theorem sigma_four_one {Z : Fin 4 → Type}
    (e : ∀ i, Iteration.Numbering (Z i)) (z : Z 1) :
    (((Iteration.Numbering.sigma e).equiv.symm ⟨1,z⟩).val) =
      (e 0).size + ((e 1).equiv.symm z).val := by
  rw [sigma_index]
  simp

theorem sigma_four_two {Z : Fin 4 → Type}
    (e : ∀ i, Iteration.Numbering (Z i)) (z : Z 2) :
    (((Iteration.Numbering.sigma e).equiv.symm ⟨2,z⟩).val) =
      (e 0).size + (e 1).size + ((e 2).equiv.symm z).val := by
  rw [sigma_index]
  change (∑ j : Fin 2, (e (Fin.castLE (by decide : 2 ≤ 4) j)).size) +
    ((e 2).equiv.symm z).val = _
  rw [Fin.sum_univ_two]
  simp

theorem sigma_four_three {Z : Fin 4 → Type}
    (e : ∀ i, Iteration.Numbering (Z i)) (z : Z 3) :
    (((Iteration.Numbering.sigma e).equiv.symm ⟨3,z⟩).val) =
      (e 0).size + ((e 1).size + ((e 2).size +
        ((e 3).equiv.symm z).val)) := by
  rw [sigma_index]
  change (∑ j : Fin 3, (e (Fin.castLE (by decide : 3 ≤ 4) j)).size) +
    ((e 3).equiv.symm z).val = _
  rw [Fin.sum_univ_three]
  simp
  omega

theorem row_zero_index (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (x : X) (c : Fin (copies (rowSupport X T V B) rowWeight 0)) :
    ((rowNumbering eX eT eV eB).equiv.symm ⟨0,(x,c)⟩).val =
      (eX x).val * copies (rowSupport X T V B) rowWeight 0 + c.val := by
  change (((Iteration.Numbering.sigma (fun i =>
      (Iteration.Numbering.rowSupport
        ⟨Fintype.card X,eX.symm⟩ ⟨Fintype.card T,eT.symm⟩
        ⟨Fintype.card V,eV.symm⟩ ⟨Fintype.card B,eB.symm⟩ i).prod
        (Iteration.Numbering.fin (copies (rowSupport X T V B) rowWeight i)))).equiv.symm
      ⟨0,(x,c)⟩).val) = _
  rw [sigma_four_zero, Iteration.Numbering.prod_index]
  simp [Iteration.Numbering.rowSupport, Iteration.Numbering.fin, Equiv.refl]
  rfl

theorem row_one_index (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (t : T) (c : Fin (copies (rowSupport X T V B) rowWeight 1)) :
    ((rowNumbering eX eT eV eB).equiv.symm ⟨1,(t,c)⟩).val =
      Fintype.card X * copies (rowSupport X T V B) rowWeight 0 +
        (eT t).val * copies (rowSupport X T V B) rowWeight 1 + c.val := by
  change (((Iteration.Numbering.sigma (fun i =>
      (Iteration.Numbering.rowSupport
        ⟨Fintype.card X,eX.symm⟩ ⟨Fintype.card T,eT.symm⟩
        ⟨Fintype.card V,eV.symm⟩ ⟨Fintype.card B,eB.symm⟩ i).prod
        (Iteration.Numbering.fin (copies (rowSupport X T V B) rowWeight i)))).equiv.symm
      ⟨1,(t,c)⟩).val) = _
  rw [sigma_four_one, Iteration.Numbering.prod_index]
  have he : ((Iteration.Numbering.rowSupport
      ⟨Fintype.card X,eX.symm⟩ ⟨Fintype.card T,eT.symm⟩
      ⟨Fintype.card V,eV.symm⟩ ⟨Fintype.card B,eB.symm⟩ 1).equiv.symm t) =
      eT t := by rfl
  rw [he]
  simp [Iteration.Numbering.prod, Iteration.Numbering.rowSupport,
    Iteration.Numbering.fin, Equiv.refl]
  change (Fintype.card X * copies (rowSupport X T V B) rowWeight 0 +
      ((eT t).val * copies (rowSupport X T V B) rowWeight 1 + c.val)) = _
  omega

theorem row_two_index (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (v : V) (c : Fin (copies (rowSupport X T V B) rowWeight 2)) :
    ((rowNumbering eX eT eV eB).equiv.symm ⟨2,(v,c)⟩).val =
      Fintype.card X * copies (rowSupport X T V B) rowWeight 0 +
        Fintype.card T * copies (rowSupport X T V B) rowWeight 1 +
        (eV v).val * copies (rowSupport X T V B) rowWeight 2 + c.val := by
  change (((Iteration.Numbering.sigma (fun i =>
      (Iteration.Numbering.rowSupport
        ⟨Fintype.card X,eX.symm⟩ ⟨Fintype.card T,eT.symm⟩
        ⟨Fintype.card V,eV.symm⟩ ⟨Fintype.card B,eB.symm⟩ i).prod
        (Iteration.Numbering.fin (copies (rowSupport X T V B) rowWeight i)))).equiv.symm
      ⟨2,(v,c)⟩).val) = _
  rw [sigma_four_two, Iteration.Numbering.prod_index]
  have he : ((Iteration.Numbering.rowSupport
      ⟨Fintype.card X,eX.symm⟩ ⟨Fintype.card T,eT.symm⟩
      ⟨Fintype.card V,eV.symm⟩ ⟨Fintype.card B,eB.symm⟩ 2).equiv.symm v) =
      eV v := by rfl
  rw [he]
  simp [Iteration.Numbering.prod, Iteration.Numbering.rowSupport,
    Iteration.Numbering.fin, Equiv.refl]
  change (Fintype.card X * copies (rowSupport X T V B) rowWeight 0 +
      Fintype.card T * copies (rowSupport X T V B) rowWeight 1 +
      ((eV v).val * copies (rowSupport X T V B) rowWeight 2 + c.val)) = _
  omega

theorem row_three_index (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (b : B) (c : Fin (copies (rowSupport X T V B) rowWeight 3)) :
    ((rowNumbering eX eT eV eB).equiv.symm ⟨3,(b,c)⟩).val =
      Fintype.card X * copies (rowSupport X T V B) rowWeight 0 +
        Fintype.card T * copies (rowSupport X T V B) rowWeight 1 +
        Fintype.card V * copies (rowSupport X T V B) rowWeight 2 +
        (eB b).val * copies (rowSupport X T V B) rowWeight 3 + c.val := by
  change (((Iteration.Numbering.sigma (fun i =>
      (Iteration.Numbering.rowSupport
        ⟨Fintype.card X,eX.symm⟩ ⟨Fintype.card T,eT.symm⟩
        ⟨Fintype.card V,eV.symm⟩ ⟨Fintype.card B,eB.symm⟩ i).prod
        (Iteration.Numbering.fin (copies (rowSupport X T V B) rowWeight i)))).equiv.symm
      ⟨3,(b,c)⟩).val) = _
  rw [sigma_four_three, Iteration.Numbering.prod_index]
  have he : ((Iteration.Numbering.rowSupport
      ⟨Fintype.card X,eX.symm⟩ ⟨Fintype.card T,eT.symm⟩
      ⟨Fintype.card V,eV.symm⟩ ⟨Fintype.card B,eB.symm⟩ 3).equiv.symm b) =
      eB b := by rfl
  rw [he]
  simp [Iteration.Numbering.prod, Iteration.Numbering.rowSupport,
    Iteration.Numbering.fin, Equiv.refl]
  change (Fintype.card X * copies (rowSupport X T V B) rowWeight 0 +
      (Fintype.card T * copies (rowSupport X T V B) rowWeight 1 +
      (Fintype.card V * copies (rowSupport X T V B) rowWeight 2 +
      ((eB b).val * copies (rowSupport X T V B) rowWeight 3 + c.val)))) = _
  omega

private theorem row_card :
    Fintype.card (Rows X T V B) =
      Fintype.card X * copies (rowSupport X T V B) rowWeight 0 +
        (Fintype.card T * copies (rowSupport X T V B) rowWeight 1 +
          (Fintype.card V * copies (rowSupport X T V B) rowWeight 2 +
            Fintype.card B * copies (rowSupport X T V B) rowWeight 3)) := by
  simp only [Rows, Carrier, Fintype.card_sigma]
  simp [Fin.sum_univ_succ, Fintype.card_prod, Fintype.card_fin]

private theorem row_address_card (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B)) :
    (rowNumbering eX eT eV eB).size =
      Fintype.card X * copies (rowSupport X T V B) rowWeight 0 +
        (Fintype.card T * copies (rowSupport X T V B) rowWeight 1 +
          (Fintype.card V * copies (rowSupport X T V B) rowWeight 2 +
            Fintype.card B * copies (rowSupport X T V B) rowWeight 3)) := by
  rw [← (rowNumbering eX eT eV eB).card_eq, row_card]

theorem row_zero_address (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (x : X) (c : Fin (copies (rowSupport X T V B) rowWeight 0)) :
    (((rowNumbering eX eT eV eB).equiv.symm ⟨0,(x,c)⟩).cast
      (row_address_card eX eT eV eB)) =
      finSumFinEquiv (Sum.inl (finProdFinEquiv (eX x,c))) := by
  apply Fin.ext
  simp only [Fin.val_cast]
  rw [row_zero_index]
  simp [finProdFinEquiv, finSumFinEquiv]
  ring

theorem typed_row_zero (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (x : X) (c : Fin (copies (rowSupport X T V B) rowWeight 0)) :
    typedRow eX eT eV eB
      (((rowNumbering eX eT eV eB).equiv.symm ⟨0,(x,c)⟩).cast
        (rowNumbering eX eT eV eB).card_eq.symm) =
      ⟨0,(x,c)⟩ := by
  simp [typedRow, decodeRow, row_zero_address]

theorem row_one_address (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (t : T) (c : Fin (copies (rowSupport X T V B) rowWeight 1)) :
    (((rowNumbering eX eT eV eB).equiv.symm ⟨1,(t,c)⟩).cast
      (row_address_card eX eT eV eB)) =
      finSumFinEquiv (Sum.inr (finSumFinEquiv
        (Sum.inl (finProdFinEquiv (eT t,c))))) := by
  apply Fin.ext
  simp only [Fin.val_cast]
  rw [row_one_index]
  simp [finProdFinEquiv, finSumFinEquiv]
  ring

theorem typed_row_one (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (t : T) (c : Fin (copies (rowSupport X T V B) rowWeight 1)) :
    typedRow eX eT eV eB
      (((rowNumbering eX eT eV eB).equiv.symm ⟨1,(t,c)⟩).cast
        (rowNumbering eX eT eV eB).card_eq.symm) =
      ⟨1,(t,c)⟩ := by
  simp [typedRow, decodeRow, row_one_address]

theorem row_two_address (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (v : V) (c : Fin (copies (rowSupport X T V B) rowWeight 2)) :
    (((rowNumbering eX eT eV eB).equiv.symm ⟨2,(v,c)⟩).cast
      (row_address_card eX eT eV eB)) =
      finSumFinEquiv (Sum.inr (finSumFinEquiv
        (Sum.inr (finSumFinEquiv
          (Sum.inl (finProdFinEquiv (eV v,c))))))) := by
  apply Fin.ext
  simp only [Fin.val_cast]
  rw [row_two_index]
  simp [finProdFinEquiv, finSumFinEquiv]
  ring

theorem typed_row_two (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (v : V) (c : Fin (copies (rowSupport X T V B) rowWeight 2)) :
    typedRow eX eT eV eB
      (((rowNumbering eX eT eV eB).equiv.symm ⟨2,(v,c)⟩).cast
        (rowNumbering eX eT eV eB).card_eq.symm) =
      ⟨2,(v,c)⟩ := by
  simp [typedRow, decodeRow, row_two_address]

theorem row_three_address (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (b : B) (c : Fin (copies (rowSupport X T V B) rowWeight 3)) :
    (((rowNumbering eX eT eV eB).equiv.symm ⟨3,(b,c)⟩).cast
      (row_address_card eX eT eV eB)) =
      finSumFinEquiv (Sum.inr (finSumFinEquiv
        (Sum.inr (finSumFinEquiv
          (Sum.inr (finProdFinEquiv (eB b,c))))))) := by
  apply Fin.ext
  simp only [Fin.val_cast]
  rw [row_three_index]
  simp [finProdFinEquiv, finSumFinEquiv]
  ring

theorem typed_row_three (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (b : B) (c : Fin (copies (rowSupport X T V B) rowWeight 3)) :
    typedRow eX eT eV eB
      (((rowNumbering eX eT eV eB).equiv.symm ⟨3,(b,c)⟩).cast
        (rowNumbering eX eT eV eB).card_eq.symm) =
      ⟨3,(b,c)⟩ := by
  simp [typedRow, decodeRow, row_three_address]

theorem typed_row_inverse (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (z : Rows X T V B) :
    typedRow eX eT eV eB
      (((rowNumbering eX eT eV eB).equiv.symm z).cast
        (rowNumbering eX eT eV eB).card_eq.symm) = z := by
  rcases z with ⟨tag, pair⟩
  fin_cases tag
  · rcases pair with ⟨x,c⟩
    exact typed_row_zero eX eT eV eB x c
  · rcases pair with ⟨t,c⟩
    exact typed_row_one eX eT eV eB t c
  · rcases pair with ⟨v,c⟩
    exact typed_row_two eX eT eV eB v c
  · rcases pair with ⟨b,c⟩
    exact typed_row_three eX eT eV eB b c

theorem typed_row_eq_numbering (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (i : Fin (Fintype.card (Rows X T V B))) :
    typedRow eX eT eV eB i =
      (rowNumbering eX eT eV eB).equiv
        (i.cast (rowNumbering eX eT eV eB).card_eq) := by
  let e := rowNumbering eX eT eV eB
  have h := typed_row_inverse eX eT eV eB
    (e.equiv (i.cast e.card_eq))
  simpa [e] using h

end EthInapproximability.CurrentPaper.MatrixWeightedNumberingAgreement
