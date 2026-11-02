import EthInapproximability.CurrentPaper.MatrixEntryProgram

/-!
# Physical bank layouts for the complete entry controller

The definitions here describe configurations for the proof. They are not
instructions, and the runtime proof must establish every transition between
them by the actual controller. All reusable data are preserved outside the
explicitly designated work registers.
-/

namespace EthInapproximability.CurrentPaper.MatrixEntryData

open MatrixEntryProgram

def extra (a d : ℕ) (data : MatrixMaterialization.ExactBitData)
    (out addr₁ mid addr₂ idx : List Bool) : Fin 28 → List Bool := fun k =>
  match k.val with
  | 0 => List.replicate a true
  | 1 => List.replicate d true
  | 2 => List.replicate (ExactConstruction.prefixLength a) true
  | 3 => List.replicate (ExactConstruction.prefixLength a + 3) true
  | 4 => data.first
  | 5 => data.second
  | 6 => data.source
  | 8 => out
  | 9 => addr₁
  | 10 => mid
  | 11 => addr₂
  | 19 => idx
  | _ => []

def join (p : MatrixEntryPreparation.Data) (e : Fin 28 → List Bool) : Stack → List Bool :=
  fun k => Sum.elim p.contents e (finSumFinEquiv.symm k)

def input (a d N₁ N₂ row col : ℕ) (data : MatrixMaterialization.ExactBitData)
    (out : List Bool) : Stack → List Bool :=
  join (MatrixEntryPreparation.inputData row col N₂ d N₁ [])
    (extra a d data out [] [] [] [])

def prepared {N₂ n d N₁ : ℕ} (a : ℕ) (r : (Fin 4 × Fin N₂) ⊕ Fin n)
    (c : ExactConstruction.Columns d N₁) (data : MatrixMaterialization.ExactBitData)
    (out addr₁ mid addr₂ idx : List Bool) : Stack → List Bool :=
  join (MatrixEntryPreparation.preparedData
      (MatrixEntryPreparation.inputData (MatrixMaterialization.rowCode N₂ n r).val
        (MatrixMaterialization.columnCode d N₁ c).val N₂ d N₁ []) r c)
    (extra a d data out addr₁ mid addr₂ idx)

theorem input_preparation (a d N₁ N₂ row col : ℕ)
    (data : MatrixMaterialization.ExactBitData) (out : List Bool) (k : Fin 26) :
    input a d N₁ N₂ row col data out (preparationSlots k) =
      (MatrixEntryPreparation.inputData row col N₂ d N₁ []).contents k := by
  fin_cases k <;> rfl

theorem prepared_preparation {N₂ n d N₁ : ℕ} (a : ℕ)
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁)
    (data : MatrixMaterialization.ExactBitData) (out : List Bool) (k : Fin 26) :
    prepared a r c data out [] [] [] [] (preparationSlots k) =
      (MatrixEntryPreparation.preparedData
        (MatrixEntryPreparation.inputData (MatrixMaterialization.rowCode N₂ n r).val
          (MatrixMaterialization.columnCode d N₁ c).val N₂ d N₁ []) r c).contents k := by
  fin_cases k <;> rfl

theorem preparation_bank {N₂ n d N₁ : ℕ} (a : ℕ)
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁)
    (data : MatrixMaterialization.ExactBitData) (out : List Bool) :
    BitMachineStackEmbedding.bank preparationSlots
      (input a d N₁ N₂ (MatrixMaterialization.rowCode N₂ n r).val
        (MatrixMaterialization.columnCode d N₁ c).val data out)
      (MatrixEntryPreparation.preparedData
        (MatrixEntryPreparation.inputData (MatrixMaterialization.rowCode N₂ n r).val
          (MatrixMaterialization.columnCode d N₁ c).val N₂ d N₁ []) r c).contents =
      prepared a r c data out [] [] [] [] := by
  classical
  funext k
  by_cases hk : k.val < 26
  · let j : Fin 26 := ⟨k.val, hk⟩
    have he : k = preparationSlots j := Fin.ext rfl
    rw [he, BitMachineStackEmbedding.bank_at, prepared_preparation]
  · rw [BitMachineStackEmbedding.bank_outside]
    · let j : Fin 28 := ⟨k.val - 26, by omega⟩
      have he : k = Fin.natAdd 26 j := by apply Fin.ext; simp [j]; omega
      simp only [input, prepared, join, he, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
    · intro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      change j.val = k.val at hv
      omega


/-- A local final bank determines the selected ambient registers; a proof of
agreement off those registers supplies the physical frame. -/
theorem bank_eq_of_frame {K : Type*} [DecidableEq K] (slots : K ↪ Stack)
    (old target : Stack → List Bool) (localBank : K → List Bool)
    (hlocal : ∀ k, localBank k = target (slots k))
    (hforeign : ∀ j, (¬ ∃ k, slots k = j) → old j = target j) :
    BitMachineStackEmbedding.bank slots old localBank = target := by
  classical
  funext j
  by_cases h : ∃ k, slots k = j
  · obtain ⟨k, rfl⟩ := h
    rw [BitMachineStackEmbedding.bank_at, hlocal]
  · rw [BitMachineStackEmbedding.bank_outside slots old localBank j h]
    exact hforeign j h

theorem template_restrict {N₂ n d N₁ : ℕ} (a : ℕ) (p : Fin 4) (z : Fin N₂)
    (c : ExactConstruction.Columns d N₁) (data : MatrixMaterialization.ExactBitData)
    (out addr₁ mid addr₂ : List Bool) (k : Fin 23) :
    MatrixTemplateEntry.contents (c.2 p).2.val (ExactConstruction.prefixLength a + 3)
      z.val d (c.2 p).1.val a (ExactConstruction.prefixLength a)
      data.first data.second out addr₁ mid addr₂ [] [] [] [] k =
    prepared (n := n) a (.inl (p,z)) c data out addr₁ mid addr₂ [] (templateSlots p k) := by
  fin_cases p <;> fin_cases k <;> rfl

theorem template_bank {N₂ n d N₁ : ℕ} (a : ℕ) (p : Fin 4) (z : Fin N₂)
    (c : ExactConstruction.Columns d N₁) (data : MatrixMaterialization.ExactBitData)
    (oldout old₁ oldmid old₂ out addr₁ mid addr₂ : List Bool) :
    BitMachineStackEmbedding.bank (templateSlots p)
      (prepared (n := n) a (.inl (p,z)) c data oldout old₁ oldmid old₂ [])
      (MatrixTemplateEntry.contents (c.2 p).2.val (ExactConstruction.prefixLength a + 3)
        z.val d (c.2 p).1.val a (ExactConstruction.prefixLength a)
        data.first data.second out addr₁ mid addr₂ [] [] [] []) =
      prepared (n := n) a (.inl (p,z)) c data out addr₁ mid addr₂ [] := by
  apply bank_eq_of_frame
  · exact template_restrict a p z c data out addr₁ mid addr₂
  · intro j hj
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 26 ⊕ Fin 28 ≃ Stack).surjective j
    rcases j with j | j
    · simp only [prepared, join, Equiv.symm_apply_apply, Sum.elim_inl]
    · simp only [prepared, join, Equiv.symm_apply_apply, Sum.elim_inr]
      fin_cases j <;> simp only [extra]
      · exact (hj ⟨19, rfl⟩).elim
      · exact (hj ⟨9, rfl⟩).elim
      · exact (hj ⟨10, rfl⟩).elim
      · exact (hj ⟨11, rfl⟩).elim

theorem source_restrict {N₂ n d N₁ : ℕ} (a : ℕ) (i : Fin n)
    (c : ExactConstruction.Columns d N₁) (data : MatrixMaterialization.ExactBitData)
    (out idx : List Bool) (k : MatrixSourceEntry.Stack) :
    (MatrixSourceEntry.cfg none {} none idx data.source [] [] (List.replicate d true)
      out (List.replicate i.val true) []).stk k =
    prepared (N₂ := N₂) a (.inr i) c data out [] [] [] idx (sourceSlots k) := by
  rcases k with k | k <;> fin_cases k <;> rfl

theorem source_bank {N₂ n d N₁ : ℕ} (a : ℕ) (i : Fin n)
    (c : ExactConstruction.Columns d N₁) (data : MatrixMaterialization.ExactBitData)
    (oldout oldidx out idx : List Bool) :
    BitMachineStackEmbedding.bank sourceSlots
      (prepared (N₂ := N₂) a (.inr i) c data oldout [] [] [] oldidx)
      (MatrixSourceEntry.cfg none {} none idx data.source [] [] (List.replicate d true)
        out (List.replicate i.val true) []).stk =
      prepared (N₂ := N₂) a (.inr i) c data out [] [] [] idx := by
  apply bank_eq_of_frame
  · exact source_restrict a i c data out idx
  · intro j hj
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 26 ⊕ Fin 28 ≃ Stack).surjective j
    rcases j with j | j
    · simp only [prepared, join, Equiv.symm_apply_apply, Sum.elim_inl]
    · simp only [prepared, join, Equiv.symm_apply_apply, Sum.elim_inr]
      fin_cases j <;> simp only [extra]
      · exact (hj ⟨.inl 10, rfl⟩).elim
      · exact (hj ⟨.inl 0, rfl⟩).elim

theorem source_copy_restrict {N₂ n d N₁ : ℕ} (a : ℕ) (i : Fin n)
    (c : ExactConstruction.Columns d N₁) (data : MatrixMaterialization.ExactBitData)
    (out idx : List Bool) (k : Fin 3) :
    (BitMachineCopy.cfg none none (List.replicate (c.2 0).1.val true) idx []).stk k =
      prepared (N₂ := N₂) a (.inr i) c data out [] [] [] idx (sourceCopySlots k) := by
  fin_cases k <;> rfl

theorem source_copy_bank {N₂ n d N₁ : ℕ} (a : ℕ) (i : Fin n)
    (c : ExactConstruction.Columns d N₁) (data : MatrixMaterialization.ExactBitData)
    (out oldidx idx : List Bool) :
    BitMachineStackEmbedding.bank sourceCopySlots
      (prepared (N₂ := N₂) a (.inr i) c data out [] [] [] oldidx)
      (BitMachineCopy.cfg none none (List.replicate (c.2 0).1.val true) idx []).stk =
      prepared (N₂ := N₂) a (.inr i) c data out [] [] [] idx := by
  apply bank_eq_of_frame
  · exact source_copy_restrict a i c data out idx
  · intro j hj
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 26 ⊕ Fin 28 ≃ Stack).surjective j
    rcases j with j | j
    · simp only [prepared, join, Equiv.symm_apply_apply, Sum.elim_inl]
    · simp only [prepared, join, Equiv.symm_apply_apply, Sum.elim_inr]
      fin_cases j <;> simp only [extra]
      · exact (hj ⟨1, rfl⟩).elim

theorem cleared_prepared {N₂ n d N₁ : ℕ} (a : ℕ)
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁)
    (data : MatrixMaterialization.ExactBitData) (out addr₁ mid addr₂ idx : List Bool) :
    BitMachineClearBank.cleared workSlot (prepared a r c data out addr₁ mid addr₂ idx) =
      input a d N₁ N₂ (MatrixMaterialization.rowCode N₂ n r).val
        (MatrixMaterialization.columnCode d N₁ c).val data out := by
  funext j
  by_cases h : ∃ i, workSlot i = j
  · obtain ⟨i, rfl⟩ := h
    rw [BitMachineClearBank.cleared_bank]
    fin_cases i <;> rfl
  · rw [BitMachineClearBank.cleared_foreign workSlot _ j (by
      intro i hi
      exact h ⟨i, hi⟩)]
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 26 ⊕ Fin 28 ≃ Stack).surjective j
    rcases j with j | j
    · simp only [prepared, input, join, Equiv.symm_apply_apply, Sum.elim_inl,
        MatrixEntryPreparation.preparedData, MatrixEntryPreparation.Data.contents,
        MatrixEntryPreparation.inputData]
      fin_cases j
      · simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
      · simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
      · simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
      · simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
      · simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
      · simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
      · exact (h ⟨0, rfl⟩).elim
      · exact (h ⟨1, rfl⟩).elim
      · exact (h ⟨2, rfl⟩).elim
      · exact (h ⟨3, rfl⟩).elim
      · exact (h ⟨4, rfl⟩).elim
      · exact (h ⟨5, rfl⟩).elim
      · exact (h ⟨6, rfl⟩).elim
      · exact (h ⟨7, rfl⟩).elim
      · exact (h ⟨8, rfl⟩).elim
      · exact (h ⟨9, rfl⟩).elim
      · exact (h ⟨10, rfl⟩).elim
      · exact (h ⟨11, rfl⟩).elim
      · exact (h ⟨12, rfl⟩).elim
      · exact (h ⟨13, rfl⟩).elim
      · exact (h ⟨14, rfl⟩).elim
      · exact (h ⟨15, rfl⟩).elim
      · exact (h ⟨16, rfl⟩).elim
      · exact (h ⟨17, rfl⟩).elim
      · exact (h ⟨18, rfl⟩).elim
      · exact (h ⟨19, rfl⟩).elim
    · simp only [prepared, input, join, Equiv.symm_apply_apply, Sum.elim_inr]
      fin_cases j
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (h ⟨20, rfl⟩).elim
      · exact (h ⟨21, rfl⟩).elim
      · exact (h ⟨22, rfl⟩).elim
      · exact (h ⟨23, rfl⟩).elim
      · exact (h ⟨24, rfl⟩).elim
      · exact (h ⟨25, rfl⟩).elim
      · exact (h ⟨26, rfl⟩).elim
      · exact (h ⟨27, rfl⟩).elim
      · exact (h ⟨28, rfl⟩).elim
      · exact (h ⟨29, rfl⟩).elim
      · exact (h ⟨30, rfl⟩).elim
      · exact (h ⟨31, rfl⟩).elim
      · exact (h ⟨32, rfl⟩).elim
      · exact (h ⟨33, rfl⟩).elim
      · exact (h ⟨34, rfl⟩).elim
      · exact (h ⟨35, rfl⟩).elim
      · exact (h ⟨36, rfl⟩).elim
      · exact (h ⟨37, rfl⟩).elim
      · exact (h ⟨38, rfl⟩).elim

def cleanupBound {N₂ n d N₁ : ℕ} (a : ℕ)
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁)
    (data : MatrixMaterialization.ExactBitData) (out addr₁ mid addr₂ idx : List Bool) : ℕ :=
  (∑ i, (prepared a r c data out addr₁ mid addr₂ idx (workSlot i)).length) + 41


def cleanupSize {N₂ n d N₁ : ℕ} (r : (Fin 4 × Fin N₂) ⊕ Fin n)
    (c : ExactConstruction.Columns d N₁) (addr₁ mid addr₂ idx : List Bool) : ℕ :=
  MatrixRowDecode.sourceIndex r + MatrixRowDecode.templateIndex r +
    (∑ p : Fin 4, ((c.2 p).2.val + (c.2 p).1.val)) +
    addr₁.length + mid.length + addr₂.length + idx.length + 41

theorem cleanupBound_eq {N₂ n d N₁ : ℕ} (a : ℕ)
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁)
    (data : MatrixMaterialization.ExactBitData) (out addr₁ mid addr₂ idx : List Bool) :
    cleanupBound a r c data out addr₁ mid addr₂ idx = cleanupSize r c addr₁ mid addr₂ idx := by
  have hs : (fun i : Fin 39 =>
      (prepared a r c data out addr₁ mid addr₂ idx (workSlot i)).length) =
      ![MatrixRowDecode.sourceIndex r, 0, 0, MatrixRowDecode.templateIndex r, 0, 0, 0, 0,
        (c.2 2).2.val, (c.2 3).2.val, (c.2 1).2.val, (c.2 0).2.val, 0,
        (c.2 3).1.val, (c.2 2).1.val, (c.2 1).1.val, (c.2 0).1.val, 0, 0, 0,
        addr₁.length, mid.length, addr₂.length, 0, 0, 0, 0, 0, 0, 0, idx.length,
        0, 0, 0, 0, 0, 0, 0, 0] := by
    funext i
    fin_cases i <;> first
    | exact List.length_replicate
    | rfl
  unfold cleanupBound cleanupSize
  change (∑ i, (fun i : Fin 39 =>
    (prepared a r c data out addr₁ mid addr₂ idx (workSlot i)).length) i) + 41 = _
  rw [hs]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Nat.add_zero]
  change _ = MatrixRowDecode.sourceIndex r + MatrixRowDecode.templateIndex r +
    ((c.2 0).2.val + (c.2 0).1.val +
      ((c.2 1).2.val + (c.2 1).1.val +
        ((c.2 2).2.val + (c.2 2).1.val + ((c.2 3).2.val + (c.2 3).1.val)))) +
    addr₁.length + mid.length + addr₂.length + idx.length + 41
  omega

end EthInapproximability.CurrentPaper.MatrixEntryData
