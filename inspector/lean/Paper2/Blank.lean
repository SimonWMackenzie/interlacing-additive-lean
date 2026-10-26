import Paper2.Install

/-! Unit 3, segment (2), lane a-success-table-12: the count-free start bank is blank.

`StartInstall.blank = SuccessOrient.startBank 0 0 0 0 0 0 0 0 0 0 []` (owner-11 `Install.lean`) is `[]` in EVERY cell.
Read from the literal layered definitions: `SuccessOrient.startBank` -> `SamplerParameterJoin.startBank` ->
`CodeFallbackEntryJoin.initial` (= `CodeFallbackDimensionLoader.initialBank`, writer cells blank) ->
`CodeSampleInterpreterJoin.initial` (= `bank sampleSlots (CodeSampleInterpreterLoader.foreign [] 0 0) …`, whose foreign
part is `CodeAdminDraw.foreign [] 0 0` = `DrawParameterLoader.initialBank [] 0 0 0`, all its unary cells at 0) ->
`CodeGeneratorSampleJoin.initial` (= `bank compilerSlots (CodeGeneratorSampleTransfer.foreign 0 0)
(CodeRecursiveSeedPrep.publicBase 0 0 0 0 0 0 0 (List.replicate 0 true))`).
Consequence (with `StartInstall.startBank_install`): eleven appends into an all-blank region end exactly at
`SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word`. -/

set_option maxRecDepth 16384

namespace Paper2.StartBlank

open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

theorem bank_nil {K J : Type*} (ι : K ↪ J) (F : J → List Bool) (S : K → List Bool)
    (hF : ∀ j, F j = []) (hS : ∀ k, S k = []) (j : J) : bank ι F S j = [] := by
  classical
  by_cases h : ∃ k, ι k = j
  · obtain ⟨k, rfl⟩ := h
    rw [bank_at]; exact hS k
  · rw [bank_outside _ _ _ _ h]; exact hF j

theorem publicBase_nil :
    ∀ i, CodeRecursiveSeedPrep.publicBase 0 0 0 0 0 0 0 (List.replicate 0 true) i = [] := by
  intro i
  simp [CodeRecursiveSeedPrep.publicBase]

theorem gsj_nil (x : CodeGeneratorSampleJoin.Stack) :
    CodeGeneratorSampleJoin.initial 0 0 0 0 0 0 0 0 0 0 x = [] := by
  unfold CodeGeneratorSampleJoin.initial CodeGeneratorSampleTransfer.initialBank
  apply bank_nil
  · intro j
    unfold CodeGeneratorSampleTransfer.foreign
    split <;> simp
  · intro k; exact publicBase_nil k

theorem draw_nil (j : DrawParameterLoader.Stack) : DrawParameterLoader.initialBank [] 0 0 0 j = [] := by
  rcases j with i | c
  · simp [DrawParameterLoader.initialBank, DrawParameterLoader.mainBank]
  · rfl

theorem sij_nil (x : CodeSampleInterpreterJoin.Stack) :
    CodeSampleInterpreterJoin.initial 0 0 0 0 0 0 0 0 0 0 [] 0 0 x = [] := by
  unfold CodeSampleInterpreterJoin.initial CodeSampleInterpreterLoader.initialBank
  apply bank_nil
  · intro j
    rcases j with j | (j | j)
    · rfl
    · show CodeAdminDraw.foreign [] 0 0 j = []
      rcases j with j | j
      · exact draw_nil j
      · rfl
    · rfl
  · exact gsj_nil

/-- The count-free start bank is blank in every cell. -/
theorem blank_nil (x : SuccessOrient.Stack) : StartInstall.blank x = [] := by
  rcases x with (c | p) | f
  · show CodeFallbackEntryJoin.initial 0 0 0 0 0 0 0 0 0 0 [] 0 0 c = []
    unfold CodeFallbackEntryJoin.initial
    rcases c with s | w
    · exact sij_nil s
    · rfl
  · rfl
  · rfl

theorem blank_eq : StartInstall.blank = fun _ => [] := funext blank_nil

end Paper2.StartBlank

#print axioms Paper2.StartBlank.blank_nil
#print axioms Paper2.StartBlank.blank_eq
