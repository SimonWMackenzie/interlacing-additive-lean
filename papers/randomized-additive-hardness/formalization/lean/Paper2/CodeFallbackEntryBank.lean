import Paper2.CodeFallbackDimensionLoader

/-! Exact bank match between the physically prepared source and the
status-preserving interpreter/fallback program's genuine initial bank. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeFallbackEntryBank

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.CodeFallbackDimensionLoader

def fallbackSlot : CodeTableFallback.Stack → Stack
  | .inl j => .inl (CodeSampleInterpreterLoader.consumerSlots j)
  | .inr j => .inr j

theorem fallbackSlot_injective : Function.Injective fallbackSlot := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have h' : CodeSampleInterpreterLoader.consumerSlots a =
          CodeSampleInterpreterLoader.consumerSlots b := Sum.inl_injective h
      exact congrArg Sum.inl (CodeSampleInterpreterLoader.consumerSlots.injective h')
    | inr b => cases h
  | inr a =>
    cases b with
    | inl b => cases h
    | inr b => exact congrArg Sum.inr (Sum.inr_injective h)

def fallbackSlots : CodeTableFallback.Stack ↪ Stack :=
  ⟨fallbackSlot, fallbackSlot_injective⟩

theorem writer_ready (S : SourceStack → List Bool) (mX mY : Nat) :
    (fun j => afterY S mX mY (.inr j)) =
      (CodeTableFallback.writerData mX mY).contents := by
  funext j
  change Function.update
      (Function.update (Sum.elim S (fun _ : WriterStack => [])) rows
        (List.replicate mX true)) cols (List.replicate mY true) (.inr j) = _
  rcases j with j | j
  · rcases j with j | j
    · exact j.elim0
    · fin_cases j <;>
        simp [Function.update, rows, cols,
          CodeTableFallback.writerData,
          EthInapproximability.CurrentPaper.MatrixTableWriter.ready,
          EthInapproximability.CurrentPaper.MatrixTableWriter.Data.contents,
          EthInapproximability.CurrentPaper.MatrixTableWriter.Data.cell]
  · cases j <;>
      simp [Function.update, rows, cols,
        CodeTableFallback.writerData,
        EthInapproximability.CurrentPaper.MatrixTableWriter.ready,
        EthInapproximability.CurrentPaper.MatrixTableWriter.Data.contents,
        EthInapproximability.CurrentPaper.MatrixTableWriter.Data.foreign]

theorem source_scratch (n s q₁ q₂ w Q k mX mY : Nat)
    (row col : Code) (tape : List Bool) (B R : Nat) :
    CodeSampleInterpreterJoin.finalBank n s q₁ q₂ w Q k mX mY
      row col tape B R CodeSampleInterpreterLoader.scratch = [] := by
  have hne : CodeSampleInterpreterLoader.scratch ≠
      CodeSampleInterpreterLoader.target := by
    simp [CodeSampleInterpreterLoader.scratch,
      CodeSampleInterpreterLoader.target,
      CodeSampleInterpreterLoader.consumerSlots]
  change (Function.update
    (CodeSampleInterpreterLoader.initialBank
      (CodeGeneratorSampleJoin.afterAssembly
        (CodeRecursiveLoop.finished n s q₁ q₂ w Q row col).stk
        mX mY row col) tape B R)
    CodeSampleInterpreterLoader.target
    (encodeCode (.append (copies mY col) (copies mX row))))
    CodeSampleInterpreterLoader.scratch = []
  rw [Function.update_of_ne hne]
  exact CodeSampleInterpreterLoader.scratch_empty _ tape B R

theorem fallback_initial_bank (root : Code) (tape : List Bool)
    (B R mX mY : Nat) :
    (CodeTableFallback.initial (GeneratorCode.initial root)
      tape B R mX mY).stk =
    Sum.elim
      (CodeFullPadding.start (GeneratorCode.initial root) tape B R).stk
      (CodeTableFallback.writerData mX mY).contents := by
  change bank CodeTableFallback.interpreterIndex
    (Sum.elim (CodeFullPadding.start (GeneratorCode.initial root) tape B R).stk
      (CodeTableFallback.writerData mX mY).contents)
    (CodeFullPadding.start (GeneratorCode.initial root) tape B R).stk = _
  apply bank_eq_self
  intro j
  rfl

theorem prepared_fallback_bank (n s q₁ q₂ w Q k mX mY : Nat)
    (row col : Code) (tape : List Bool) (B R : Nat) :
    let root : Code := .append (copies mY col) (copies mX row)
    let S := CodeSampleInterpreterJoin.finalBank n s q₁ q₂ w Q k mX mY
      row col tape B R
    (fun j => afterY S mX mY (fallbackSlots j)) =
      (CodeTableFallback.initial (GeneratorCode.initial root)
        tape B R mX mY).stk := by
  let root : Code := .append (copies mY col) (copies mX row)
  let S := CodeSampleInterpreterJoin.finalBank n s q₁ q₂ w Q k mX mY
    row col tape B R
  dsimp only
  rw [fallback_initial_bank]
  funext j
  cases j with
  | inl j =>
    have h := CodeSampleInterpreterLoader.loaded_consumer_bank
      (CodeGeneratorSampleJoin.afterAssembly
        (CodeRecursiveLoop.finished n s q₁ q₂ w Q row col).stk
        mX mY row col) tape B R root
    have hcols : (Sum.inl (CodeSampleInterpreterLoader.consumerSlots j) : Stack) ≠ cols := by
      simp [cols]
    have hrows : (Sum.inl (CodeSampleInterpreterLoader.consumerSlots j) : Stack) ≠ rows := by
      simp [rows]
    change Function.update
      (Function.update (Sum.elim S (fun _ : WriterStack => [])) rows
        (List.replicate mX true)) cols (List.replicate mY true)
      (.inl (CodeSampleInterpreterLoader.consumerSlots j)) = _
    rw [Function.update_of_ne hcols, Function.update_of_ne hrows]
    exact congrFun h j
  | inr j =>
    exact congrFun (writer_ready S mX mY) j

#print axioms writer_ready
#print axioms source_scratch
#print axioms prepared_fallback_bank

end Paper2.CodeFallbackEntryBank
