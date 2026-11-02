import EthInapproximability.CurrentPaper.SourceGenericAcceptedSource

/-!
# First-row join on one bank (unit 1, segment 2)

Paper B, locked v8 Section 6 and Appendix B; CP-SOURCE-EFFECTIVE, arbitrary
fixed alphabet `a`.

ONE fixed-`(a,q)` body program on the common bank, sequenced with
`BitMachineRawSequence`:

1. the admitted staged first-row body `SourceCSPFirstRowController.bodyProgram`
   (the accepted branch of `raw_total_first_row`), lifted to the bank;
2. the segment-1 ambient prefix program (unary `n` copy, all at-least chains,
   all `a*a` ordered pairs with diagonals, copy-back into writer
   `saved`/`count`), lifted to the bank;
3. `SourceGenericFirstRowSuffix.callbackClearSuffixProgram` (row 0, loop-count
   clear, rows `1..m-1`, EOF), lifted to the bank.

`body_run` starts from the ACTUAL accepting validator halt (no supplied rows,
prefix words, callback result or runtime) and derives every premise of
`first_then_remaining` (truth/query/rest of row 0, unary vertex, empty row
index, header count, cap, and the word bound `H`) from whole-bank preservation
and the typed source readback. `accepted_first_row_join` inlines it in the
raw-input verdict controller `top`.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.FirstRow

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceGenericPrefixMachine PrefixAmbientCopy PrefixAmbientSeed
  PrefixAmbientWork PrefixAmbientInstall
open scoped Classical

/-- The control type of a fixed program (used only to name control values). -/
abbrev CtlOf {K L V : Type} [DecidableEq K]
    (_P : L → TM2.Stmt (fun _ : K => Bool) L V) : Type := V

noncomputable def ambControl (a q : Nat) :
    CtlOf (PrefixAmbientProgram.program a q) :=
  (none,
    (((((AtLeastLoopCallback.callback a q).initial, none),
        ((none, none), none)),
      ((PairVertexLoopCallback.routine a q).initial, none)),
      (none, none)))

noncomputable def suffixStart {a q : Nat} (hq : 0 < q) :
    CtlOf (SourceGenericFirstRowSuffix.callbackClearSuffixProgram (a := a) hq) :=
  (((((), none), (SourceClauseGenericAllSlots.allCircuit (a := a) hq).initial),
    ((), none)), .copy none)

noncomputable def suffixEnd {a q : Nat} (hq : 0 < q) :
    CtlOf (SourceGenericFirstRowSuffix.callbackClearSuffixProgram (a := a) hq) :=
  (((((), none), (SourceClauseGenericAllSlots.allCircuit (a := a) hq).initial),
    ((), none)), .done true)

noncomputable def stageProgram (a q : Nat) :=
  fun l => stackStmt (frEmb q) (SourceCSPFirstRowController.bodyProgram q a l)

noncomputable def ambientProgram (a q : Nat) :=
  fun l => stackStmt (ambEmb q) (PrefixAmbientProgram.program a q l)

noncomputable def suffixProgram {a q : Nat} (hq : 0 < q) :=
  fun l => stackStmt (fsbEmb q)
    (SourceGenericFirstRowSuffix.callbackClearSuffixProgram (a := a) hq l)

noncomputable def tailProgram {a q : Nat} (hq : 0 < q) :=
  BitMachineRawSequence.program (ambientProgram a q) (suffixProgram (a := a) hq)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.clear 0))))
    (ambControl a q) (suffixStart (a := a) hq)

/-- The fixed segment-2 body: staged first row, ambient prefix, then row 0
and the remaining rows. -/
noncomputable def program {a q : Nat} (hq : 0 < q) :=
  BitMachineRawSequence.program (stageProgram a q) (tailProgram (a := a) hq)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    SourceCSPFirstRowController.bodyInitial
    (ambControl a q, suffixStart (a := a) hq)

/-! ## Named whole banks -/

noncomputable def globalBank {q : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool) :
    Stack q → List Bool :=
  bank (globalEmb q) (fun _ => []) S

noncomputable def stagedBank {q : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (U : SourceCSPFirstRowController.Stack q → List Bool) :
    Stack q → List Bool :=
  bank (frEmb q) (globalBank S) U

noncomputable def prefixedBank {q : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (U : SourceCSPFirstRowController.Stack q → List Bool) (n a : Nat) :
    Stack q → List Bool :=
  bank (ambEmb q) (stagedBank S U) (installed U n a)

/-- Raw first-row-controller bank after the prefix install. -/
noncomputable def installedRaw {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) (n a : Nat) :
    SourceCSPFirstRowController.Stack q → List Bool :=
  Function.update
    (Function.update U (.inr SourceClauseRowWriterCleanup.savedCell)
      (savedWord n a q))
    (.inr SourceClauseRowWriterCleanup.countCell) (countWord n a)

noncomputable def firstClauses {n m a q : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q) : List EncodedCNF.Clause :=
  SourceGenericAllRowLoop.rowClauses rows hq ⟨0, hm⟩

noncomputable def restClauses {n m a q : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q) : List EncodedCNF.Clause :=
  SourceGenericAllRowLoop.suffixClauses rows hq 0 (m - 1) (by omega)

/-- Exact whole bank at the end of the body. -/
noncomputable def finalBank {n m a q : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool) :
    Stack q → List Bool :=
  bank (fsbEmb q) (prefixedBank S U n a)
    (SourceCSPNextRowBridge.callbackBank
      (SourceGenericAllRowLoop.withRemaining
        (Function.update S SourceCSPHeaderRowBridge.loopCount []) 0)
      lastRow n (m - 1)
      ((EncodedCNF.clauseFields (restClauses hq hm rows)).reverse ++
        (EncodedCNF.clauseFields (firstClauses hq hm rows)).reverse ++
          savedWord n a q)
      []
      (List.replicate (restClauses hq hm rows).length true ++
        List.replicate (firstClauses hq hm rows).length true ++
          countWord n a))

/-- Word bound fed to `first_then_remaining`: an explicit fixed-`(a,q)`
function of the raw length, `n`, `m` and the actual row-0/prefix words. -/
noncomputable def hBound {n m a q : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q) (L : Nat) : Nat :=
  AcceptedSource.envelope a q L + n + m + (1 + a ^ q) +
    ((EncodedCNF.clauseFields (firstClauses hq hm rows)).reverse ++
      savedWord n a q).length +
    (List.replicate (firstClauses hq hm rows).length true ++
      countWord n a).length

/-- Charged clock of the suffix phase, exactly as in `first_then_remaining`
at the installed bank. -/
noncomputable def suffixClock {n m a q : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (U : SourceCSPFirstRowController.Stack q → List Bool) (L : Nat) : Nat :=
  SourceCSPFirstSlotBridge.cleanupTime (installedRaw U n a) +
    SourceClauseGenericAllSlotPolynomial.allCoefficient a q *
      (SourceClauseGenericRow.inputBits
        (SourceCSPFirstSlotBridge.row (installedRaw U n a)) n 0
        (savedWord n a q) [] (countWord n a) + 1)^2 +
    hBound hq hm rows L + 3 +
    SourceGenericAllRowLoopClock.loopCoefficient a q *
      (hBound hq hm rows L + 1)^9 + 2

/-! ## Bank bookkeeping -/

theorem ambEmb_not_side {q : Nat} (i : Fin 2) :
    ¬ ∃ y, ambEmb q y =
      (.inl (.inl (.inr (.inr i))) : Stack q) := by
  rintro ⟨y, hy⟩
  rcases y with (x | w) | s
  · cases x <;>
      simp [ambEmb, ambMap, frToFsb] at hy
  · simp [ambEmb, ambMap] at hy
  · simp [ambEmb, ambMap] at hy

theorem frEmb_not_side {q : Nat} (i : Fin 2) :
    ¬ ∃ x, frEmb q x = (.inl (.inl (.inr (.inr i))) : Stack q) := by
  rintro ⟨x, hx⟩
  cases x <;> simp [frEmb, fsbEmb, frToFsb] at hx

theorem frEmb_not_work {q : Nat} (w : PrefixCopy.Stack) :
    ¬ ∃ x, frEmb q x = (.inl (.inr w) : Stack q) := by
  rintro ⟨x, hx⟩
  cases x <;> simp [frEmb, fsbEmb, frToFsb] at hx

theorem frEmb_not_scratch {q : Nat} (s : Fin 1) :
    ¬ ∃ x, frEmb q x = (.inr s : Stack q) := by
  rintro ⟨x, hx⟩
  cases x <;> simp [frEmb, fsbEmb, frToFsb] at hx

theorem globalBank_outside_fr {q : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (y : Stack q) (hy : ¬ ∃ x, frEmb q x = y) : globalBank S y = [] := by
  unfold globalBank
  rw [bank_outside]
  rintro ⟨g, rfl⟩
  exact hy ⟨.inl g, rfl⟩

theorem stagedBank_amb {q : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (U : SourceCSPFirstRowController.Stack q → List Bool) :
    bank (ambEmb q) (stagedBank S U) (initial U) = stagedBank S U := by
  apply bank_eq_self
  intro y
  rcases y with (x | w) | s
  · change initial U (rawEmbedding q x) = stagedBank S U (frEmb q x)
    rw [stagedBank, bank_at, initial_raw]
  · change initial U (workEmbedding q w) = stagedBank S U (.inl (.inr w))
    rw [stagedBank, bank_outside _ _ _ _ (frEmb_not_work w),
      globalBank_outside_fr S _ (frEmb_not_work w), initial_work]
  · have hs : s = 0 := Subsingleton.elim _ _
    subst s
    change initial U (scratch q) = stagedBank S U (.inr 0)
    rw [stagedBank, bank_outside _ _ _ _ (frEmb_not_scratch 0),
      globalBank_outside_fr S _ (frEmb_not_scratch 0), initial_scratch]

theorem prefixedBank_fsb {q : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (U : SourceCSPFirstRowController.Stack q → List Bool) (n a : Nat) :
    bank (fsbEmb q) (prefixedBank S U n a)
        (SourceCSPFirstSlotBridge.extended (installedRaw U n a)) =
      prefixedBank S U n a := by
  apply bank_eq_self
  intro z
  rcases z with g | (k | i)
  · change _ = bank (ambEmb q) (stagedBank S U) (installed U n a)
        (ambEmb q (rawEmbedding q (.inl g)))
    rw [bank_at, installed_raw]
    rfl
  · change _ = bank (ambEmb q) (stagedBank S U) (installed U n a)
        (ambEmb q (rawEmbedding q (.inr k)))
    rw [bank_at, installed_raw]
    rfl
  · change [] = bank (ambEmb q) (stagedBank S U) (installed U n a)
        (.inl (.inl (.inr (.inr i))))
    rw [bank_outside _ _ _ _ (ambEmb_not_side i), stagedBank,
      bank_outside _ _ _ _ (frEmb_not_side i),
      globalBank_outside_fr S _ (frEmb_not_side i)]

theorem installedRaw_left {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) (n a : Nat)
    (g : SourceCSPGlobalDecisionProgram.Stack q) :
    installedRaw U n a (.inl g) = U (.inl g) := by
  simp [installedRaw]

theorem installedRaw_row {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) (n a : Nat)
    (x : SourceCSPRowQueryFrame.Stack q) :
    SourceCSPFirstSlotBridge.row (installedRaw U n a) x =
      SourceCSPFirstSlotBridge.row U x := by
  simp [installedRaw, SourceCSPFirstSlotBridge.row, SourceCSPStagedFirstRow.rowSlot,
    SourceClauseRowWriterCleanup.rowCell, SourceClauseRowWriterCleanup.savedCell,
    SourceClauseRowWriterCleanup.countCell]

theorem installedRaw_vertex {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) (n a : Nat) :
    SourceCSPFirstSlotBridge.writer (installedRaw U n a)
        SourceClauseRowWriterOperands.vertex =
      SourceCSPFirstSlotBridge.writer U SourceClauseRowWriterOperands.vertex := by
  simp [installedRaw, SourceCSPFirstSlotBridge.writer,
    SourceClauseRowWriterOperands.vertex, SourceClauseRowWriterCleanup.savedCell,
    SourceClauseRowWriterCleanup.countCell]

theorem installedRaw_rowIndex {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) (n a : Nat) :
    SourceCSPFirstSlotBridge.writer (installedRaw U n a)
        SourceClauseRowWriterOperands.rowIndex =
      SourceCSPFirstSlotBridge.writer U SourceClauseRowWriterOperands.rowIndex := by
  simp [installedRaw, SourceCSPFirstSlotBridge.writer,
    SourceClauseRowWriterOperands.rowIndex, SourceClauseRowWriterCleanup.savedCell,
    SourceClauseRowWriterCleanup.countCell]

theorem installedRaw_saved {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) (n a : Nat) :
    SourceCSPFirstSlotBridge.writer (installedRaw U n a)
        SourceClauseRowWriterCleanup.savedCell = savedWord n a q := by
  simp [installedRaw, SourceCSPFirstSlotBridge.writer,
    SourceClauseRowWriterCleanup.savedCell, SourceClauseRowWriterCleanup.countCell]

theorem installedRaw_count {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) (n a : Nat) :
    SourceCSPFirstSlotBridge.writer (installedRaw U n a)
        SourceClauseRowWriterCleanup.countCell = countWord n a := by
  simp [installedRaw, SourceCSPFirstSlotBridge.writer]

theorem installedRaw_output {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) (n a : Nat) :
    SourceCSPFirstSlotBridge.writer (installedRaw U n a)
        SourceClauseRowWriterCleanup.outputCell =
      SourceCSPFirstSlotBridge.writer U SourceClauseRowWriterCleanup.outputCell := by
  simp [installedRaw, SourceCSPFirstSlotBridge.writer,
    SourceClauseRowWriterCleanup.outputCell, SourceClauseRowWriterCleanup.savedCell,
    SourceClauseRowWriterCleanup.countCell]

theorem installedRaw_other {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) (n a : Nat)
    (x : SourceCSPFirstRowController.Stack q)
    (hs : x ≠ .inr SourceClauseRowWriterCleanup.savedCell)
    (hc : x ≠ .inr SourceClauseRowWriterCleanup.countCell) :
    installedRaw U n a x = U x := by
  simp [installedRaw, hs, hc]

#print axioms stagedBank_amb
#print axioms prefixedBank_fsb
#print axioms installedRaw_row

end EthInapproximability.CurrentPaper.SourceGenericComposite.FirstRow
