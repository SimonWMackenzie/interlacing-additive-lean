import Paper2.CodeRecursiveStepClock
import EthInapproximability.CurrentPaper.SourceClauseClearExcept
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Physical cleanup and reentry between calls of the fixed successor
compiler. -/

set_option maxHeartbeats 1000000

namespace Paper2.CodeRecursiveReentry

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.CodeRecursiveColumn Paper2.CodeRecursiveRow
open Paper2.CodeRecursiveStep

def publicCells : Finset Stack := {12,16,17,18,31,32}
def keepBefore : Finset Stack := publicCells ∪ {37,52}
def keepAfter : Finset Stack := publicCells ∪ {2,33}

noncomputable def cleanedBefore (S : Stack → List Bool) : Stack → List Bool :=
  SourceClauseClearExcept.result keepBefore S

noncomputable def withRow (S : Stack → List Bool) : Stack → List Bool :=
  Function.update (cleanedBefore S) 2 (S 52)

noncomputable def withColumn (S : Stack → List Bool) : Stack → List Bool :=
  Function.update (withRow S) 33 (S 37)

noncomputable def reentered (S : Stack → List Bool) : Stack → List Bool :=
  SourceClauseClearExcept.result keepAfter (withColumn S)

theorem before_output_row (S : Stack → List Bool) :
    cleanedBefore S 52 = S 52 := by
  exact SourceClauseClearExcept.retained keepBefore S 52 (by decide)

theorem before_output_column (S : Stack → List Bool) :
    cleanedBefore S 37 = S 37 := by
  exact SourceClauseClearExcept.retained keepBefore S 37 (by decide)

theorem before_blank (S : Stack → List Bool) (i : Stack)
    (hi : i ∉ keepBefore) : cleanedBefore S i = [] := by
  exact SourceClauseClearExcept.emptied keepBefore S i hi

theorem reentered_row (S : Stack → List Bool) :
    reentered S 2 = S 52 := by
  rw [reentered, SourceClauseClearExcept.retained keepAfter _ 2 (by decide)]
  simp [withColumn, withRow]

theorem reentered_column (S : Stack → List Bool) :
    reentered S 33 = S 37 := by
  rw [reentered, SourceClauseClearExcept.retained keepAfter _ 33 (by decide)]
  simp [withColumn]

theorem reentered_public (S : Stack → List Bool) (i : Stack)
    (hi : i ∈ publicCells) : reentered S i = S i := by
  have hbefore : i ∈ keepBefore := Finset.mem_union_left _ hi
  have hafter : i ∈ keepAfter := Finset.mem_union_left _ hi
  have h2 : i ≠ (2 : Stack) := by
    intro h; subst i; exact (by decide : (2 : Stack) ∉ publicCells) hi
  have h33 : i ≠ (33 : Stack) := by
    intro h; subst i; exact (by decide : (33 : Stack) ∉ publicCells) hi
  rw [reentered, SourceClauseClearExcept.retained keepAfter _ i hafter]
  simp [withColumn, withRow, cleanedBefore,
    Function.update_of_ne h33, Function.update_of_ne h2,
    SourceClauseClearExcept.retained keepBefore S i hbefore]

theorem reentered_other (S : Stack → List Bool) (i : Stack)
    (hi : i ∉ keepAfter) : reentered S i = [] := by
  exact SourceClauseClearExcept.emptied keepAfter (withColumn S) i hi

noncomputable def beforeProgram := SourceClauseClearExcept.program keepBefore
noncomputable def beforeTime (S : Stack → List Bool) : Nat :=
  (∑ i : Fin (SourceClauseClearExcept.workCount keepBefore),
    (S (SourceClauseClearExcept.workBank keepBefore i)).length) +
      SourceClauseClearExcept.workCount keepBefore + 2

theorem before_run (S : Stack → List Bool) :
    ((advance beforeProgram)^[beforeTime S])
      (⟨some (.clear 0), ((),none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, ((),none), cleanedBefore S⟩ := by
  exact SourceClauseClearExcept.run keepBefore S

def rowCopyIndex : Fin 3 ↪ Stack where
  toFun i := ![52,2,0] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def rowCopyProgram : BitMachineCopy.Label →
    TM2.Stmt (fun _ : Stack => Bool)
      BitMachineCopy.Label (Option Bool) :=
  fun l => BitMachineStackEmbedding.stackStmt rowCopyIndex
    (BitMachineCopy.program l)

theorem row_copy_initial_bank (S : Stack → List Bool) :
    BitMachineStackEmbedding.bank rowCopyIndex (cleanedBefore S)
      (BitMachineCopy.cfg (some .scan) none (S 52) [] []).stk =
    cleanedBefore S := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · exact (before_output_row S).symm
  · exact (before_blank S 2 (by decide)).symm
  · exact (before_blank S 0 (by decide)).symm

theorem row_copy_result_bank (S : Stack → List Bool) :
    BitMachineStackEmbedding.bank rowCopyIndex (cleanedBefore S)
      (BitMachineCopy.cfg none none (S 52) (S 52) []).stk =
    withRow S := by
  have hstk :
      (BitMachineCopy.cfg none none (S 52) (S 52) []).stk =
      Function.update
        (BitMachineCopy.cfg (some .scan) none (S 52) [] []).stk
        (1 : Fin 3) (S 52) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    row_copy_initial_bank]
  rfl

theorem row_copy_run (S : Stack → List Bool) :
    ((advance rowCopyProgram)^[2*(S 52).length+2])
      (⟨some .scan, none, cleanedBefore S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, withRow S⟩ := by
  have h := BitMachineStackRun.run rowCopyIndex (cleanedBefore S)
    BitMachineCopy.program
    (BitMachineCopy.cfg (some .scan) none (S 52) [] [])
    (2*(S 52).length+2)
  have hc := BitMachineCopy.run_correct none (S 52) []
  simp only [List.append_nil] at hc
  rw [← BitMachineCopy.run, hc] at h
  simpa only [rowCopyProgram, BitMachineStackEmbedding.stackCfg,
    row_copy_initial_bank, row_copy_result_bank] using h

def columnCopyIndex : Fin 3 ↪ Stack where
  toFun i := ![37,33,0] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def columnCopyProgram : BitMachineCopy.Label →
    TM2.Stmt (fun _ : Stack => Bool)
      BitMachineCopy.Label (Option Bool) :=
  fun l => BitMachineStackEmbedding.stackStmt columnCopyIndex
    (BitMachineCopy.program l)

theorem column_copy_initial_bank (S : Stack → List Bool) :
    BitMachineStackEmbedding.bank columnCopyIndex (withRow S)
      (BitMachineCopy.cfg (some .scan) none (S 37) [] []).stk =
    withRow S := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · change S 37 = Function.update (cleanedBefore S) 2 (S 52) 37
    rw [Function.update_of_ne (by decide : (37 : Stack) ≠ 2)]
    exact (before_output_column S).symm
  · change ([] : List Bool) =
      Function.update (cleanedBefore S) 2 (S 52) 33
    rw [Function.update_of_ne (by decide : (33 : Stack) ≠ 2)]
    exact (before_blank S 33 (by decide)).symm
  · change ([] : List Bool) =
      Function.update (cleanedBefore S) 2 (S 52) 0
    rw [Function.update_of_ne (by decide : (0 : Stack) ≠ 2)]
    exact (before_blank S 0 (by decide)).symm

theorem column_copy_result_bank (S : Stack → List Bool) :
    BitMachineStackEmbedding.bank columnCopyIndex (withRow S)
      (BitMachineCopy.cfg none none (S 37) (S 37) []).stk =
    withColumn S := by
  have hstk :
      (BitMachineCopy.cfg none none (S 37) (S 37) []).stk =
      Function.update
        (BitMachineCopy.cfg (some .scan) none (S 37) [] []).stk
        (1 : Fin 3) (S 37) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    column_copy_initial_bank]
  rfl

theorem column_copy_run (S : Stack → List Bool) :
    ((advance columnCopyProgram)^[2*(S 37).length+2])
      (⟨some .scan, none, withRow S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, withColumn S⟩ := by
  have h := BitMachineStackRun.run columnCopyIndex (withRow S)
    BitMachineCopy.program
    (BitMachineCopy.cfg (some .scan) none (S 37) [] [])
    (2*(S 37).length+2)
  have hc := BitMachineCopy.run_correct none (S 37) []
  simp only [List.append_nil] at hc
  rw [← BitMachineCopy.run, hc] at h
  simpa only [columnCopyProgram, BitMachineStackEmbedding.stackCfg,
    column_copy_initial_bank, column_copy_result_bank] using h

noncomputable def afterProgram := SourceClauseClearExcept.program keepAfter
noncomputable def afterTime (S : Stack → List Bool) : Nat :=
  (∑ i : Fin (SourceClauseClearExcept.workCount keepAfter),
    ((withColumn S) (SourceClauseClearExcept.workBank keepAfter i)).length) +
      SourceClauseClearExcept.workCount keepAfter + 2

theorem after_run (S : Stack → List Bool) :
    ((advance afterProgram)^[afterTime S])
      (⟨some (.clear 0), ((),none), withColumn S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, ((),none), reentered S⟩ := by
  exact SourceClauseClearExcept.run keepAfter (withColumn S)

noncomputable def p₁ := BitMachineRawSequence.program beforeProgram rowCopyProgram
  BitMachineCopy.Label.scan ((),none) none

noncomputable def b₁ (S : Stack → List Bool) : Nat :=
  beforeTime S + (2*(S 52).length+2)+1

theorem p₁_run (S : Stack → List Bool) :
    ∃ t ≤ b₁ S,
      ((advance p₁)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.clear 0)),
          (((),none),none), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (((),none),none), withRow S⟩ := by
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    beforeProgram rowCopyProgram (.clear 0) .scan
    ((),none) ((),none) none none
    S (cleanedBefore S) (withRow S)
    (beforeTime S) (2*(S 52).length+2)
    (before_run S) (row_copy_run S)
  exact ⟨t, by dsimp [b₁]; omega, hr⟩

noncomputable def p₂ := BitMachineRawSequence.program p₁ columnCopyProgram
  BitMachineCopy.Label.scan (((),none),none) none

noncomputable def b₂ (S : Stack → List Bool) : Nat :=
  b₁ S + (2*(S 37).length+2)+1

theorem p₂_run (S : Stack → List Bool) :
    ∃ t ≤ b₂ S,
      ((advance p₂)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (.clear 0))),
          ((((),none),none),none), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((((),none),none),none), withColumn S⟩ := by
  obtain ⟨ta,hta,ha⟩ := p₁_run S
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    p₁ columnCopyProgram
    (BitMachineRawSequence.leftLabel (.clear 0)) .scan
    (((),none),none) (((),none),none) none none
    S (withRow S) (withColumn S)
    ta (2*(S 37).length+2)
    ha (column_copy_run S)
  exact ⟨t, by dsimp [b₂]; omega, hr⟩

noncomputable def program := BitMachineRawSequence.program p₂ afterProgram
  (.clear 0) ((((),none),none),none) ((),none)

noncomputable def clock (S : Stack → List Bool) : Nat :=
  b₂ S + afterTime S+1

/-- One fixed finite TM2 program physically discards all temporary words,
copies the two successor words into their next-round inputs, and clears
their old output cells. Its clock includes each pop, each copied bit, the
empty tests, and the three sequence handoffs. -/
theorem run_exact (S : Stack → List Bool) :
    ∃ t ≤ clock S,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (.clear 0)))),
          (((((),none),none),none),((),none)), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (((((),none),none),none),((),none)), reentered S⟩ := by
  obtain ⟨ta,hta,ha⟩ := p₂_run S
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    p₂ afterProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.clear 0))) (.clear 0)
    ((((),none),none),none) ((((),none),none),none)
    ((),none) ((),none)
    S (withColumn S) (reentered S)
    ta (afterTime S)
    ha (after_run S)
  exact ⟨t, by dsimp [clock]; omega, hr⟩

#print axioms run_exact

end Paper2.CodeRecursiveReentry
