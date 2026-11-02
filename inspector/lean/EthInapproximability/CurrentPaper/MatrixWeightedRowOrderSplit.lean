import EthInapproximability.CurrentPaper.MatrixWeightedRowOrderLookup
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! # Source-preserving physical quotient and remainder for item labels -/

namespace EthInapproximability.CurrentPaper.MatrixWeightedRowOrderSplit

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := Fin 8
abbrev Label := BitMachineRawSequence.Label BitMachineCopy.Label
  MatrixUnaryDivision.Label
abbrev Control := Option Bool × Bool

def copySlots : Fin 3 ↪ Stack where
  toFun := ![0, 2, 3]
  inj' := by decide

def divisionSlots : Fin 6 ↪ Stack where
  toFun := ![2, 1, 4, 5, 6, 7]
  inj' := by decide

def copyProgram := fun l => stackStmt copySlots (BitMachineCopy.program l)
def divisionProgram := fun l => stackStmt divisionSlots (MatrixUnaryDivision.program l)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineRawSequence.program copyProgram divisionProgram
    .start none false

def initialBank (label width : ℕ) : Stack → List Bool :=
  ![List.replicate label true, List.replicate width true,
    [], [], [], [], [], []]

def copiedBank (label width : ℕ) : Stack → List Bool :=
  ![List.replicate label true, List.replicate width true,
    List.replicate label true, [], [], [], [], []]

def finalBank (label width : ℕ) : Stack → List Bool :=
  ![List.replicate label true, List.replicate width true,
    [], [], [], List.replicate (label % width) true,
    List.replicate (label / width) true, []]

theorem copy_run (label width : ℕ) :
    ((advance copyProgram)^[2 * label + 2])
      (⟨some .scan, none, initialBank label width⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, copiedBank label width⟩ := by
  let loc := BitMachineCopy.cfg (some .scan) none
    (List.replicate label true) [] []
  have hi : bank copySlots (initialBank label width) loc.stk =
      initialBank label width := by
    apply bank_eq_self
    intro k
    fin_cases k <;> rfl
  have hf : bank copySlots (initialBank label width)
      (BitMachineCopy.cfg none none (List.replicate label true)
        (List.replicate label true) []).stk = copiedBank label width := by
    funext k
    fin_cases k
    · simpa [copySlots, copiedBank, BitMachineCopy.cfg,
        BitMachineCopy.stackContents] using
        (bank_at copySlots (initialBank label width) _ (0 : Fin 3))
    · have h : ¬∃ i : Fin 3, copySlots i = (1 : Fin 8) := by decide
      simpa [initialBank, copiedBank] using
        (bank_outside copySlots (initialBank label width) _ (1 : Fin 8) h)
    · simpa [copySlots, copiedBank, BitMachineCopy.cfg,
        BitMachineCopy.stackContents] using
        (bank_at copySlots (initialBank label width) _ (1 : Fin 3))
    · simpa [copySlots, copiedBank, BitMachineCopy.cfg,
        BitMachineCopy.stackContents] using
        (bank_at copySlots (initialBank label width) _ (2 : Fin 3))
    · have h : ¬∃ i : Fin 3, copySlots i = (4 : Fin 8) := by decide
      simpa [initialBank, copiedBank] using
        (bank_outside copySlots (initialBank label width) _ (4 : Fin 8) h)
    · have h : ¬∃ i : Fin 3, copySlots i = (5 : Fin 8) := by decide
      simpa [initialBank, copiedBank] using
        (bank_outside copySlots (initialBank label width) _ (5 : Fin 8) h)
    · have h : ¬∃ i : Fin 3, copySlots i = (6 : Fin 8) := by decide
      simpa [initialBank, copiedBank] using
        (bank_outside copySlots (initialBank label width) _ (6 : Fin 8) h)
    · have h : ¬∃ i : Fin 3, copySlots i = (7 : Fin 8) := by decide
      simpa [initialBank, copiedBank] using
        (bank_outside copySlots (initialBank label width) _ (7 : Fin 8) h)
  have h := BitMachineStackRun.run copySlots (initialBank label width)
    BitMachineCopy.program loc (2 * label + 2)
  have hloc := BitMachineCopy.run_correct none
    (List.replicate label true) []
  simp only [BitMachineCopy.run, List.length_replicate,
    List.append_nil] at hloc
  change ((advance BitMachineCopy.program)^[2 * label + 2]) loc = _ at hloc
  rw [hloc] at h
  simpa only [copyProgram, stackCfg, hi, hf] using h

theorem division_run (label width : ℕ) (hw : 0 < width) :
    ((advance divisionProgram)^[MatrixUnaryDivision.exactTime label width])
      (⟨some .start, false, copiedBank label width⟩ :
        TM2.Cfg (fun _ : Stack => Bool) MatrixUnaryDivision.Label Bool) =
      ⟨none, false, finalBank label width⟩ := by
  let loc := MatrixUnaryDivision.cfg (some .start) false
    (List.replicate label true) (List.replicate width true) [] [] [] []
  have hi : bank divisionSlots (copiedBank label width) loc.stk =
      copiedBank label width := by
    apply bank_eq_self
    intro k
    fin_cases k <;> rfl
  have hf : bank divisionSlots (copiedBank label width)
      (MatrixUnaryDivision.cfg none false [] (List.replicate width true) []
        (List.replicate (label % width) true)
        (List.replicate (label / width) true) []).stk =
        finalBank label width := by
    funext k
    fin_cases k
    · have h : ¬∃ i : Fin 6, divisionSlots i = (0 : Fin 8) := by decide
      simpa [copiedBank, finalBank] using
        (bank_outside divisionSlots (copiedBank label width) _ (0 : Fin 8) h)
    · simpa [divisionSlots, finalBank, MatrixUnaryDivision.cfg] using
        (bank_at divisionSlots (copiedBank label width) _ (1 : Fin 6))
    · simpa [divisionSlots, finalBank, MatrixUnaryDivision.cfg] using
        (bank_at divisionSlots (copiedBank label width) _ (0 : Fin 6))
    · have h : ¬∃ i : Fin 6, divisionSlots i = (3 : Fin 8) := by decide
      simpa [copiedBank, finalBank] using
        (bank_outside divisionSlots (copiedBank label width) _ (3 : Fin 8) h)
    · simpa [divisionSlots, finalBank, MatrixUnaryDivision.cfg] using
        (bank_at divisionSlots (copiedBank label width) _ (2 : Fin 6))
    · simpa [divisionSlots, finalBank, MatrixUnaryDivision.cfg] using
        (bank_at divisionSlots (copiedBank label width) _ (3 : Fin 6))
    · simpa [divisionSlots, finalBank, MatrixUnaryDivision.cfg] using
        (bank_at divisionSlots (copiedBank label width) _ (4 : Fin 6))
    · simpa [divisionSlots, finalBank, MatrixUnaryDivision.cfg] using
        (bank_at divisionSlots (copiedBank label width) _ (5 : Fin 6))
  have h := BitMachineStackRun.run divisionSlots (copiedBank label width)
    MatrixUnaryDivision.program loc (MatrixUnaryDivision.exactTime label width)
  have hloc := MatrixUnaryDivision.division_run label width hw
  change ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.exactTime label width])
    loc = _ at hloc
  rw [hloc] at h
  simpa only [divisionProgram, stackCfg, hi, hf] using h

theorem split_run (label width : ℕ) (hw : 0 < width) :
    ∃ t ≤ 10 * label + 3 * width + 7,
      ((advance program)^[t])
        (⟨some (.inl .scan), (none, false), initialBank label width⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none, (none, false), finalBank label width⟩ := by
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    copyProgram divisionProgram .scan .start none none false false
    (initialBank label width) (copiedBank label width)
    (finalBank label width) (2 * label + 2)
    (MatrixUnaryDivision.exactTime label width)
    (copy_run label width) (division_run label width hw)
  refine ⟨t, ?_, ?_⟩
  · have hcost := MatrixUnaryDivision.exactTime_bound label width
    omega
  · exact hr

end EthInapproximability.CurrentPaper.MatrixWeightedRowOrderSplit
