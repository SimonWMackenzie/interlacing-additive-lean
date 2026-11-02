import CurrentAdditive.V40RandomPermittedFamily
import CurrentAdditive.MachineInvokeFull
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.SourceFieldWriter

/-! A fixed physical requester. The only stored inputs are unary B, unary k,
and the printed encoded instance. Copies preserve those three source cells;
all numerator arithmetic, binary serialization, matrix projection and request
concatenation occur in the actual finite program below. -/

noncomputable section
namespace CurrentAdditive.V40MidpointRequest

open Paper2 Turing EthInapproximability.CurrentPaper BitMachineEncoding
open EncodedCommunication BitMachineStackEmbedding
open MinimumRatioContext

abbrev FieldM := SourceFieldWriter.unaryFieldMachine
abbrev MatrixM := AFront.Projection.matrixMachine
def N : ℕ := FieldM.stackCount + MatrixM.stackCount
abbrev Stack := Fin (32 + N)
abbrev Bank := Stack → List Bool
def low (i : Fin 32) : Stack := ⟨i.val, by have hi := i.isLt; omega⟩

@[simp] theorem low_eq_iff (i j : Fin 32) : low i = low j ↔ i = j := by
  constructor
  · intro he; exact Fin.ext (congrArg (fun k : Stack => k.val) he)
  · intro he; rw [he]

def slots (M : BitMachine.Machine) (offset : ℕ) (hfit : offset + M.stackCount ≤ N)
    (source target : Fin 32) (hne : source ≠ target)
    (hs : source ≠ 4) (ht : target ≠ 4) : MachineInvokeCore.Slots M N where
  machine := {
    toFun := fun i => ⟨32 + offset + i.val, by have hi := i.isLt; omega⟩
    inj' := by intro a b he; apply Fin.ext; have h := congrArg Fin.val he; simp only at h; omega }
  source := low source
  target := low target
  scratch := low 4
  source_target := by intro he; exact hne ((low_eq_iff _ _).mp he)
  source_scratch := by intro he; exact hs ((low_eq_iff _ _).mp he)
  target_scratch := by intro he; exact ht ((low_eq_iff _ _).mp he)
  source_machine := by
    intro i he; have h := congrArg Fin.val he; have hi := source.isLt
    change source.val = 32 + offset + i.val at h; omega
  target_machine := by
    intro i he; have h := congrArg Fin.val he; have hi := target.isLt
    change target.val = 32 + offset + i.val at h; omega
  scratch_machine := by
    intro i he; have h := congrArg Fin.val he
    change 4 = 32 + offset + i.val at h; omega

def fieldSlots := slots FieldM 0 (by simp [N]) 2 3 (by decide) (by decide) (by decide)
def matrixSlots := slots MatrixM FieldM.stackCount (by simp [N])
  5 6 (by decide) (by decide) (by decide)

def copySlots (source target : Fin 32) (hne : source ≠ target)
    (hs : source ≠ 4) (ht : target ≠ 4) : Fin 3 ↪ Stack :=
  ⟨![low source, low target, low 4], by
    intro a b he
    have h := congrArg Fin.val he
    fin_cases a <;> fin_cases b <;> simp_all [low, Fin.ext_iff]⟩

def bSlots := copySlots 0 2 (by decide) (by decide) (by decide)
def kSlots := copySlots 1 2 (by decide) (by decide) (by decide)
def outputSlots := copySlots 6 7 (by decide) (by decide) (by decide)
def headerSlots := copySlots 3 7 (by decide) (by decide) (by decide)
def copyB := MatrixStage4ScalarPreparationOps.copyProgram bSlots
def copyK := MatrixStage4ScalarPreparationOps.copyProgram kSlots
def copyMatrix := MatrixStage4ScalarPreparationOps.copyProgram outputSlots
def copyHeader := MatrixStage4ScalarPreparationOps.copyProgram headerSlots
def fieldProgram := MachineInvokeFull.program fieldSlots
def matrixProgram := MachineInvokeFull.program matrixSlots

def pBB := BitMachineRawSequence.program copyB copyB .scan (none : Option Bool) none
def sBB := BitMachineRawSequence.leftLabel (LB := BitMachineCopy.Label) (.scan : BitMachineCopy.Label)
def cBB := ((none : Option Bool), (none : Option Bool))
def pBBK := BitMachineRawSequence.program pBB copyK .scan cBB none
def sBBK := BitMachineRawSequence.leftLabel (LB := BitMachineCopy.Label) sBB
def cBBK := (cBB, (none : Option Bool))
def pField := BitMachineRawSequence.program pBBK fieldProgram (MachineInvokeFull.start fieldSlots)
  cBBK (MachineInvokeFull.control fieldSlots)
def sField := BitMachineRawSequence.leftLabel (LB := MachineInvokeFull.LabelFull FieldM) sBBK
def cField := (cBBK, MachineInvokeFull.control fieldSlots)
def pMatrix := BitMachineRawSequence.program pField matrixProgram (MachineInvokeFull.start matrixSlots)
  cField (MachineInvokeFull.control matrixSlots)
def sMatrix := BitMachineRawSequence.leftLabel (LB := MachineInvokeFull.LabelFull MatrixM) sField
def cMatrix := (cField, MachineInvokeFull.control matrixSlots)
def pOutput := BitMachineRawSequence.program pMatrix copyMatrix .scan cMatrix none
def sOutput := BitMachineRawSequence.leftLabel (LB := BitMachineCopy.Label) sMatrix
def cOutput := (cMatrix, (none : Option Bool))
def program := BitMachineRawSequence.program pOutput copyHeader .scan cOutput none
def start := BitMachineRawSequence.leftLabel (LB := BitMachineCopy.Label) sOutput
def control := (cOutput, (none : Option Bool))

def fieldClock (B k : ℕ) := MachineInvokeFull.uniformBound FieldM
  (List.replicate (2*B+k) true) ((UnaryBinaryEncoding.coefficient+10)*(2*B+k+1)^2)
def matrixClock (word : List Bool) := MachineInvokeFull.uniformBound MatrixM word (3*(word.length+1))
def clock (B k : ℕ) (word : List Bool) :=
  (2*B+2) + (2*B+2) + (2*k+2) + fieldClock B k + matrixClock word +
  (2*(AFront.Projection.matrixPart word).length+2) +
  (2*(natField (2*B+k)).length+2) + 6

def final (S : Bank) (B k : ℕ) (word : List Bool) : Bank :=
  Function.update
    (Function.update
      (Function.update
        (Function.update S (low 2) (List.replicate (2*B+k) true))
        (low 3) (natField (2*B+k)))
      (low 6) (AFront.Projection.matrixPart word))
    (low 7) (natField (2*B+k) ++ AFront.Projection.matrixPart word)

theorem b_copy (S : Bank) (h4 : S (low 4) = []) :
    ((advance copyB)^[2*(S (low 0)).length+2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, Function.update S (low 2) (S (low 0) ++ S (low 2))⟩ :=
  MatrixStage4ScalarPreparationOps.copy_run bSlots S h4

theorem k_copy (S : Bank) (h4 : S (low 4) = []) :
    ((advance copyK)^[2*(S (low 1)).length+2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, Function.update S (low 2) (S (low 1) ++ S (low 2))⟩ :=
  MatrixStage4ScalarPreparationOps.copy_run kSlots S h4

theorem copy_numerator (S : Bank) (B k : ℕ)
    (hB : S (low 0) = List.replicate B true)
    (hk : S (low 1) = List.replicate k true)
    (h2 : S (low 2) = []) (h4 : S (low 4) = []) :
    ∃ t ≤ (2*B+2)+(2*B+2)+(2*k+2)+2,
      ((advance pBBK)^[t])
        (⟨some sBBK, cBBK, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, cBBK, Function.update S (low 2) (List.replicate (2*B+k) true)⟩ := by
  let S1 := Function.update S (low 2) (List.replicate B true)
  let S2 := Function.update S (low 2) (List.replicate B true ++ List.replicate B true)
  have h1 : ((advance copyB)^[2*B+2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) = ⟨none, none, S1⟩ := by
    simpa only [hB, List.length_replicate, h2, List.append_nil] using b_copy S h4
  have h2run := b_copy S1 (by simpa [S1, Function.update] using h4)
  have h2' : ((advance copyB)^[2*B+2])
      (⟨some .scan, none, S1⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) = ⟨none, none, S2⟩ := by
    simpa [S1, S2, Function.update, hB] using h2run
  obtain ⟨a, ha, hrA⟩ := BitMachineRawSequence.runs copyB copyB .scan .scan
    (none : Option Bool) none none none S S1 S2 (2*B+2) (2*B+2) h1 h2'
  have hkRun := k_copy S2 (by simpa [S2, Function.update] using h4)
  have hrep : List.replicate k true ++ (List.replicate B true ++ List.replicate B true) =
      List.replicate (2*B+k) true := by
    rw [← List.replicate_add, ← List.replicate_add]
    congr 1
    omega
  have hk' : ((advance copyK)^[2*k+2])
      (⟨some .scan, none, S2⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, Function.update S (low 2) (List.replicate (2*B+k) true)⟩ := by
    simpa [S2, Function.update, hk, ← List.replicate_add,
      show k + (B + B) = 2*B+k by omega] using hkRun
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs pBB copyK sBB .scan cBB cBB none none
    S S2 _ a (2*k+2) (by simpa only [pBB, sBB, cBB] using hrA) hk'
  exact ⟨t, by omega, by simpa only [pBBK, sBBK, cBBK] using hr⟩

#print axioms copy_numerator

end CurrentAdditive.V40MidpointRequest
