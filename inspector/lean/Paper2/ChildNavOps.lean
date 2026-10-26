import Paper2.ChildNav
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! `dropChild`, `takeChild` and `copyIn` as fixed sequenced programs. -/

namespace Paper2.ChildNav

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def exStart := BitMachineRawSequence.leftLabel (LB := CodeExtract.FinishLabel)
  (BitMachineRawSequence.leftLabel (LB := CodeScanner.Label) BitMachineCopy.Label.scan)
def exCtl : (Option Bool × CodeScanner.Control) × Option Bool :=
  ((none, ((none, none), none)), none)

theorem extract_run' (c : Code) (rest inp outp : List Bool) :
    ∃ t ≤ 12 * (encodeCode c ++ rest).length + 12,
      ((advance extractP)^[t])
        (⟨some exStart, exCtl, nb (encodeCode c ++ rest) [] [true] inp outp⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, exCtl, nb (encodeCode c) rest [] inp outp⟩ :=
  extract_run c rest inp outp

def slots3 (a b c : Stack) (h : Function.Injective ![a, b, c]) : Fin 3 ↪ Stack := ⟨![a, b, c], h⟩

def inSlots : Fin 3 ↪ Stack := slots3 inpC srcC scratchC (by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [inpC, srcC, scratchC])
def backSlots : Fin 3 ↪ Stack := slots3 scannedC srcC scratchC (by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [scannedC, srcC, scratchC])
def outSlots : Fin 3 ↪ Stack := slots3 srcC outpC scratchC (by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [outpC, srcC, scratchC])

def copyIn := MatrixStage4ScalarPreparationOps.copyProgram inSlots
def copyBack := MatrixStage4ScalarPreparationOps.copyProgram backSlots
def copyOut := MatrixStage4ScalarPreparationOps.copyProgram outSlots

theorem copyIn_run (inp outp : List Bool) :
    ((advance copyIn)^[2 * inp.length + 2])
      (⟨some .scan, none, nb [] [] [] inp outp⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, nb inp [] [] inp outp⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run inSlots (nb [] [] [] inp outp) rfl
  have e0 : nb [] [] [] inp outp (inSlots 0) = inp := rfl
  have e1 : nb [] [] [] inp outp (inSlots 1) = [] := rfl
  rw [e0, e1, List.append_nil, show inSlots 1 = srcC from rfl, up_src] at h
  exact h

theorem copyBack_run (w inp outp : List Bool) :
    ((advance copyBack)^[2 * w.length + 2])
      (⟨some .scan, none, nb [] w [] inp outp⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, nb w w [] inp outp⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run backSlots (nb [] w [] inp outp) rfl
  have e0 : nb [] w [] inp outp (backSlots 0) = w := rfl
  have e1 : nb [] w [] inp outp (backSlots 1) = [] := rfl
  rw [e0, e1, List.append_nil, show backSlots 1 = srcC from rfl, up_src] at h
  exact h

theorem copyOut_run (code rest inp : List Bool) :
    ((advance copyOut)^[2 * code.length + 2])
      (⟨some .scan, none, nb code rest [] inp []⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, nb code rest [] inp code⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run outSlots (nb code rest [] inp []) rfl
  have e0 : nb code rest [] inp [] (outSlots 0) = code := rfl
  have e1 : nb code rest [] inp [] (outSlots 1) = [] := rfl
  rw [e0, e1, List.append_nil, show outSlots 1 = outpC from rfl, up_outp] at h
  exact h

/-! ### dropChild: pushPend, extract, clear src, copy scanned back, clear scanned -/

def clrSrc := clearCell srcC
def clrScanned := clearCell scannedC

def dA := BitMachineRawSequence.program pushPend extractP exStart () exCtl
def dB := BitMachineRawSequence.program dA clrSrc () ((), exCtl) (none : Option Bool)
def dC := BitMachineRawSequence.program dB copyBack .scan (((), exCtl), (none : Option Bool))
  (none : Option Bool)
def dropChild := BitMachineRawSequence.program dC clrScanned ()
  ((((), exCtl), (none : Option Bool)), (none : Option Bool)) (none : Option Bool)
def labelOf {L σ K : Type*} (_P : L → TM2.Stmt (fun _ : K => Bool) L σ) (l : L) : L := l

def dropStart := labelOf dropChild
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel ()))))
def dropCtl := (((((), exCtl), (none : Option Bool)), (none : Option Bool)),
  (none : Option Bool))

def dropBound (c : Code) (w : List Bool) : Nat :=
  1 + (12 * (encodeCode c ++ w).length + 12) + (codeSize c + 1) +
    (2 * w.length + 2) + (w.length + 1) + 4

theorem dropChild_run (c : Code) (w inp outp : List Bool) :
    ∃ t ≤ dropBound c w,
      ((advance dropChild)^[t])
        (⟨some dropStart, dropCtl, nb (encodeCode c ++ w) [] [] inp outp⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, dropCtl, nb w [] [] inp outp⟩ := by
  have p1 : ((advance pushPend)^[1]) (⟨some (), (), nb (encodeCode c ++ w) [] [] inp outp⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Unit Unit) =
      ⟨none, (), nb (encodeCode c ++ w) [] [true] inp outp⟩ :=
    pushPend_run (encodeCode c ++ w) [] inp outp
  obtain ⟨t2, ht2, p2⟩ := extract_run' c w inp outp
  have p3 := clearCell_run srcC (encodeCode c) (nb (encodeCode c) w [] inp outp) none rfl
  rw [up_src, encodeCode_length] at p3
  have p4 := copyBack_run w inp outp
  have p5 := clearCell_run scannedC w (nb w w [] inp outp) none rfl
  rw [up_scanned] at p5
  obtain ⟨s1, hs1, r1⟩ := BitMachineRawSequence.runs pushPend extractP () exStart
    () () exCtl exCtl _ _ _ _ _ p1 p2
  obtain ⟨s2, hs2, r2⟩ := BitMachineRawSequence.runs dA clrSrc
    (BitMachineRawSequence.leftLabel ()) () ((), exCtl) ((), exCtl) none none _ _ _ _ _ r1 p3
  obtain ⟨s3, hs3, r3⟩ := BitMachineRawSequence.runs dB copyBack
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel ())) .scan
    (((), exCtl), none) (((), exCtl), none) none none _ _ _ _ _ r2 p4
  obtain ⟨s4, hs4, r4⟩ := BitMachineRawSequence.runs dC clrScanned
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel ()))) ()
    ((((), exCtl), none), none) ((((), exCtl), none), none) none none _ _ _ _ _ r3 p5
  refine ⟨s4, ?_, r4⟩
  simp only [dropBound]
  omega

/-! ### takeChild: pushPend, extract, copy src → outp, clear src, clear scanned -/

def tA := BitMachineRawSequence.program pushPend extractP exStart () exCtl
def tB := BitMachineRawSequence.program tA copyOut .scan ((), exCtl) (none : Option Bool)
def tC := BitMachineRawSequence.program tB clrSrc () (((), exCtl), (none : Option Bool))
  (none : Option Bool)
def takeChild := BitMachineRawSequence.program tC clrScanned ()
  ((((), exCtl), (none : Option Bool)), (none : Option Bool)) (none : Option Bool)
def takeStart := labelOf takeChild
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel ()))))
def takeCtl := dropCtl

def takeBound (c : Code) (w : List Bool) : Nat :=
  1 + (12 * (encodeCode c ++ w).length + 12) + (2 * codeSize c + 2) +
    (codeSize c + 1) + (w.length + 1) + 4

theorem takeChild_run (c : Code) (w inp : List Bool) :
    ∃ t ≤ takeBound c w,
      ((advance takeChild)^[t])
        (⟨some takeStart, takeCtl, nb (encodeCode c ++ w) [] [] inp []⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, takeCtl, nb [] [] [] inp (encodeCode c)⟩ := by
  have p1 : ((advance pushPend)^[1]) (⟨some (), (), nb (encodeCode c ++ w) [] [] inp []⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Unit Unit) =
      ⟨none, (), nb (encodeCode c ++ w) [] [true] inp []⟩ :=
    pushPend_run (encodeCode c ++ w) [] inp []
  obtain ⟨t2, ht2, p2⟩ := extract_run' c w inp []
  have p3 := copyOut_run (encodeCode c) w inp
  rw [encodeCode_length] at p3
  have p4 := clearCell_run srcC (encodeCode c) (nb (encodeCode c) w [] inp (encodeCode c))
    none rfl
  rw [up_src, encodeCode_length] at p4
  have p5 := clearCell_run scannedC w (nb [] w [] inp (encodeCode c)) none rfl
  rw [up_scanned] at p5
  obtain ⟨s1, hs1, r1⟩ := BitMachineRawSequence.runs pushPend extractP () exStart
    () () exCtl exCtl _ _ _ _ _ p1 p2
  obtain ⟨s2, hs2, r2⟩ := BitMachineRawSequence.runs tA copyOut
    (BitMachineRawSequence.leftLabel ()) .scan ((), exCtl) ((), exCtl) none none _ _ _ _ _ r1 p3
  obtain ⟨s3, hs3, r3⟩ := BitMachineRawSequence.runs tB clrSrc
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel ())) ()
    (((), exCtl), none) (((), exCtl), none) none none _ _ _ _ _ r2 p4
  obtain ⟨s4, hs4, r4⟩ := BitMachineRawSequence.runs tC clrScanned
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel ()))) ()
    ((((), exCtl), none), none) ((((), exCtl), none), none) none none _ _ _ _ _ r3 p5
  refine ⟨s4, ?_, r4⟩
  simp only [takeBound]
  omega

#print axioms dropChild_run
#print axioms takeChild_run

end Paper2.ChildNav
