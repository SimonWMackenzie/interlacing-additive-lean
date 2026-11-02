import EthInapproximability.CurrentPaper.EntryVectorsFormula
import EthInapproximability.CurrentPaper.EntryUnaryCompare
import EthInapproximability.CurrentPaper.FamilyRowGeneric
import EthInapproximability.CurrentPaper.EntryFamilyAssembly

/-!
# Segment 2: one fixed cell program for the actual vectors table

Lane owner:b-stage4-entry-program-2, segment 2.

ONE fixed controller on `MatrixTableWriter.CellStack 25` (thirteen phases,
right-nested `BitMachineRawSequence`, every handoff charged). From the
writer's unary indices `x` (row) and `y` (column) and the fixed bank
(endpoint stream of `serializeGraph G`, unary `D = |V| + (s-3)`, `|V|`, `m = |E|`,
`M4 = 4 s m`, all other cells blank) it pushes exactly
`cellRule edges s |V| (s-3) m x y` and restores every cell:

1. copy `y`; 2. admitted division by `m` (`y % m`, `y / m`);
3. copy `x`; 4. admitted division by `D` (`x % D`, `x / D`);
5–7. copies of `y`, `M4`, comparator `y < M4`;
8. comparator `y / m = x / D` (consumes both quotients);
9. the admitted `SourceGraphPayloadMachine.BaseCell` endpoint query on
   `(x % D, y % m)`;
10–11. copy of `|V|`, comparator `x % D < |V|` (consumes `x % D`);
12. charged pop clear of `y % m`; 13. one combine step onto the answer.

`entry_runs` is the `MatrixTableWriter.EntryRuns` instance; with
`EntryVectorsFormula.vectors_formula` and `write_rowMajor` it writes
`rowMajor (GraphVectors.vectors G s)`.
-/

namespace EthInapproximability.CurrentPaper.EntryVectorsCell

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps

noncomputable section

abbrev CS := MatrixTableWriter.CellStack 25

def c (i : Fin 25) : CS := .inl i
def XI : CS := .inr 0
def YI : CS := .inr 1
def ANS : CS := .inr 2

/-- The fixed bank. -/
def cellBank (edges : List (ℕ × ℕ)) (D nV m M4 : ℕ) : Fin 25 → List Bool :=
  fun i => if i = 0 then SourceGraphPayloadMachine.endpointStream edges
    else if i = 7 then List.replicate D true
    else if i = 8 then List.replicate nV true
    else if i = 9 then List.replicate m true
    else if i = 10 then List.replicate M4 true
    else []

def st (x y : ℕ) (w : Fin 25 → List Bool) (ans : List Bool) : CS → List Bool :=
  Sum.elim w (![List.replicate x true, List.replicate y true, ans] : Fin 3 → List Bool)

/-! ## Slots -/

def sCopyY1 : Fin 3 ↪ CS := ⟨![YI, c 11, c 19], by decide⟩
def sDivY : Fin 6 ↪ CS := ⟨![c 11, c 9, c 13, c 16, c 15, c 14], by decide⟩
def sCopyX : Fin 3 ↪ CS := ⟨![XI, c 12, c 19], by decide⟩
def sDivX : Fin 6 ↪ CS := ⟨![c 12, c 7, c 13, c 18, c 17, c 14], by decide⟩
def sCopyY2 : Fin 3 ↪ CS := ⟨![YI, c 19, c 21], by decide⟩
def sCopyM4 : Fin 3 ↪ CS := ⟨![c 10, c 20, c 21], by decide⟩
def sCopyNV : Fin 3 ↪ CS := ⟨![c 8, c 20, c 19], by decide⟩

def baseMap : MatrixTableWriter.CellStack 7 → CS
  | .inl i => .inl ⟨i.val, by omega⟩
  | .inr i => (![c 18, c 16, c 24] : Fin 3 → CS) i

def baseSlots : MatrixTableWriter.CellStack 7 ↪ CS := ⟨baseMap, by decide⟩

/-! ## Programs -/

def P1 := copyProgram sCopyY1
def P2 := FamilyRowGeneric.divProgram sDivY
def P3 := copyProgram sCopyX
def P4 := FamilyRowGeneric.divProgram sDivX
def P5 := copyProgram sCopyY2
def P6 := copyProgram sCopyM4
def P7 := EntryUnaryCompare.program (c 19) (c 20) (c 21) true false false
def P8 := EntryUnaryCompare.program (c 15) (c 17) (c 22) false true false
def P9 := fun l => stackStmt baseSlots (SourceGraphPayloadMachine.BaseCell.program l)
def P10 := copyProgram sCopyNV
def P11 := EntryUnaryCompare.program (c 18) (c 20) (c 23) true false false

inductive ClearLabel where
  | loop | done
  deriving DecidableEq, Fintype

def P12 : ClearLabel → TM2.Stmt (fun _ : CS => Bool) ClearLabel (Unit × Option Bool)
  | .loop => BitMachineClearBank.clearStep (c 16) ClearLabel.loop ClearLabel.done
  | .done => .halt

abbrev V4 := Option Bool × Option Bool × Option Bool × Option Bool

def comb (b1 b2 b3 b4 : Bool) : Bool := b1 && b2 && (if b3 then b4 else true)

def P13 : Unit → TM2.Stmt (fun _ : CS => Bool) Unit V4
  | () => .pop (c 21) (fun v b => (b, v.2))
      (.pop (c 22) (fun v b => (v.1, b, v.2.2))
        (.pop (c 23) (fun v b => (v.1, v.2.1, b, v.2.2.2))
          (.pop (c 24) (fun v b => (v.1, v.2.1, v.2.2.1, b))
            (.push ANS (fun v => comb (v.1.getD false) (v.2.1.getD false)
              (v.2.2.1.getD false) (v.2.2.2.getD false)) .halt))))

/-! ## The fixed controller -/

def i13 : V4 := (none, none, none, none)
def i12 : Unit × Option Bool := ((), none)

def q12 := BitMachineRawSequence.program P12 P13 () i12 i13
def q11 := BitMachineRawSequence.program P11 q12
  (BitMachineRawSequence.leftLabel ClearLabel.loop) ((none, none) : EntryUnaryCompare.CV)
  (i12, i13)
def q10 := BitMachineRawSequence.program P10 q11
  (BitMachineRawSequence.leftLabel EntryUnaryCompare.CL.loop) (none : Option Bool)
  (((none, none) : EntryUnaryCompare.CV), (i12, i13))
def q9 := BitMachineRawSequence.program P9 q10
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
  SourceGraphPayloadMachine.BaseCell.initial
  ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13)))
def q8 := BitMachineRawSequence.program P8 q9
  (BitMachineRawSequence.leftLabel SourceGraphPayloadMachine.BaseCell.start)
  ((none, none) : EntryUnaryCompare.CV)
  (SourceGraphPayloadMachine.BaseCell.initial,
    ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13))))
def q7 := BitMachineRawSequence.program P7 q8
  (BitMachineRawSequence.leftLabel EntryUnaryCompare.CL.loop)
  ((none, none) : EntryUnaryCompare.CV)
  (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
    ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13)))))
def q6 := BitMachineRawSequence.program P6 q7
  (BitMachineRawSequence.leftLabel EntryUnaryCompare.CL.loop) (none : Option Bool)
  (((none, none) : EntryUnaryCompare.CV), (((none, none) : EntryUnaryCompare.CV),
    (SourceGraphPayloadMachine.BaseCell.initial,
    ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13))))))
def q5 := BitMachineRawSequence.program P5 q6
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool)
  ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV),
    (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
    ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13)))))))
def q4 := BitMachineRawSequence.program P4 q5
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) false
  ((none : Option Bool), ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV),
    (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
    ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13))))))))
def q3 := BitMachineRawSequence.program P3 q4
  (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start) (none : Option Bool)
  (false, ((none : Option Bool), ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV),
    (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
    ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13)))))))))
def q2 := BitMachineRawSequence.program P2 q3
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) false
  ((none : Option Bool), (false, ((none : Option Bool), ((none : Option Bool),
    (((none, none) : EntryUnaryCompare.CV),
    (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
    ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13))))))))))

def tailInit :=
  (false, ((none : Option Bool), (false, ((none : Option Bool), ((none : Option Bool),
    (((none, none) : EntryUnaryCompare.CV),
    (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
    ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13)))))))))))

/-- The single fixed cell controller. -/
def program := BitMachineRawSequence.program P1 q2
  (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start) (none : Option Bool)
  tailInit

def initControl := ((none : Option Bool), tailInit)

end

end EthInapproximability.CurrentPaper.EntryVectorsCell
