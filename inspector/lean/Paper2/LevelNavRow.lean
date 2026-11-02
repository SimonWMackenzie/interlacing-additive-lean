import Paper2.LevelNavCol

/-! Segment 2, item (2): level-`k` row code `row_k` produced physically from
the serialized raw-row code `G_k = graphRowsCode row_k = branch3 512 510 511 A B C`
with `B = append (emit [true]) (append vertices row_k)`: drop the `branch3`
header and its unary fields `512, 510, 511`, drop child `A`, enter `B`: drop
its header and the `emit` child, drop the inner header and the `vertices`
child, take `row_k`. All on the checked `ChildNav` bank. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.LevelNavRow

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorSource
open ChildNav (nb)
open LevelNav (oc drop3 d3start)
open LevelNavCol (dk3)

def j1 := (oc, ())
def j2 := (j1, oc)
def j3 := (j2, oc)
def j4 := (j3, oc)
def j5 := (j4, ChildNav.dropCtl)
def j6 := (j5, ())
def j7 := (j6, ChildNav.dropCtl)
def j8 := (j7, ())
def j9 := (j8, ChildNav.dropCtl)

def r1 := BitMachineRawSequence.program ChildNav.copyIn drop3 d3start oc ()
def r2 := BitMachineRawSequence.program r1 ChildNav.dropUnary () j1 oc
def r3 := BitMachineRawSequence.program r2 ChildNav.dropUnary () j2 oc
def r4 := BitMachineRawSequence.program r3 ChildNav.dropUnary () j3 oc
def r5 := BitMachineRawSequence.program r4 ChildNav.dropChild ChildNav.dropStart j4
  ChildNav.dropCtl
def r6 := BitMachineRawSequence.program r5 drop3 d3start j5 ()
def r7 := BitMachineRawSequence.program r6 ChildNav.dropChild ChildNav.dropStart j6
  ChildNav.dropCtl
def r8 := BitMachineRawSequence.program r7 drop3 d3start j7 ()
def r9 := BitMachineRawSequence.program r8 ChildNav.dropChild ChildNav.dropStart j8
  ChildNav.dropCtl
def program := BitMachineRawSequence.program r9 ChildNav.takeChild ChildNav.takeStart j9
  ChildNav.takeCtl

def startLabel := ChildNav.labelOf program
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))))))))
def ctl := (j9, ChildNav.takeCtl)

def encA (q₁ q₂ s : ℕ) (row : Code) : List Bool :=
  encodeCode (.append (.emit [false]) (templateRowCode q₁ q₂ s row))
def encB (n s : ℕ) (row : Code) : List Bool :=
  encodeCode (.append (.emit [true]) (.append (vertexLabelsCode (V := Fin n) s) row))
def encC (s : ℕ) (row : Code) : List Bool :=
  encodeCode (.append (.emit [true]) (.append (auxiliaryLabelsCode s) row))

def bound (n q₁ q₂ s : ℕ) (row : Code) : ℕ :=
  (2 * (encodeCode (graphRowsCode (V := Fin n) q₁ q₂ s row)).length + 2) + 4 +
    (512 + 1) + (510 + 1) + (511 + 1) +
    ChildNav.dropBound (.append (.emit [false]) (templateRowCode q₁ q₂ s row))
      (encB n s row ++ encC s row) + 4 +
    ChildNav.dropBound (.emit [true])
      (encodeCode (.append (vertexLabelsCode (V := Fin n) s) row) ++ encC s row) + 4 +
    ChildNav.dropBound (vertexLabelsCode (V := Fin n) s) (encodeCode row ++ encC s row) +
    ChildNav.takeBound row (encC s row) + 10

theorem row_run (n q₁ q₂ s : ℕ) (row : Code) :
    let G : Code := graphRowsCode (V := Fin n) q₁ q₂ s row
    ∃ t ≤ bound n q₁ q₂ s row,
      ((advance program)^[t])
        (⟨some startLabel, ctl, nb [] [] [] (encodeCode G) []⟩ :
          TM2.Cfg (fun _ : ChildNav.Stack => Bool) _ _) =
        ⟨none, ctl, nb [] [] [] (encodeCode G) (encodeCode row)⟩ := by
  intro G
  let inp := encodeCode G
  let A : Code := .append (.emit [false]) (templateRowCode q₁ q₂ s row)
  let vs : Code := vertexLabelsCode (V := Fin n) s
  let rB := encB n s row ++ encC s row
  have h01 : inp = [true, false, false] ++
      (unary 512 ++ (unary 510 ++ (unary 511 ++ (encodeCode A ++ rB)))) := by
    simp [inp, G, A, rB, encB, encC, graphRowsCode, rowsCode, encodeCode]
  have h56 : rB = [false, true, true] ++
      (encodeCode (.emit [true]) ++ (encodeCode (.append vs row) ++ encC s row)) := by
    simp [rB, vs, encB, encodeCode]
  have h78 : encodeCode (.append vs row) ++ encC s row = [false, true, true] ++
      (encodeCode vs ++ (encodeCode row ++ encC s row)) := by
    simp [encodeCode]
  have p0 := ChildNav.copyIn_run inp []
  have p1 := dk3 [true, false, false]
    (unary 512 ++ (unary 510 ++ (unary 511 ++ (encodeCode A ++ rB)))) [] [] inp [] rfl
  rw [← h01] at p1
  have p2 := ChildNav.dropUnary_run 512 (unary 510 ++ (unary 511 ++ (encodeCode A ++ rB)))
    [] [] inp [] oc
  have p3 := ChildNav.dropUnary_run 510 (unary 511 ++ (encodeCode A ++ rB)) [] [] inp [] oc
  have p4 := ChildNav.dropUnary_run 511 (encodeCode A ++ rB) [] [] inp [] oc
  obtain ⟨t5, ht5, p5⟩ := ChildNav.dropChild_run A rB inp []
  have p6 := dk3 [false, true, true]
    (encodeCode (.emit [true]) ++ (encodeCode (.append vs row) ++ encC s row)) [] [] inp [] rfl
  rw [← h56] at p6
  obtain ⟨t7, ht7, p7⟩ := ChildNav.dropChild_run (.emit [true])
    (encodeCode (.append vs row) ++ encC s row) inp []
  have p8 := dk3 [false, true, true] (encodeCode vs ++ (encodeCode row ++ encC s row))
    [] [] inp [] rfl
  rw [← h78] at p8
  obtain ⟨t9, ht9, p9⟩ := ChildNav.dropChild_run vs (encodeCode row ++ encC s row) inp []
  obtain ⟨t10, ht10, p10⟩ := ChildNav.takeChild_run row (encC s row) inp
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs ChildNav.copyIn drop3 .scan d3start
    oc oc () () _ _ _ _ _ p0 p1
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs r1 ChildNav.dropUnary (BitMachineRawSequence.leftLabel .scan) ()
    j1 j1 oc (some false) _ _ _ _ _ q1 p2
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs r2 ChildNav.dropUnary (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)) ()
    j2 (j1, some false) oc (some false) _ _ _ _ _ q2 p3
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs r3 ChildNav.dropUnary (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan))) ()
    j3 (j2, some false) oc (some false) _ _ _ _ _ q3 p4
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs r4 ChildNav.dropChild (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan))))
    ChildNav.dropStart j4 (j3, some false) ChildNav.dropCtl ChildNav.dropCtl _ _ _ _ _ q4 p5
  obtain ⟨u6, hu6, q6⟩ := BitMachineRawSequence.runs r5 drop3 (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan))))) d3start
    j5 j5 () () _ _ _ _ _ q5 p6
  obtain ⟨u7, hu7, q7⟩ := BitMachineRawSequence.runs r6 ChildNav.dropChild (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan))))))
    ChildNav.dropStart j6 j6 ChildNav.dropCtl ChildNav.dropCtl _ _ _ _ _ q6 p7
  obtain ⟨u8, hu8, q8⟩ := BitMachineRawSequence.runs r7 drop3 (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan))))))) d3start
    j7 j7 () () _ _ _ _ _ q7 p8
  obtain ⟨u9, hu9, q9⟩ := BitMachineRawSequence.runs r8 ChildNav.dropChild (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan))))))))
    ChildNav.dropStart j8 j8 ChildNav.dropCtl ChildNav.dropCtl _ _ _ _ _ q8 p9
  obtain ⟨u10, hu10, q10⟩ := BitMachineRawSequence.runs r9 ChildNav.takeChild (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)))))))))
    ChildNav.takeStart j9 j9 ChildNav.takeCtl ChildNav.takeCtl _ _ _ _ _ q9 p10
  refine ⟨u10, ?_, q10⟩
  have hinp : inp.length = (encodeCode (graphRowsCode (V := Fin n) q₁ q₂ s row)).length := rfl
  have ht5' : t5 ≤ ChildNav.dropBound (.append (.emit [false]) (templateRowCode q₁ q₂ s row))
      (encB n s row ++ encC s row) := ht5
  have ht9' : t9 ≤ ChildNav.dropBound (vertexLabelsCode (V := Fin n) s)
      (encodeCode row ++ encC s row) := ht9
  have ht7' : t7 ≤ ChildNav.dropBound (.emit [true])
      (encodeCode (.append (vertexLabelsCode (V := Fin n) s) row) ++ encC s row) := ht7
  simp only [bound]
  omega

end

#print axioms row_run

end Paper2.LevelNavRow
