import Paper2.LevelNav

/-! Segment 2, item (2): level-`k` column code `col_k` produced physically
from the serialized row entry code `E_k = append (ticket w) (taggedCode col_k)`
(for the next request level). Path: drop the `append` header, drop the
`ticket w` child, drop the `branch3` header and its three unary fields
`256, 254, 255`, enter the first alternative
`append (emit [false]) (rawCode col_k)`: drop its header and the `emit`
child, drop the `rawCode` header, drop the `copies (s+1)` header, take the
first child. All on the checked `ChildNav` bank. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.LevelNavCol

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorSource
open ChildNav (nb)
open LevelNav (oc drop3 d3start)

theorem dk3 (pre w scanned pend inp outp : List Bool) (h : pre.length = 3) :
    ((advance drop3)^[4]) (⟨some d3start, (), nb (pre ++ w)
      scanned pend inp outp⟩ : TM2.Cfg (fun _ : ChildNav.Stack => Bool) _ _) =
      ⟨none, (), nb w scanned pend inp outp⟩ :=
  ChildNav.dropK_run 3 0 (by omega) pre h w scanned pend inp outp

def k1 := (oc, ())
def k2 := (k1, ChildNav.dropCtl)
def k3 := (k2, ())
def k4 := (k3, oc)
def k5 := (k4, oc)
def k6 := (k5, oc)
def k7 := (k6, ())
def k8 := (k7, ChildNav.dropCtl)
def k9 := (k8, ())
def k10 := (k9, ())

def c1 := BitMachineRawSequence.program ChildNav.copyIn drop3 d3start oc ()
def c2 := BitMachineRawSequence.program c1 ChildNav.dropChild ChildNav.dropStart k1
  ChildNav.dropCtl
def c3 := BitMachineRawSequence.program c2 drop3 d3start k2 ()
def c4 := BitMachineRawSequence.program c3 ChildNav.dropUnary () k3 oc
def c5 := BitMachineRawSequence.program c4 ChildNav.dropUnary () k4 oc
def c6 := BitMachineRawSequence.program c5 ChildNav.dropUnary () k5 oc
def c7 := BitMachineRawSequence.program c6 drop3 d3start k6 ()
def c8 := BitMachineRawSequence.program c7 ChildNav.dropChild ChildNav.dropStart k7
  ChildNav.dropCtl
def c9 := BitMachineRawSequence.program c8 drop3 d3start k8 ()
def c10 := BitMachineRawSequence.program c9 drop3 d3start k9 ()
def program := BitMachineRawSequence.program c10 ChildNav.takeChild ChildNav.takeStart k10
  ChildNav.takeCtl

def startLabel := ChildNav.labelOf program
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))))))))
def ctl := (k10, ChildNav.takeCtl)

/-- The words left after each phase (public, determined by the code). -/
def R1 (q₁ q₂ s : ℕ) (col : Code) : List Bool :=
  encodeCode (.append (.emit [true, false]) (fixedTailCode q₁ q₂ s col)) ++
    encodeCode (.append (.emit [true, true]) (outerCode q₁ q₂ s col))
def R2 (q₁ q₂ s : ℕ) (col : Code) : List Bool :=
  encodeCode (copies s (outerCode q₁ q₂ s col)) ++ R1 q₁ q₂ s col
def R3 (q₁ q₂ s : ℕ) (col : Code) : List Bool :=
  encodeCode (copies s col) ++ R2 q₁ q₂ s col

def bound (q₁ q₂ s w : ℕ) (col : Code) : ℕ :=
  (2 * (encodeCode (.append (.ticket w) (taggedCode q₁ q₂ s col))).length + 2) + 4 +
    ChildNav.dropBound (.ticket w) (encodeCode (taggedCode q₁ q₂ s col)) + 4 +
    (256 + 1) + (254 + 1) + (255 + 1) + 4 +
    ChildNav.dropBound (.emit [false]) (encodeCode (rawCode q₁ q₂ s col) ++ R1 q₁ q₂ s col) +
    4 + 4 + ChildNav.takeBound col (R3 q₁ q₂ s col) + 11

theorem col_run (q₁ q₂ s w : ℕ) (col : Code) :
    let E : Code := .append (.ticket w) (taggedCode q₁ q₂ s col)
    ∃ t ≤ bound q₁ q₂ s w col,
      ((advance program)^[t])
        (⟨some startLabel, ctl, nb [] [] [] (encodeCode E) []⟩ :
          TM2.Cfg (fun _ : ChildNav.Stack => Bool) _ _) =
        ⟨none, ctl, nb [] [] [] (encodeCode E) (encodeCode col)⟩ := by
  intro E
  let inp := encodeCode E
  let T := encodeCode (taggedCode q₁ q₂ s col)
  let encA := encodeCode (.append (.emit [false]) (rawCode q₁ q₂ s col))
  let r1 := R1 q₁ q₂ s col
  let R0 := encA ++ r1
  let encRaw := encodeCode (rawCode q₁ q₂ s col)
  have h01 : inp = [false, true, true] ++ (encodeCode (.ticket w) ++ T) := by
    simp [inp, E, T, encodeCode]
  have h23 : T = [true, false, false] ++
      (unary 256 ++ (unary 254 ++ (unary 255 ++ R0))) := by
    simp [T, R0, encA, r1, R1, taggedCode, encodeCode]
  have h67 : R0 = [false, true, true] ++ (encodeCode (.emit [false]) ++ (encRaw ++ r1)) := by
    simp [R0, encA, encRaw, encodeCode]
  have h89 : encRaw ++ r1 = [false, true, true] ++
      (encodeCode (copies (s + 1) col) ++ R2 q₁ q₂ s col) := by
    simp [encRaw, r1, R2, rawCode, encodeCode]
  have h910 : encodeCode (copies (s + 1) col) ++ R2 q₁ q₂ s col =
      [false, true, true] ++ (encodeCode col ++ R3 q₁ q₂ s col) := by
    simp [R3, copies, encodeCode]
  -- phases
  have p0 := ChildNav.copyIn_run inp []
  have p1 := dk3 [false, true, true] (encodeCode (.ticket w) ++ T) [] [] inp [] rfl
  rw [← h01] at p1
  obtain ⟨t2, ht2, p2⟩ := ChildNav.dropChild_run (.ticket w) T inp []
  have p3 := dk3 [true, false, false] (unary 256 ++ (unary 254 ++ (unary 255 ++ R0)))
    [] [] inp [] rfl
  rw [← h23] at p3
  have p4 := ChildNav.dropUnary_run 256 (unary 254 ++ (unary 255 ++ R0)) [] [] inp [] oc
  have p5 := ChildNav.dropUnary_run 254 (unary 255 ++ R0) [] [] inp [] oc
  have p6 := ChildNav.dropUnary_run 255 R0 [] [] inp [] oc
  have p7 := dk3 [false, true, true] (encodeCode (.emit [false]) ++ (encRaw ++ r1))
    [] [] inp [] rfl
  rw [← h67] at p7
  obtain ⟨t8, ht8, p8⟩ := ChildNav.dropChild_run (.emit [false]) (encRaw ++ r1) inp []
  have p9 := dk3 [false, true, true] (encodeCode (copies (s + 1) col) ++ R2 q₁ q₂ s col)
    [] [] inp [] rfl
  rw [← h89] at p9
  have p10 := dk3 [false, true, true] (encodeCode col ++ R3 q₁ q₂ s col) [] [] inp [] rfl
  rw [← h910] at p10
  obtain ⟨t11, ht11, p11⟩ := ChildNav.takeChild_run col (R3 q₁ q₂ s col) inp
  -- sequencing
  obtain ⟨r1', hr1, q1⟩ := BitMachineRawSequence.runs ChildNav.copyIn drop3 .scan d3start
    oc oc () () _ _ _ _ _ p0 p1
  obtain ⟨r2, hr2, q2⟩ := BitMachineRawSequence.runs c1 ChildNav.dropChild
    (BitMachineRawSequence.leftLabel .scan) ChildNav.dropStart
    k1 k1 ChildNav.dropCtl ChildNav.dropCtl _ _ _ _ _ q1 p2
  obtain ⟨r3, hr3, q3⟩ := BitMachineRawSequence.runs c2 drop3
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)) d3start
    k2 k2 () () _ _ _ _ _ q2 p3
  obtain ⟨r4, hr4, q4⟩ := BitMachineRawSequence.runs c3 ChildNav.dropUnary
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel .scan))) ()
    k3 k3 oc (some false) _ _ _ _ _ q3 p4
  obtain ⟨r5, hr5, q5⟩ := BitMachineRawSequence.runs c4 ChildNav.dropUnary
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)))) ()
    k4 (k3, some false) oc (some false) _ _ _ _ _ q4 p5
  obtain ⟨r6, hr6, q6⟩ := BitMachineRawSequence.runs c5 ChildNav.dropUnary
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel .scan))))) ()
    k5 (k4, some false) oc (some false) _ _ _ _ _ q5 p6
  obtain ⟨r7, hr7, q7⟩ := BitMachineRawSequence.runs c6 drop3
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)))))) d3start
    k6 (k5, some false) () () _ _ _ _ _ q6 p7
  obtain ⟨r8, hr8, q8⟩ := BitMachineRawSequence.runs c7 ChildNav.dropChild
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel .scan))))))) ChildNav.dropStart
    k7 k7 ChildNav.dropCtl ChildNav.dropCtl _ _ _ _ _ q7 p8
  obtain ⟨r9, hr9, q9⟩ := BitMachineRawSequence.runs c8 drop3
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan))))))))
    d3start k8 k8 () () _ _ _ _ _ q8 p9
  obtain ⟨r10, hr10, q10⟩ := BitMachineRawSequence.runs c9 drop3
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel .scan)))))))))
    d3start k9 k9 () () _ _ _ _ _ q9 p10
  obtain ⟨r11, hr11, q11⟩ := BitMachineRawSequence.runs c10 ChildNav.takeChild
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan))))))))))
    ChildNav.takeStart k10 k10 ChildNav.takeCtl ChildNav.takeCtl _ _ _ _ _ q10 p11
  refine ⟨r11, ?_, q11⟩
  have hinp : inp.length =
      (encodeCode (.append (.ticket w) (taggedCode q₁ q₂ s col))).length := rfl
  have ht2' : t2 ≤ ChildNav.dropBound (.ticket w) (encodeCode (taggedCode q₁ q₂ s col)) := ht2
  have ht8' : t8 ≤ ChildNav.dropBound (.emit [false])
      (encodeCode (rawCode q₁ q₂ s col) ++ R1 q₁ q₂ s col) := ht8
  simp only [bound]
  omega

end

#print axioms col_run

end Paper2.LevelNavCol
