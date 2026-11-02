import Paper2.ChildNavOps
import Paper2.FullSupport

/-! Segment 2, item (2): the two sub-codes consumed by
`RequestSelect.select_generic` produced physically from the serialized
level-`k+1` codes (charged, not supplied):

* row entry `E_k = append (ticket w) (taggedCode col_k)` is the first child of
  `row_{k+1} = copies Q E_k` (`Q > 0`): copy the code in, drop the 3-bit
  `append` header, take the first child;
* raw-row code `G_k = graphRowsCode row_k` is the first child of the second
  child of `col_{k+1} = append (ticket Q) (copies w G_k)` (`w > 0`): copy in,
  drop the header, drop the ticket child, drop the next header, take the
  first child.

Both run on the checked `ChildNav` bank (`nb src scanned pend inp outp`),
with the input code retained in `inp` and the result in `outp`. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.LevelNav

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorSource
open ChildNav (nb)

abbrev oc := (none : Option Bool)

def drop3 := ChildNav.dropK 3
def d3start : Fin 4 := ⟨0, by omega⟩

/-! ### First child of an `append` -/

def l1 := BitMachineRawSequence.program ChildNav.copyIn drop3 d3start oc ()
def leftProgram := BitMachineRawSequence.program l1 ChildNav.takeChild ChildNav.takeStart
  (oc, ()) ChildNav.takeCtl

def leftStart := ChildNav.labelOf leftProgram
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
def leftCtl := ((oc, ()), ChildNav.takeCtl)

def leftBound (a b : Code) : Nat :=
  (2 * (encodeCode (.append a b)).length + 2) + 4 + ChildNav.takeBound a (encodeCode b) + 2

theorem drop3_run (w scanned pend inp outp : List Bool) :
    ((advance drop3)^[4]) (⟨some d3start, (), nb ([false, true, true] ++ w)
      scanned pend inp outp⟩ : TM2.Cfg (fun _ : ChildNav.Stack => Bool) _ _) =
      ⟨none, (), nb w scanned pend inp outp⟩ :=
  ChildNav.dropK_run 3 0 (by omega) [false, true, true] rfl w scanned pend inp outp

theorem left_run (a b : Code) :
    ∃ t ≤ leftBound a b,
      ((advance leftProgram)^[t])
        (⟨some leftStart, leftCtl, nb [] [] [] (encodeCode (.append a b)) []⟩ :
          TM2.Cfg (fun _ : ChildNav.Stack => Bool) _ _) =
        ⟨none, leftCtl, nb [] [] [] (encodeCode (.append a b)) (encodeCode a)⟩ := by
  let inp := encodeCode (.append a b)
  have p1 := ChildNav.copyIn_run inp []
  have hsplit : inp = [false, true, true] ++ (encodeCode a ++ encodeCode b) := by
    simp [inp, encodeCode]
  have p2 := drop3_run (encodeCode a ++ encodeCode b) [] [] inp []
  rw [← hsplit] at p2
  obtain ⟨t3, ht3, p3⟩ := ChildNav.takeChild_run a (encodeCode b) inp
  obtain ⟨r1, hr1, q1⟩ := BitMachineRawSequence.runs ChildNav.copyIn drop3 .scan d3start
    oc oc () () _ _ _ _ _ p1 p2
  obtain ⟨r2, hr2, q2⟩ := BitMachineRawSequence.runs l1 ChildNav.takeChild
    (BitMachineRawSequence.leftLabel .scan) ChildNav.takeStart
    (oc, ()) (oc, ()) ChildNav.takeCtl ChildNav.takeCtl _ _ _ _ _ q1 p3
  refine ⟨r2, ?_, q2⟩
  have hinp : inp.length = (encodeCode (.append a b)).length := rfl
  simp only [leftBound]
  omega

/-! ### First child of the second child of an `append` -/

def m1 := BitMachineRawSequence.program ChildNav.copyIn drop3 d3start oc ()
def m2 := BitMachineRawSequence.program m1 ChildNav.dropChild ChildNav.dropStart (oc, ())
  ChildNav.dropCtl
def m3 := BitMachineRawSequence.program m2 drop3 d3start ((oc, ()), ChildNav.dropCtl) ()
def midProgram := BitMachineRawSequence.program m3 ChildNav.takeChild ChildNav.takeStart
  (((oc, ()), ChildNav.dropCtl), ()) ChildNav.takeCtl

def midStart := ChildNav.labelOf midProgram
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      BitMachineCopy.Label.scan))))
def midCtl := ((((oc, ()), ChildNav.dropCtl), ()), ChildNav.takeCtl)

def midBound (a b c : Code) : Nat :=
  (2 * (encodeCode (.append a (.append b c))).length + 2) + 4 +
    ChildNav.dropBound a (encodeCode (.append b c)) + 4 +
    ChildNav.takeBound b (encodeCode c) + 4

theorem mid_run (a b c : Code) :
    ∃ t ≤ midBound a b c,
      ((advance midProgram)^[t])
        (⟨some midStart, midCtl, nb [] [] [] (encodeCode (.append a (.append b c))) []⟩ :
          TM2.Cfg (fun _ : ChildNav.Stack => Bool) _ _) =
        ⟨none, midCtl, nb [] [] [] (encodeCode (.append a (.append b c))) (encodeCode b)⟩ := by
  let inp := encodeCode (.append a (.append b c))
  have p1 := ChildNav.copyIn_run inp []
  have hsplit : inp = [false, true, true] ++ (encodeCode a ++ encodeCode (.append b c)) := by
    simp [inp, encodeCode]
  have p2 := drop3_run (encodeCode a ++ encodeCode (.append b c)) [] [] inp []
  rw [← hsplit] at p2
  obtain ⟨t3, ht3, p3⟩ := ChildNav.dropChild_run a (encodeCode (.append b c)) inp []
  have hsplit2 : encodeCode (.append b c) = [false, true, true] ++ (encodeCode b ++ encodeCode c) := by
    simp [encodeCode]
  have p4 := drop3_run (encodeCode b ++ encodeCode c) [] [] inp []
  rw [← hsplit2] at p4
  obtain ⟨t5, ht5, p5⟩ := ChildNav.takeChild_run b (encodeCode c) inp
  obtain ⟨r1, hr1, q1⟩ := BitMachineRawSequence.runs ChildNav.copyIn drop3 .scan d3start
    oc oc () () _ _ _ _ _ p1 p2
  obtain ⟨r2, hr2, q2⟩ := BitMachineRawSequence.runs m1 ChildNav.dropChild
    (BitMachineRawSequence.leftLabel .scan) ChildNav.dropStart
    (oc, ()) (oc, ()) ChildNav.dropCtl ChildNav.dropCtl _ _ _ _ _ q1 p3
  obtain ⟨r3, hr3, q3⟩ := BitMachineRawSequence.runs m2 drop3
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)) d3start
    ((oc, ()), ChildNav.dropCtl) ((oc, ()), ChildNav.dropCtl) () () _ _ _ _ _ q2 p4
  obtain ⟨r4, hr4, q4⟩ := BitMachineRawSequence.runs m3 ChildNav.takeChild
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel .scan))) ChildNav.takeStart
    (((oc, ()), ChildNav.dropCtl), ()) (((oc, ()), ChildNav.dropCtl), ())
    ChildNav.takeCtl ChildNav.takeCtl _ _ _ _ _ q3 p5
  refine ⟨r4, ?_, q4⟩
  have hinp : inp.length = (encodeCode (.append a (.append b c))).length := rfl
  simp only [midBound]
  omega

/-! ### The actual level-`k+1` codes -/

theorem row_succ_eq {n p s q₁ q₂ w Q : ℕ} (hQ : 0 < Q) (k : ℕ) :
    (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).1 =
      .append (.append (.ticket w) (taggedCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2))
        (copies (Q - 1) (.append (.ticket w)
          (taggedCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2))) := by
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
  rfl

theorem col_succ_eq {n p s q₁ q₂ w Q : ℕ} (hw : 0 < w) (k : ℕ) :
    (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).2 =
      .append (.ticket Q)
        (.append (graphRowsCode (V := Fin n) q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).1)
          (copies (w - 1)
            (graphRowsCode (V := Fin n) q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).1))) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  rfl

/-- `E_k` from the serialized `row_{k+1}`. -/
theorem entry_code_run {n p s q₁ q₂ w Q : ℕ} (hQ : 0 < Q) (k : ℕ) :
    let c := seedRecursiveCodes n p s q₁ q₂ w Q k
    let E : Code := .append (.ticket w) (taggedCode q₁ q₂ s c.2)
    let row := (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).1
    ∃ t ≤ leftBound E (copies (Q - 1) E),
      ((advance leftProgram)^[t])
        (⟨some leftStart, leftCtl, nb [] [] [] (encodeCode row) []⟩ :
          TM2.Cfg (fun _ : ChildNav.Stack => Bool) _ _) =
        ⟨none, leftCtl, nb [] [] [] (encodeCode row) (encodeCode E)⟩ := by
  intro c E row
  have h := row_succ_eq (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) hQ k
  have hr : row = .append E (copies (Q - 1) E) := h
  rw [hr]
  exact left_run E (copies (Q - 1) E)

/-- `G_k` from the serialized `col_{k+1}`. -/
theorem rawrow_code_run {n p s q₁ q₂ w Q : ℕ} (hw : 0 < w) (k : ℕ) :
    let c := seedRecursiveCodes n p s q₁ q₂ w Q k
    let G : Code := graphRowsCode (V := Fin n) q₁ q₂ s c.1
    let col := (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).2
    ∃ t ≤ midBound (.ticket Q) G (copies (w - 1) G),
      ((advance midProgram)^[t])
        (⟨some midStart, midCtl, nb [] [] [] (encodeCode col) []⟩ :
          TM2.Cfg (fun _ : ChildNav.Stack => Bool) _ _) =
        ⟨none, midCtl, nb [] [] [] (encodeCode col) (encodeCode G)⟩ := by
  intro c G col
  have h := col_succ_eq (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (Q := Q) hw k
  have hc : col = .append (.ticket Q) (.append G (copies (w - 1) G)) := h
  rw [hc]
  exact mid_run (.ticket Q) G (copies (w - 1) G)

end

#print axioms left_run
#print axioms mid_run
#print axioms entry_code_run
#print axioms rawrow_code_run

end Paper2.LevelNav
