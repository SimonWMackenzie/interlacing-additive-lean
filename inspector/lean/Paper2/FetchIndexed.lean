import Paper2.FetchLabelRun
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Indexed column-label fetch from the complete forward successful word.

Bank: the `FetchLabel` bank beside five retained cells: `fw` (forward
columns-first sample word), `cc` (serialized column code), `rc` (serialized
row code), `my` (unary column count), `idx` (unary requested index).
One fixed program: copy `fw` to the skipper's output cell, copy `idx` to the
counter, copy `cc` to the code cell, skip `idx` column labels, capture the
next one into `lbl`, clear the code and the residual output. Every retained
cell ends unchanged; only `lbl` changes. -/

namespace Paper2.FetchIndexed

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization
open RecursiveRequestCodeShape
open OutputSkipper (bk ctl0 Shape)
open FetchLabel (fb eb)

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

abbrev Inner := FetchLabel.Stack
abbrev Stack := Inner ⊕ Fin 5

def ext5 (a b c d e : List Bool) : Fin 5 → List Bool :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else
    if i = 3 then d else e

def FB (O code cnt lbl fw cc rc my idx : List Bool) : Stack → List Bool :=
  Sum.elim (fb (eb O) code cnt [] lbl) (ext5 fw cc rc my idx)

def fwC : Stack := .inr 0
def ccC : Stack := .inr 1
def rcC : Stack := .inr 2
def myC : Stack := .inr 3
def idxC : Stack := .inr 4
def outI : Stack := .inl (FetchLabel.skC OutputSkipper.out)
def codeI : Stack := .inl FetchLabel.codeC
def cntI : Stack := .inl FetchLabel.cntC
def scrI : Stack := .inl FetchLabel.scrC

def inner : Inner ↪ Stack := ⟨Sum.inl, fun _ _ h => Sum.inl_injective h⟩

theorem bank_inner (X Z : Inner → List Bool) (Y : Fin 5 → List Bool) :
    bank inner (Sum.elim X Y) Z = Sum.elim Z Y := by
  funext j
  cases j with
  | inl j => exact bank_at inner _ Z j
  | inr j => exact bank_outside inner _ Z (.inr j) (by rintro ⟨k, hk⟩; cases hk)

theorem inner_run {L V : Type*} (P : L → TM2.Stmt (fun _ : Inner => Bool) L V)
    (l : L) (v v' : V) (X X' : Inner → List Bool) (Y : Fin 5 → List Bool) (t : Nat)
    (h : ((advance P)^[t]) (⟨some l, v, X⟩ : TM2.Cfg (fun _ : Inner => Bool) L V) =
      ⟨none, v', X'⟩) :
    ((advance (fun l => stackStmt inner (P l)))^[t])
      (⟨some l, v, Sum.elim X Y⟩ : TM2.Cfg (fun _ : Stack => Bool) L V) =
      ⟨none, v', Sum.elim X' Y⟩ := by
  have hr := BitMachineStackRun.run inner (Sum.elim X Y) P
    (⟨some l, v, X⟩ : TM2.Cfg (fun _ : Inner => Bool) L V) t
  rw [h] at hr
  simpa only [stackCfg, bank_inner] using hr

/-! ### Copies and clears -/

def fwSlots : Fin 3 ↪ Stack := ⟨![fwC, outI, scrI], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [fwC, outI, scrI,
    FetchLabel.skC, FetchLabel.scrC, OutputSkipper.out]⟩
def idxSlots : Fin 3 ↪ Stack := ⟨![idxC, cntI, scrI], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [idxC, cntI, scrI,
    FetchLabel.cntC, FetchLabel.scrC]⟩
def ccSlots : Fin 3 ↪ Stack := ⟨![ccC, codeI, scrI], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [ccC, codeI, scrI,
    FetchLabel.codeC, FetchLabel.scrC]⟩

def clearProg (k : Stack) : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit (Option Bool) :=
  fun _ => pop k (fun _ b => b) (branch Option.isSome (goto (fun _ => ())) halt)

theorem clear_run (k : Stack) : ∀ (xs : List Bool) (S : Stack → List Bool) (v : Option Bool),
    S k = xs →
    ((advance (clearProg k))^[xs.length + 1]) (⟨some (), v, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Unit (Option Bool)) =
      ⟨none, none, Function.update S k []⟩
  | [], S, v, hS => by
      have hS' : Function.update S k [] = S := by rw [← hS]; exact Function.update_eq_self _ _
      simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, clearProg, hS, hS']
  | b :: xs, S, v, hS => by
      rw [show (b :: xs).length + 1 = (xs.length + 1) + 1 by simp, Function.iterate_add_apply]
      have e : ((advance (clearProg k))^[1]) (⟨some (), v, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Unit (Option Bool)) =
          ⟨some (), some b, Function.update S k xs⟩ := by
        simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, clearProg, hS]
      rw [e, clear_run k xs (Function.update S k xs) (some b) (by simp)]
      simp

/-! ### Bank lemmas -/

section BankLemmas
variable (O code cnt lbl fw cc rc my idx x : List Bool)

@[simp] theorem FB_fw : FB O code cnt lbl fw cc rc my idx fwC = fw := rfl
@[simp] theorem FB_cc : FB O code cnt lbl fw cc rc my idx ccC = cc := rfl
@[simp] theorem FB_idx : FB O code cnt lbl fw cc rc my idx idxC = idx := rfl
@[simp] theorem FB_out : FB O code cnt lbl fw cc rc my idx outI = O := rfl
@[simp] theorem FB_code : FB O code cnt lbl fw cc rc my idx codeI = code := rfl
@[simp] theorem FB_cnt : FB O code cnt lbl fw cc rc my idx cntI = cnt := rfl
@[simp] theorem FB_scr : FB O code cnt lbl fw cc rc my idx scrI = [] := rfl

theorem FB_up_out : Function.update (FB O code cnt lbl fw cc rc my idx) outI x =
    FB x code cnt lbl fw cc rc my idx := by
  funext j; rcases j with (((j | j) | j) | j) | j <;> first | (fin_cases j <;> rfl) | rfl
theorem FB_up_code : Function.update (FB O code cnt lbl fw cc rc my idx) codeI x =
    FB O x cnt lbl fw cc rc my idx := by
  funext j; rcases j with (((j | j) | j) | j) | j <;> first | (fin_cases j <;> rfl) | rfl
theorem FB_up_cnt : Function.update (FB O code cnt lbl fw cc rc my idx) cntI x =
    FB O code x lbl fw cc rc my idx := by
  funext j; rcases j with (((j | j) | j) | j) | j <;> first | (fin_cases j <;> rfl) | rfl

end BankLemmas

/-! ### The column fetch program -/

def copyFW := MatrixStage4ScalarPreparationOps.copyProgram fwSlots
def copyIdx := MatrixStage4ScalarPreparationOps.copyProgram idxSlots
def copyCC := MatrixStage4ScalarPreparationOps.copyProgram ccSlots
def skipP := fun l => stackStmt inner (FetchLabel.program false l)
def captureP := fun l => stackStmt inner (FetchLabel.program true l)
def clearCode := clearProg codeI
def clearOut := clearProg outI

def q1 := BitMachineRawSequence.program copyFW copyIdx .scan (none : Option Bool)
  (none : Option Bool)
def q2 := BitMachineRawSequence.program q1 copyCC .scan ((none : Option Bool), (none : Option Bool))
  (none : Option Bool)
def q3 := BitMachineRawSequence.program q2 skipP .cnt
  (((none : Option Bool), (none : Option Bool)), (none : Option Bool)) FetchLabel.base
def q4 := BitMachineRawSequence.program q3 captureP (.copy .scan)
  ((((none : Option Bool), (none : Option Bool)), (none : Option Bool)), FetchLabel.base)
  FetchLabel.base
def q5 := BitMachineRawSequence.program q4 clearCode ()
  (((((none : Option Bool), (none : Option Bool)), (none : Option Bool)), FetchLabel.base),
    FetchLabel.base) (none : Option Bool)
def colProgram := BitMachineRawSequence.program q5 clearOut ()
  ((((((none : Option Bool), (none : Option Bool)), (none : Option Bool)), FetchLabel.base),
    FetchLabel.base), (none : Option Bool)) (none : Option Bool)

def c5 := ((((((none : Option Bool), (none : Option Bool)), (none : Option Bool)),
  FetchLabel.base), FetchLabel.base), (none : Option Bool))
def colStart := BitMachineRawSequence.leftLabel (LB := Unit)
  (BitMachineRawSequence.leftLabel (LB := Unit)
    (BitMachineRawSequence.leftLabel (LB := FetchLabel.Label)
      (BitMachineRawSequence.leftLabel (LB := FetchLabel.Label)
        (BitMachineRawSequence.leftLabel (LB := BitMachineCopy.Label)
          (BitMachineRawSequence.leftLabel (LB := BitMachineCopy.Label)
            BitMachineCopy.Label.scan)))))
def colControl := (c5, (none : Option Bool))

def colBound (col : Code) (cs : List (List Bool)) (y : Nat) (O : List Bool) : Nat :=
  (2 * (cs.flatten ++ O).length + 2) + (2 * y + 2) + (2 * codeSize col + 2) +
    FetchLabel.loopBound col (cs.take y) + FetchLabel.iterBound col (cs.getD y []) +
    (codeSize col + 1) + ((cs.drop (y + 1)).flatten ++ O).length + 1 + 6

theorem col_fetch (col : Code) (hcol : Shape col) (cs : List (List Bool))
    (hcs : ∀ c ∈ cs, Produces (meaning col) c) (O : List Bool) (y : Nat) (hy : y < cs.length)
    (cc rc my : List Bool) (hcc : cc = encodeCode col) :
    ∃ t ≤ colBound col cs y O, ∃ v,
      ((advance colProgram)^[t])
        (⟨some colStart, colControl,
          FB [] [] [] [] (cs.flatten ++ O) cc rc my (List.replicate y true)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, v, FB [] [] [] (cs.getD y []) (cs.flatten ++ O) cc rc my
          (List.replicate y true)⟩ := by
  let fw := cs.flatten ++ O
  let idx := List.replicate y true
  let w := cs.getD y []
  let O2 := (cs.drop (y + 1)).flatten ++ O
  have hsplit : fw = (cs.take y).flatten ++ (w ++ O2) := by
    have h1 : cs = cs.take y ++ w :: cs.drop (y + 1) := by
      have hd := List.drop_eq_getElem_cons hy
      have hw' : w = cs[y] := by
        simp only [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy, Option.getD_some]
      rw [hw', ← hd, List.take_append_drop]
    simp only [fw, O2]
    conv_lhs => rw [h1]
    simp [List.flatten_append, List.append_assoc]
  have hw : Produces (meaning col) w := by
    apply hcs
    simp only [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy, Option.getD_some]
    exact List.getElem_mem hy
  -- phase 1: fw → out
  have p1 := MatrixStage4ScalarPreparationOps.copy_run fwSlots
    (FB [] [] [] [] fw cc rc my idx) rfl
  have p1' : ((advance copyFW)^[2 * fw.length + 2])
      (⟨some .scan, none, FB [] [] [] [] fw cc rc my idx⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, FB fw [] [] [] fw cc rc my idx⟩ := by
    have e0 : FB [] [] [] [] fw cc rc my idx (fwSlots 0) = fw := rfl
    have e1 : FB [] [] [] [] fw cc rc my idx (fwSlots 1) = [] := rfl
    rw [e0, e1, List.append_nil] at p1
    rw [show fwSlots 1 = outI from rfl, FB_up_out] at p1
    exact p1
  -- phase 2: idx → cnt
  have p2 := MatrixStage4ScalarPreparationOps.copy_run idxSlots
    (FB fw [] [] [] fw cc rc my idx) rfl
  have p2' : ((advance copyIdx)^[2 * idx.length + 2])
      (⟨some .scan, none, FB fw [] [] [] fw cc rc my idx⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, FB fw [] idx [] fw cc rc my idx⟩ := by
    have e0 : FB fw [] [] [] fw cc rc my idx (idxSlots 0) = idx := rfl
    have e1 : FB fw [] [] [] fw cc rc my idx (idxSlots 1) = [] := rfl
    rw [e0, e1, List.append_nil] at p2
    rw [show idxSlots 1 = cntI from rfl, FB_up_cnt] at p2
    exact p2
  -- phase 3: cc → code
  have p3 := MatrixStage4ScalarPreparationOps.copy_run ccSlots
    (FB fw [] idx [] fw cc rc my idx) rfl
  have p3' : ((advance copyCC)^[2 * cc.length + 2])
      (⟨some .scan, none, FB fw [] idx [] fw cc rc my idx⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, FB fw cc idx [] fw cc rc my idx⟩ := by
    have e0 : FB fw [] idx [] fw cc rc my idx (ccSlots 0) = cc := rfl
    have e1 : FB fw [] idx [] fw cc rc my idx (ccSlots 1) = [] := rfl
    rw [e0, e1, List.append_nil] at p3
    rw [show ccSlots 1 = codeI from rfl, FB_up_code] at p3
    exact p3
  -- phase 4: skip y labels
  have htake : (cs.take y).length = y := by simp; omega
  obtain ⟨t4, ht4, v4, h4⟩ := FetchLabel.skipN_run col hcol cc hcc []
    (cs.take y) (fun c hc => hcs c (List.mem_of_mem_take hc)) (w ++ O2) FetchLabel.base
  rw [htake] at h4
  have p4 := inner_run (FetchLabel.program false) FetchLabel.Label.cnt FetchLabel.base v4
    _ _ (ext5 fw cc rc my idx) t4 h4
  -- phase 5: capture
  obtain ⟨t5, ht5, v5, h5⟩ := FetchLabel.capture_run col hcol w hw O2 cc [] hcc
  have p5 := inner_run (FetchLabel.program true) (FetchLabel.Label.copy .scan)
    FetchLabel.base v5 _ _ (ext5 fw cc rc my idx) t5 h5
  -- phase 6, 7: clears
  have p6 := clear_run codeI cc (FB O2 cc [] w fw cc rc my idx) none rfl
  rw [FB_up_code] at p6
  have p7 := clear_run outI O2 (FB O2 [] [] w fw cc rc my idx) none rfl
  rw [FB_up_out] at p7
  -- sequencing
  obtain ⟨s1, hs1, r1⟩ := BitMachineRawSequence.runs copyFW copyIdx .scan .scan
    none none none none _ _ _ _ _ p1' p2'
  obtain ⟨s2, hs2, r2⟩ := BitMachineRawSequence.runs q1 copyCC
    (BitMachineRawSequence.leftLabel .scan) .scan
    (none, none) (none, none) none none _ _ _ _ _ r1 p3'
  have hfb4 : FB fw cc idx [] fw cc rc my idx =
      Sum.elim (fb (eb ((cs.take y).flatten ++ (w ++ O2))) cc (List.replicate y true) [] [])
        (ext5 fw cc rc my idx) := by
    rw [← hsplit]; rfl
  rw [hfb4] at r2
  obtain ⟨s3, hs3, r3⟩ := BitMachineRawSequence.runs q2 skipP
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)) .cnt
    ((none, none), none) ((none, none), none) FetchLabel.base v4 _ _ _ _ _ r2 p4
  obtain ⟨s4, hs4, r4⟩ := BitMachineRawSequence.runs q3 captureP
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel .scan))) (.copy .scan)
    (((none, none), none), FetchLabel.base) (((none, none), none), v4)
    FetchLabel.base v5 _ _ _ _ _ r3 p5
  have hfb6 : Sum.elim (fb (eb O2) cc [] [] w) (ext5 fw cc rc my idx) =
      FB O2 cc [] w fw cc rc my idx := rfl
  rw [hfb6] at r4
  obtain ⟨s5, hs5, r5⟩ := BitMachineRawSequence.runs q4 clearCode
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)))) ()
    ((((none, none), none), FetchLabel.base), FetchLabel.base)
    ((((none, none), none), FetchLabel.base), v5)
    none none _ _ _ _ _ r4 p6
  obtain ⟨s6, hs6, r6⟩ := BitMachineRawSequence.runs q5 clearOut
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel .scan))))) ()
    c5 c5 none none _ _ _ _ _ r5 p7
  refine ⟨s6, ?_, _, r6⟩
  have hcc' : cc.length = codeSize col := by rw [hcc, encodeCode_length]
  have hidx : idx.length = y := by simp [idx]
  have ht5' : t5 ≤ FetchLabel.iterBound col (cs.getD y []) := ht5
  have hfw : fw.length = (cs.flatten ++ O).length := rfl
  have hO2 : O2.length = ((cs.drop (y + 1)).flatten ++ O).length := rfl
  have hs1' : s1 ≤ 2 * fw.length + 2 + (2 * idx.length + 2) + 1 := hs1
  have hs2' : s2 ≤ s1 + (2 * cc.length + 2) + 1 := hs2
  have hs3' : s3 ≤ s2 + t4 + 1 := hs3
  have hs4' : s4 ≤ s3 + t5 + 1 := hs4
  have hs5' : s5 ≤ s4 + (cc.length + 1) + 1 := hs5
  have hs6' : s6 ≤ s5 + (O2.length + 1) + 1 := hs6
  simp only [colBound]
  omega

#print axioms col_fetch

/-! ### The row fetch program: skip all `mY` column labels, then `idx` row
labels, capture the next row label. -/

def mySlots : Fin 3 ↪ Stack := ⟨![myC, cntI, scrI], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [myC, cntI, scrI,
    FetchLabel.cntC, FetchLabel.scrC]⟩
def rcSlots : Fin 3 ↪ Stack := ⟨![rcC, codeI, scrI], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [rcC, codeI, scrI,
    FetchLabel.codeC, FetchLabel.scrC]⟩

def copyMY := MatrixStage4ScalarPreparationOps.copyProgram mySlots
def copyRC := MatrixStage4ScalarPreparationOps.copyProgram rcSlots

abbrev oc := (none : Option Bool)

def r1p := BitMachineRawSequence.program copyFW copyMY .scan oc oc
def r2p := BitMachineRawSequence.program r1p copyCC .scan (oc, oc) oc
def r3p := BitMachineRawSequence.program r2p skipP .cnt ((oc, oc), oc) FetchLabel.base
def r4p := BitMachineRawSequence.program r3p clearCode () (((oc, oc), oc), FetchLabel.base) oc
def r5p := BitMachineRawSequence.program r4p copyIdx .scan
  ((((oc, oc), oc), FetchLabel.base), oc) oc
def r6p := BitMachineRawSequence.program r5p copyRC .scan
  (((((oc, oc), oc), FetchLabel.base), oc), oc) oc
def r7p := BitMachineRawSequence.program r6p skipP .cnt
  ((((((oc, oc), oc), FetchLabel.base), oc), oc), oc) FetchLabel.base
def r8p := BitMachineRawSequence.program r7p captureP (.copy .scan)
  (((((((oc, oc), oc), FetchLabel.base), oc), oc), oc), FetchLabel.base) FetchLabel.base
def r9p := BitMachineRawSequence.program r8p clearCode ()
  ((((((((oc, oc), oc), FetchLabel.base), oc), oc), oc), FetchLabel.base), FetchLabel.base) oc
def rowProgram := BitMachineRawSequence.program r9p clearOut ()
  (((((((((oc, oc), oc), FetchLabel.base), oc), oc), oc), FetchLabel.base), FetchLabel.base),
    oc) oc

def d9 := (((((((((oc, oc), oc), FetchLabel.base), oc), oc), oc), FetchLabel.base),
  FetchLabel.base), oc)
def labelOf {L σ K : Type*} (_P : L → TM2.Stmt (fun _ : K => Bool) L σ) (l : L) : L := l

def rowStart := labelOf rowProgram
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
            BitMachineCopy.Label.scan))))))))))
def rowControl := (d9, oc)

def rowBound (col row : Code) (cs rs : List (List Bool)) (x : Nat) (O : List Bool) : Nat :=
  (2 * (cs.flatten ++ rs.flatten ++ O).length + 2) + (2 * cs.length + 2) +
    (2 * codeSize col + 2) + FetchLabel.loopBound col cs + (codeSize col + 1) +
    (2 * x + 2) + (2 * codeSize row + 2) + FetchLabel.loopBound row (rs.take x) +
    FetchLabel.iterBound row (rs.getD x []) + (codeSize row + 1) +
    ((rs.drop (x + 1)).flatten ++ O).length + 1 + 10

theorem row_fetch (col row : Code) (hcol : Shape col) (hrow : Shape row)
    (cs rs : List (List Bool))
    (hcs : ∀ c ∈ cs, Produces (meaning col) c) (hrs : ∀ r ∈ rs, Produces (meaning row) r)
    (O : List Bool) (x : Nat) (hx : x < rs.length)
    (cc rc : List Bool) (hcc : cc = encodeCode col) (hrc : rc = encodeCode row) :
    ∃ t ≤ rowBound col row cs rs x O, ∃ v,
      ((advance rowProgram)^[t])
        (⟨some rowStart, rowControl,
          FB [] [] [] [] (cs.flatten ++ rs.flatten ++ O) cc rc (List.replicate cs.length true)
            (List.replicate x true)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, v, FB [] [] [] (rs.getD x []) (cs.flatten ++ rs.flatten ++ O) cc rc
          (List.replicate cs.length true) (List.replicate x true)⟩ := by
  let fw := cs.flatten ++ rs.flatten ++ O
  let my := List.replicate cs.length true
  let idx := List.replicate x true
  let w := rs.getD x []
  let O2 := (rs.drop (x + 1)).flatten ++ O
  let O1 := rs.flatten ++ O
  have hsplit1 : fw = cs.flatten ++ O1 := by simp [fw, O1, List.append_assoc]
  have hsplit2 : O1 = (rs.take x).flatten ++ (w ++ O2) := by
    have h1 : rs = rs.take x ++ w :: rs.drop (x + 1) := by
      have hd := List.drop_eq_getElem_cons hx
      have hw' : w = rs[x] := by
        simp only [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx, Option.getD_some]
      rw [hw', ← hd, List.take_append_drop]
    simp only [O1, O2]
    conv_lhs => rw [h1]
    simp [List.flatten_append, List.append_assoc]
  have hw : Produces (meaning row) w := by
    apply hrs
    simp only [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx, Option.getD_some]
    exact List.getElem_mem hx
  -- phase 1: fw → out
  have p1 := MatrixStage4ScalarPreparationOps.copy_run fwSlots
    (FB [] [] [] [] fw cc rc my idx) rfl
  have p1' : ((advance copyFW)^[2 * fw.length + 2])
      (⟨some .scan, none, FB [] [] [] [] fw cc rc my idx⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, FB fw [] [] [] fw cc rc my idx⟩ := by
    have e0 : FB [] [] [] [] fw cc rc my idx (fwSlots 0) = fw := rfl
    have e1 : FB [] [] [] [] fw cc rc my idx (fwSlots 1) = [] := rfl
    rw [e0, e1, List.append_nil] at p1
    rw [show fwSlots 1 = outI from rfl, FB_up_out] at p1
    exact p1
  -- phase 2: my → cnt
  have p2 := MatrixStage4ScalarPreparationOps.copy_run mySlots
    (FB fw [] [] [] fw cc rc my idx) rfl
  have p2' : ((advance copyMY)^[2 * my.length + 2])
      (⟨some .scan, none, FB fw [] [] [] fw cc rc my idx⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, FB fw [] my [] fw cc rc my idx⟩ := by
    have e0 : FB fw [] [] [] fw cc rc my idx (mySlots 0) = my := rfl
    have e1 : FB fw [] [] [] fw cc rc my idx (mySlots 1) = [] := rfl
    rw [e0, e1, List.append_nil] at p2
    rw [show mySlots 1 = cntI from rfl, FB_up_cnt] at p2
    exact p2
  -- phase 3: cc → code
  have p3 := MatrixStage4ScalarPreparationOps.copy_run ccSlots
    (FB fw [] my [] fw cc rc my idx) rfl
  have p3' : ((advance copyCC)^[2 * cc.length + 2])
      (⟨some .scan, none, FB fw [] my [] fw cc rc my idx⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, FB fw cc my [] fw cc rc my idx⟩ := by
    have e0 : FB fw [] my [] fw cc rc my idx (ccSlots 0) = cc := rfl
    have e1 : FB fw [] my [] fw cc rc my idx (ccSlots 1) = [] := rfl
    rw [e0, e1, List.append_nil] at p3
    rw [show ccSlots 1 = codeI from rfl, FB_up_code] at p3
    exact p3
  -- phase 4: skip all column labels
  obtain ⟨t4, ht4, v4, h4⟩ := FetchLabel.skipN_run col hcol cc hcc []
    cs hcs O1 FetchLabel.base
  have p4 := inner_run (FetchLabel.program false) FetchLabel.Label.cnt FetchLabel.base v4
    _ _ (ext5 fw cc rc my idx) t4 h4
  -- phase 5: clear code
  have p5 := clear_run codeI cc (FB O1 cc [] [] fw cc rc my idx) none rfl
  rw [FB_up_code] at p5
  -- phase 6: idx → cnt
  have p6 := MatrixStage4ScalarPreparationOps.copy_run idxSlots
    (FB O1 [] [] [] fw cc rc my idx) rfl
  have p6' : ((advance copyIdx)^[2 * idx.length + 2])
      (⟨some .scan, none, FB O1 [] [] [] fw cc rc my idx⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, FB O1 [] idx [] fw cc rc my idx⟩ := by
    have e0 : FB O1 [] [] [] fw cc rc my idx (idxSlots 0) = idx := rfl
    have e1 : FB O1 [] [] [] fw cc rc my idx (idxSlots 1) = [] := rfl
    rw [e0, e1, List.append_nil] at p6
    rw [show idxSlots 1 = cntI from rfl, FB_up_cnt] at p6
    exact p6
  -- phase 7: rc → code
  have p7 := MatrixStage4ScalarPreparationOps.copy_run rcSlots
    (FB O1 [] idx [] fw cc rc my idx) rfl
  have p7' : ((advance copyRC)^[2 * rc.length + 2])
      (⟨some .scan, none, FB O1 [] idx [] fw cc rc my idx⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, FB O1 rc idx [] fw cc rc my idx⟩ := by
    have e0 : FB O1 [] idx [] fw cc rc my idx (rcSlots 0) = rc := rfl
    have e1 : FB O1 [] idx [] fw cc rc my idx (rcSlots 1) = [] := rfl
    rw [e0, e1, List.append_nil] at p7
    rw [show rcSlots 1 = codeI from rfl, FB_up_code] at p7
    exact p7
  -- phase 8: skip x row labels
  have htake : (rs.take x).length = x := by simp; omega
  obtain ⟨t8, ht8, v8, h8⟩ := FetchLabel.skipN_run row hrow rc hrc []
    (rs.take x) (fun r hr => hrs r (List.mem_of_mem_take hr)) (w ++ O2) FetchLabel.base
  rw [htake] at h8
  have p8 := inner_run (FetchLabel.program false) FetchLabel.Label.cnt FetchLabel.base v8
    _ _ (ext5 fw cc rc my idx) t8 h8
  -- phase 9: capture
  obtain ⟨t9, ht9, v9, h9⟩ := FetchLabel.capture_run row hrow w hw O2 rc [] hrc
  have p9 := inner_run (FetchLabel.program true) (FetchLabel.Label.copy .scan)
    FetchLabel.base v9 _ _ (ext5 fw cc rc my idx) t9 h9
  -- phases 10, 11: clears
  have p10 := clear_run codeI rc (FB O2 rc [] w fw cc rc my idx) none rfl
  rw [FB_up_code] at p10
  have p11 := clear_run outI O2 (FB O2 [] [] w fw cc rc my idx) none rfl
  rw [FB_up_out] at p11
  -- sequencing
  obtain ⟨s1, hs1, e1⟩ := BitMachineRawSequence.runs copyFW copyMY .scan .scan
    none none none none _ _ _ _ _ p1' p2'
  obtain ⟨s2, hs2, e2⟩ := BitMachineRawSequence.runs r1p copyCC
    (BitMachineRawSequence.leftLabel .scan) .scan
    (none, none) (none, none) none none _ _ _ _ _ e1 p3'
  have hfb4 : FB fw cc my [] fw cc rc my idx =
      Sum.elim (fb (eb (cs.flatten ++ O1)) cc (List.replicate cs.length true) [] [])
        (ext5 fw cc rc my idx) := by
    rw [← hsplit1]; rfl
  rw [hfb4] at e2
  obtain ⟨s3, hs3, e3⟩ := BitMachineRawSequence.runs r2p skipP
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)) .cnt
    ((none, none), none) ((none, none), none) FetchLabel.base v4 _ _ _ _ _ e2 p4
  have hfb5 : Sum.elim (fb (eb O1) cc [] [] []) (ext5 fw cc rc my idx) =
      FB O1 cc [] [] fw cc rc my idx := rfl
  rw [hfb5] at e3
  obtain ⟨s4, hs4, e4⟩ := BitMachineRawSequence.runs r3p clearCode
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel .scan))) ()
    (((none, none), none), FetchLabel.base) (((none, none), none), v4)
    none none _ _ _ _ _ e3 p5
  obtain ⟨s5, hs5, e5⟩ := BitMachineRawSequence.runs r4p copyIdx
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)))) .scan
    ((((none, none), none), FetchLabel.base), none)
    ((((none, none), none), FetchLabel.base), none)
    none none _ _ _ _ _ e4 p6'
  obtain ⟨s6, hs6, e6⟩ := BitMachineRawSequence.runs r5p copyRC
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel .scan))))) .scan
    (((((none, none), none), FetchLabel.base), none), none)
    (((((none, none), none), FetchLabel.base), none), none)
    none none _ _ _ _ _ e5 p7'
  have hfb8 : FB O1 rc idx [] fw cc rc my idx =
      Sum.elim (fb (eb ((rs.take x).flatten ++ (w ++ O2))) rc (List.replicate x true) [] [])
        (ext5 fw cc rc my idx) := by
    rw [← hsplit2]; rfl
  rw [hfb8] at e6
  obtain ⟨s7, hs7, e7⟩ := BitMachineRawSequence.runs r6p skipP
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)))))) .cnt
    ((((((none, none), none), FetchLabel.base), none), none), none)
    ((((((none, none), none), FetchLabel.base), none), none), none)
    FetchLabel.base v8 _ _ _ _ _ e6 p8
  obtain ⟨s8, hs8, e8⟩ := BitMachineRawSequence.runs r7p captureP
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel .scan))))))) (.copy .scan)
    (((((((none, none), none), FetchLabel.base), none), none), none), FetchLabel.base)
    (((((((none, none), none), FetchLabel.base), none), none), none), v8)
    FetchLabel.base v9 _ _ _ _ _ e7 p9
  have hfb10 : Sum.elim (fb (eb O2) rc [] [] w) (ext5 fw cc rc my idx) =
      FB O2 rc [] w fw cc rc my idx := rfl
  rw [hfb10] at e8
  obtain ⟨s9, hs9, e9⟩ := BitMachineRawSequence.runs r8p clearCode
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)))))))) ()
    ((((((((none, none), none), FetchLabel.base), none), none), none), FetchLabel.base),
      FetchLabel.base)
    ((((((((none, none), none), FetchLabel.base), none), none), none), FetchLabel.base), v9)
    none none _ _ _ _ _ e8 p10
  obtain ⟨s10, hs10, e10⟩ := BitMachineRawSequence.runs r9p clearOut
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel .scan))))))))) ()
    d9 d9 none none _ _ _ _ _ e9 p11
  refine ⟨s10, ?_, _, e10⟩
  have hcc' : cc.length = codeSize col := by rw [hcc, encodeCode_length]
  have hrc' : rc.length = codeSize row := by rw [hrc, encodeCode_length]
  have hidx : idx.length = x := by simp [idx]
  have hmy : my.length = cs.length := by simp [my]
  have ht9' : t9 ≤ FetchLabel.iterBound row (rs.getD x []) := ht9
  have hfw : fw.length = (cs.flatten ++ rs.flatten ++ O).length := rfl
  have hO2 : O2.length = ((rs.drop (x + 1)).flatten ++ O).length := rfl
  have hs1' : s1 ≤ 2 * fw.length + 2 + (2 * my.length + 2) + 1 := hs1
  have hs2' : s2 ≤ s1 + (2 * cc.length + 2) + 1 := hs2
  have hs3' : s3 ≤ s2 + t4 + 1 := hs3
  have hs4' : s4 ≤ s3 + (cc.length + 1) + 1 := hs4
  have hs5' : s5 ≤ s4 + (2 * idx.length + 2) + 1 := hs5
  have hs6' : s6 ≤ s5 + (2 * rc.length + 2) + 1 := hs6
  have hs7' : s7 ≤ s6 + t8 + 1 := hs7
  have hs8' : s8 ≤ s7 + t9 + 1 := hs8
  have hs9' : s9 ≤ s8 + (rc.length + 1) + 1 := hs9
  have hs10' : s10 ≤ s9 + (O2.length + 1) + 1 := hs10
  simp only [rowBound]
  omega

#print axioms row_fetch

#print axioms clear_run

end Paper2.FetchIndexed
