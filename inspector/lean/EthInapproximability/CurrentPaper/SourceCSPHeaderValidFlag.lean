import EthInapproximability.CurrentPaper.SourceCSPHeaderStatus

/-!
# Physical all-input fixed-header validity flag

The four-field parser and two fixed `a,q` word comparisons leave three
literal Boolean statuses on two stacks. A finite instruction chain consumes
those statuses and writes their conjunction. Malformed input still halts.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPHeaderValidFlag

open Turing BitMachineEncoding

abbrev Stack := SourceCSPHeaderCheck.Stack
abbrev ParseLabel (a q : Nat) := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label (SourceCSPRowController.Label 4 0)
    (SourceFixedBinaryCheck.Label a.bits))
  (SourceFixedBinaryCheck.Label q.bits)
abbrev ParseControl := (SourceCSPRowController.Control × Option Bool) × Option Bool
abbrev Control := Option Bool × Option Bool × Option Bool

def parserSlot : Stack := .inl (.inr 2)
def flagSlot : Stack := .inr 0

def parserGood (input : List Bool) : Bool :=
  (SourceCSPRowController.readQueriesFrom (q := 4) 0 input
    (fun _ => [])).isSome

theorem parser_result (input : List Bool) :
    SourceCSPRowController.rowResult 4 0 input = [parserGood input] := by
  unfold SourceCSPRowController.rowResult parserGood
  cases h : SourceCSPRowController.readQueriesFrom (q := 4) 0 input
      (fun _ => []) with
  | none => simp
  | some p => simp [SourceCSPRowMachine.result]

def collectProgram (_ : Unit) : TM2.Stmt (fun _ : Stack => Bool) Unit Control :=
  .pop parserSlot (fun _ b => (b, none, none))
    (.pop flagSlot (fun v b => (v.1, b, none))
      (.pop flagSlot (fun v b => (v.1, v.2.1, b))
        (.push flagSlot (fun v =>
          v.1 == some true && v.2.1 == some true && v.2.2 == some true)
          .halt)))

theorem collect_step (before : Stack → List Bool) (bp bq ba : Bool)
    (hp : before parserSlot = [bp])
    (hq : before flagSlot = [bq, ba]) :
    let c := advance collectProgram
      (⟨some (), (none, none, none), before⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Unit Control)
    c.l = none ∧
      c.stk flagSlot = [bp && bq && ba] ∧
      c.stk parserSlot = [] := by
  change before (.inl (.inr 2)) = [bp] at hp
  change before (.inr 0) = [bq, ba] at hq
  simp [advance, TM2.step, TM2.stepAux, collectProgram,
    parserSlot, flagSlot, hp, hq, Bool.and_assoc]

def program (a q : Nat) :=
  BitMachineRawSequence.program
    (SourceCSPHeaderCheck.fixedHeaderProgram a q) collectProgram ()
    (((none, none), none), none) (none, none, none)

/-- Every raw bitstream reaches an explicit header-validity bit after the
physical parser, two fixed comparators, and one finite status collection
transition. This is only a header gate; `m`, vertex cap, rows, and EOF remain
separate checks. -/
theorem all_input (a q : Nat) (input : List Bool) :
    ∃ t S v wa wq,
      t ≤ 4 * (2 * input.length + 4) + 3 +
        (a.bits.length + 1) + (q.bits.length + 1) + 4 ∧
      ((advance (program a q))^[t])
        (⟨some (.inl (.inl (.inl (.start 0)))),
          ((((none, none), none), none), (none, none, none)),
          SourceCSPHeaderCheck.parserInitial input⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label (ParseLabel a q) Unit)
            (ParseControl × Control)) =
        ⟨none, ((((none, none), none), none), v), S⟩ ∧
      S flagSlot =
        [parserGood input && decide (wq = q.bits) && decide (wa = a.bits)] := by
  obtain ⟨tp, Sp, vp, wa, wq, htp, hrp, hp, hc⟩ :=
    SourceCSPHeaderStatus.fixed_header_total_status a q input
  have hp' : Sp parserSlot = [parserGood input] := by
    exact hp.trans (parser_result input)
  let bq := decide (wq = q.bits)
  let ba := decide (wa = a.bits)
  have hc' : Sp flagSlot = [bq, ba] := hc
  let c : TM2.Cfg (fun _ : Stack => Bool) Unit Control :=
    advance collectProgram
      (⟨some (), (none, none, none), Sp⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Unit Control)
  obtain ⟨hhalt, hflag, _⟩ :=
    collect_step Sp (parserGood input) bq ba hp' hc'
  have hrunC : ((advance collectProgram)^[1])
      (⟨some (), (none, none, none), Sp⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Unit Control) =
      ⟨none, c.var, c.stk⟩ := by
    change c = ⟨none, c.var, c.stk⟩
    change c.l = none at hhalt
    cases hc : c with
    | mk l v S =>
        have hl : l = none := by simpa only [hc] using hhalt
        cases l <;> simp_all
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourceCSPHeaderCheck.fixedHeaderProgram a q) collectProgram
    (.inl (.inl (.start 0)) : ParseLabel a q) ()
    ((((none, none), none), none) : ParseControl)
    ((((none, none), none), vp) : ParseControl)
    ((none, none, none) : Control) c.var
    (SourceCSPHeaderCheck.parserInitial input) Sp c.stk
    tp 1 hrp hrunC
  refine ⟨t, c.stk, c.var, wa, wq, ?_, ?_, ?_⟩
  · omega
  · simpa only [program] using hr
  · simpa only [c, bq, ba] using hflag

end EthInapproximability.CurrentPaper.SourceCSPHeaderValidFlag
