import CurrentAdditive.CylinderEqualMachine
import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! A fixed ordinary machine compares any two physically parsed bitwords.
The final output is only the equality bit, with no serialization of consumed
input fields or comparator scratch stacks. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace CurrentAdditive.WordEqualityOrdinary
open Turing EthInapproximability.CurrentPaper BitMachineEncoding

abbrev Stack := BitMachineBankCodec.Stack 2
abbrev ParserLabel := BitMachineBankCodec.ParserLabel 2
abbrev Label := BitMachineRawSequence.Label ParserLabel CylinderEqualMachine.Label
abbrev Control := BitMachineRawSequence.Control (Option Bool) CylinderEqualMachine.Control

def input (a b : List Bool) : List Bool := BitMachineBankCodec.encode ![a,b]
def inputCell : Stack := .inr 0
def outputCell : Stack := .inr 2

def slots : Fin 3 ↪ Stack where
  toFun := ![.inl 0, .inl 1, .inr 2]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def compareProgram (l : CylinderEqualMachine.Label) :=
  BitMachineStackEmbedding.stmt slots id id id none (CylinderEqualMachine.program l)
def compareStart := CylinderEqualMachine.Label.scan
def compareControl : CylinderEqualMachine.Control := (true, none, none)

def program := BitMachineRawSequence.program (BitMachineBankCodec.parser 2)
  compareProgram compareStart (none : Option Bool) compareControl
def start : Label := BitMachineRawSequence.leftLabel (.scan 0)
def control : Control := (none, compareControl)
def machine : BitMachine.Machine := ofFinite inputCell outputCell start control program

def parsed (a b : List Bool) : Stack → List Bool :=
  (BitMachineBankCodec.parserCfg (K := 2) none (some true) ![a,b] [] [] []).stk

theorem parse_run (a b : List Bool) :
    ∃ t ≤ 5 * ((input a b).length + 1),
      ((advance (BitMachineBankCodec.parser 2))^[t])
        (rawInit inputCell (.scan 0 : ParserLabel) (none : Option Bool) (input a b)) =
      ⟨none, some true, parsed a b⟩ := by
  obtain ⟨t, ht, hr⟩ := BitMachineBankCodec.parser_correct 2 (input a b) []
  rw [input, BitMachineBankCodec.decode_encode] at hr
  have hi : rawInit inputCell (.scan 0 : ParserLabel) (none : Option Bool) (input a b) =
      BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => []) (input a b) [] [] := by
    unfold rawInit BitMachineBankCodec.parserCfg
    congr 1
    funext k
    cases k with
    | inl k => simp [rawInit, inputCell, BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]
    | inr k => fin_cases k <;>
        simp [rawInit, inputCell, BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]
  refine ⟨t, ht, ?_⟩
  rw [hi]
  exact hr

theorem compare_initial (a b : List Bool) :
    BitMachineStackEmbedding.cfg slots (parsed a b) id id none
      (CylinderEqualMachine.cfg (some .scan) compareControl a b []) =
      (⟨some compareStart, compareControl, parsed a b⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CylinderEqualMachine.Label CylinderEqualMachine.Control) := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;>
    simp [CylinderEqualMachine.cfg, CylinderEqualMachine.bank, slots, parsed,
      BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]

/-- Both actual parser and actual comparator executions occur on the same
five stacks. No prepared fields or component run is supplied to the caller. -/
theorem actual_run (a b : List Bool) :
    ∃ t ≤ 5 * ((input a b).length + 1) + min a.length b.length + 2,
      (((advance program)^[t]) (rawInit inputCell start control (input a b))).l = none ∧
      (((advance program)^[t]) (rawInit inputCell start control (input a b))).stk outputCell =
        [decide (a = b)] := by
  obtain ⟨p, hp, hparse⟩ := parse_run a b
  obtain ⟨c, hc, hhalt, hout⟩ := CylinderEqualMachine.compare_run true a b []
  let final := CylinderEqualMachine.run c
    (CylinderEqualMachine.cfg (some .scan) compareControl a b [])
  have hfl : final.l = none := hhalt
  have hfo : final.stk 2 = [decide (a = b)] := by simpa using hout
  obtain ⟨u, hu, hcompare⟩ := BitMachineStackEmbedding.outputs slots (parsed a b)
    id id id (fun _ => rfl) none CylinderEqualMachine.program compareProgram
    (fun _ => rfl) (CylinderEqualMachine.cfg (some .scan) compareControl a b []) c hhalt
  rw [compare_initial] at hcompare
  change ((advance compareProgram)^[u])
    (⟨some compareStart, compareControl, parsed a b⟩ :
      TM2.Cfg (fun _ : Stack => Bool) CylinderEqualMachine.Label CylinderEqualMachine.Control) =
      BitMachineStackEmbedding.cfg slots (parsed a b) id id none final at hcompare
  simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, id_eq, hfl] at hcompare
  obtain ⟨t, ht, hfull⟩ := BitMachineRawSequence.runs
    (BitMachineBankCodec.parser 2) compareProgram (.scan 0) compareStart
    none (some true) compareControl final.var
    (rawInit inputCell (.scan 0 : ParserLabel) (none : Option Bool) (input a b)).stk
    (parsed a b) (BitMachineStackEmbedding.bank slots (parsed a b) final.stk)
    p u hparse hcompare
  have hf : ((advance program)^[t]) (rawInit inputCell start control (input a b)) =
      ⟨none, (none, final.var), BitMachineStackEmbedding.bank slots (parsed a b) final.stk⟩ := hfull
  refine ⟨t, by omega, ?_, ?_⟩
  · rw [hf]
  · rw [hf]
    change BitMachineStackEmbedding.bank slots (parsed a b) final.stk (slots 2) = _
    rw [BitMachineStackEmbedding.bank_at]
    exact hfo

def clock (a b : List Bool) : Nat :=
  5 * ((input a b).length + 1) + min a.length b.length + 2

theorem outputs (a b : List Bool) :
    machine.OutputsWithin (input a b) [decide (a = b)] (clock a b) := by
  obtain ⟨t, ht, hh, ho⟩ := actual_run a b
  exact outputsWithin_of_raw_run inputCell outputCell start control program
    (input a b) [decide (a = b)] t (clock a b) ht hh ho

def coefficient : Nat := 7
def degree : Nat := 1

/-- One fixed linear polynomial, in the original framed input length,
covers every pair of arbitrary bitwords, including empty words. -/
theorem outputs_polynomial (a b : List Bool) :
    machine.OutputsWithin (input a b) [decide (a = b)]
      (coefficient * ((input a b).length + 1)^degree) := by
  apply BitMachine.outputsWithin_mono _ (outputs a b)
  have ha : a.length ≤ (input a b).length :=
    BitMachineBankCodec.word_length_le_encode (![a,b] : Fin 2 → List Bool) 0
  have hm := Nat.min_le_left a.length b.length
  simp only [clock, coefficient, degree, pow_one]
  omega

#print axioms actual_run
#print axioms outputs_polynomial
end CurrentAdditive.WordEqualityOrdinary
