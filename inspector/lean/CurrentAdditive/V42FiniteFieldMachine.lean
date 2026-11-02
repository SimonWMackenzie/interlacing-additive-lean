import CurrentAdditive.V42FiniteFieldList
import CurrentAdditive.D22NatExpression
import EthInapproximability.CurrentPaper.BitMachineStackRun

namespace CurrentAdditive.V42FiniteFieldMachine

open Turing Turing.TM2.Stmt EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldMachine

namespace Field
export CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine
  (Stack Label Control program initialConfig initialStack prepEmbed run run_eq_any
    prepTime physical_firstPassing_packed_from_unary fieldSlots)
end Field

namespace Parser
inductive Label where | degree | width deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Bool
  | .degree => pop 0 (fun _ b => b.getD false)
      (branch id (push 1 (fun _ => true) (goto (fun _ => .degree)))
        (goto (fun _ => .width)))
  | .width => pop 0 (fun _ b => b.isSome)
      (branch id (push 2 (fun _ => true) (goto (fun _ => .width)))
        (load (fun _ => false) halt))

def cfg (l : Option Label) (s : Bool) (input left right : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label Bool :=
  ⟨l, s, ![input, left, right]⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Bool) :=
  ((advance program)^[t]) c

private theorem run_succ {c e : TM2.Cfg (fun _ : Fin 3 => Bool) Label Bool}
    (h : TM2.step program c = some e) (t : ℕ) : run (t + 1) c = run t e := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem degree_cons (s : Bool) (bits left right : List Bool) :
    TM2.step program (cfg (some .degree) s (true :: bits) left right) =
      some (cfg (some .degree) true bits (true :: left) right) := by
  apply congrArg (fun S => some (⟨some .degree, true, S⟩ :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label Bool))
  funext i
  fin_cases i <;> rfl

private theorem degree_end (s : Bool) (bits left right : List Bool) :
    TM2.step program (cfg (some .degree) s (false :: bits) left right) =
      some (cfg (some .width) false bits left right) := by
  apply congrArg (fun S => some (⟨some .width, false, S⟩ :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label Bool))
  funext i
  fin_cases i <;> rfl

private theorem width_cons (s : Bool) (bits left right : List Bool) :
    TM2.step program (cfg (some .width) s (true :: bits) left right) =
      some (cfg (some .width) true bits left (true :: right)) := by
  apply congrArg (fun S => some (⟨some .width, true, S⟩ :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label Bool))
  funext i
  fin_cases i <;> rfl

private theorem width_end (s : Bool) (left right : List Bool) :
    TM2.step program (cfg (some .width) s [] left right) =
      some (cfg none false [] left right) := by
  apply congrArg (fun S => some (⟨none, false, S⟩ :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label Bool))
  funext i
  fin_cases i <;> rfl

theorem degree_run (d k : ℕ) (s : Bool) (bits right : List Bool) :
    run (d+1) (cfg (some .degree) s
      (List.replicate d true ++ false :: bits) (List.replicate k true) right) =
      cfg (some .width) false bits (List.replicate (d+k) true) right := by
  induction d generalizing k s with
  | zero => simpa using run_succ (degree_end s bits (List.replicate k true) right) 0
  | succ d ih =>
      rw [List.replicate_succ, List.cons_append, run_succ (degree_cons _ _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 k] using ih (k+1) true

theorem width_run (n k : ℕ) (s : Bool) (left : List Bool) :
    run (n+1) (cfg (some .width) s
      (List.replicate n true) left (List.replicate k true)) =
      cfg none false [] left (List.replicate (n+k) true) := by
  induction n generalizing k s with
  | zero => simpa using run_succ (width_end s left (List.replicate k true)) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (width_cons _ _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 k] using ih (k+1) true

theorem full_run (d n : ℕ) :
    run (d+n+2) (cfg (some .degree) false
      (MatrixUnaryArithmetic.encodeInput d n) [] []) =
      cfg none false [] (List.replicate d true) (List.replicate n true) := by
  have hadd : d+n+2 = (n+1)+(d+1) := by omega
  rw [hadd, run, Function.iterate_add_apply]
  change run (n+1) (run (d+1) _) = _
  have hd := degree_run d 0 false (List.replicate n true) []
  simp only [Nat.add_zero, List.replicate_zero] at hd
  change run (d+1) (cfg (some .degree) false
    (MatrixUnaryArithmetic.encodeInput d n) [] []) = _ at hd
  rw [hd]
  simpa using width_run n 0 false (List.replicate d true)
end Parser

abbrev Stack := Unit ⊕ Field.Stack

def parserSlots : Fin 3 ↪ Stack where
  toFun := ![.inl (), .inr (.inl 0), .inr (.inl 1)]
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def fieldSlots : Field.Stack ↪ Stack where
  toFun := Sum.inr
  inj' := by intro a b h; exact Sum.inr.inj h

def parseProgram := fun l => stackStmt parserSlots (Parser.program l)
def fieldProgram := fun l => stackStmt fieldSlots (Field.program l)

def program := BitMachineRawSequence.program parseProgram fieldProgram
  (.prep .scanD) false (Field.prepEmbed none)

def start : BitMachineRawSequence.Label Parser.Label Field.Label :=
  BitMachineRawSequence.leftLabel Parser.Label.degree
def control := (false, Field.prepEmbed none)
def output : Stack := .inr (Field.fieldSlots
  (FieldSearchPrinterHandoff.printerSlots FieldListOutputMachine.output))

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inl ()) output start control program

set_option maxHeartbeats 1500000

private theorem parser_stack (l : Option Parser.Label) (s : Bool)
    (input left right : List Bool) (k : Stack) :
    (stackCfg parserSlots (fun _ => []) (Parser.cfg l s input left right)).stk k =
      if k = (.inl () : Stack) then input else
        if k = .inr (.inl 0) then left else
          if k = .inr (.inl 1) then right else [] := by
  by_cases h0 : k = (.inl () : Stack)
  · subst k
    simpa only [stackCfg, parserSlots, Parser.cfg, dif_pos, ↓reduceIte] using
      bank_at parserSlots (fun _ => []) (Parser.cfg l s input left right).stk 0
  · by_cases h1 : k = .inr (.inl 0)
    · subst k
      simpa only [stackCfg, parserSlots, Parser.cfg, ↓reduceIte] using
        bank_at parserSlots (fun _ => []) (Parser.cfg l s input left right).stk 1
    · by_cases h2 : k = .inr (.inl 1)
      · subst k
        simpa only [stackCfg, parserSlots, Parser.cfg, ↓reduceIte] using
          bank_at parserSlots (fun _ => []) (Parser.cfg l s input left right).stk 2
      · rw [if_neg h0, if_neg h1, if_neg h2]
        apply bank_outside
        rintro ⟨i, hi⟩
        fin_cases i <;> simp_all [parserSlots]

private theorem initial_stacks (d n : ℕ) :
    (stackCfg parserSlots (fun _ => [])
      (Parser.cfg (some .degree) false (MatrixUnaryArithmetic.encodeInput d n) [] [])).stk =
      fun k => if k = (.inl () : Stack) then MatrixUnaryArithmetic.encodeInput d n else [] := by
  funext k
  rw [parser_stack]
  split_ifs <;> rfl

private theorem parsed_stacks (d n : ℕ) :
    (stackCfg parserSlots (fun _ => [])
      (Parser.cfg none false [] (List.replicate d true) (List.replicate n true))).stk =
      (stackCfg fieldSlots (fun _ => []) (Field.initialConfig d n)).stk := by
  funext k
  rw [parser_stack]
  rcases k with k | k
  · cases k
    simp only [↓reduceIte]
    symm
    apply bank_outside fieldSlots (fun _ => []) (Field.initialConfig d n).stk
    rintro ⟨i, hi⟩
    simp [fieldSlots] at hi
  · rcases k with k | k
    · have hb := bank_at fieldSlots (fun _ => []) (Field.initialConfig d n).stk (.inl k)
      change _ = bank fieldSlots (fun _ => []) (Field.initialConfig d n).stk (fieldSlots (.inl k))
      rw [hb]
      fin_cases k <;> simp [Field.initialConfig, Field.initialStack]
    · have hb := bank_at fieldSlots (fun _ => []) (Field.initialConfig d n).stk (.inr k)
      change _ = bank fieldSlots (fun _ => []) (Field.initialConfig d n).stk (fieldSlots (.inr k))
      rw [hb]
      simp [Field.initialConfig, Field.initialStack]

/-- One fixed finite Boolean-stack machine parses the two unary parameters,
performs the actual first-passing polynomial search, and prints every bit.
Neither irreducibility nor a search/runtime certificate is supplied. -/
theorem machine_outputs (d n : ℕ) (hd : 0 < d) :
    ∃ c < 2 ^ d,
      FiniteFieldConstructor.TrialSearch.firstPassing d =
        some (FiniteFieldConstructor.TrialSearch.monicBits d c) ∧
      machine.OutputsWithin (MatrixUnaryArithmetic.encodeInput d n)
        (UnifiedFieldListMachine.packedBits d c n)
        (d+n+3 + Field.prepTime d n +
          55 * 2 ^ d * 2 ^ (d / 2) * (d+1)^2 + 2 +
          FieldListOutputMachine.timeBound d c n) := by
  obtain ⟨c, hc, hfirst, t, ht, hhalt, hout⟩ :=
    Field.physical_firstPassing_packed_from_unary d n hd
  let q := Field.run t (Field.initialConfig d n)
  let S := (stackCfg fieldSlots (fun _ => []) (Field.initialConfig d n)).stk
  let T := (stackCfg fieldSlots (fun _ => []) q).stk
  have hp := BitMachineStackRun.run parserSlots (fun _ => []) Parser.program
    (Parser.cfg (some .degree) false (MatrixUnaryArithmetic.encodeInput d n) [] []) (d+n+2)
  rw [← Parser.run, Parser.full_run] at hp
  have hstart : stackCfg parserSlots (fun _ => [])
      (Parser.cfg (some Parser.Label.degree) false (MatrixUnaryArithmetic.encodeInput d n) [] []) =
      (⟨some Parser.Label.degree, false,
        fun k => if k = (.inl () : Stack) then MatrixUnaryArithmetic.encodeInput d n else []⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) := by
    exact congrArg (fun A => (⟨some Parser.Label.degree, false, A⟩ :
      TM2.Cfg (fun _ : Stack => Bool) _ _)) (initial_stacks d n)
  have hend : stackCfg parserSlots (fun _ => [])
      (Parser.cfg none false [] (List.replicate d true) (List.replicate n true)) =
      (⟨none, false, S⟩ : TM2.Cfg (fun _ : Stack => Bool) Parser.Label Bool) := by
    exact congrArg (fun A => (⟨none, false, A⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Parser.Label Bool)) (parsed_stacks d n)
  rw [hstart, hend] at hp
  have hp' : ((advance parseProgram)^[d+n+2])
      (⟨some Parser.Label.degree, false,
        fun k => if k = (.inl () : Stack) then MatrixUnaryArithmetic.encodeInput d n else []⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) = ⟨none, false, S⟩ := by
    exact hp
  have hf := BitMachineStackRun.run fieldSlots (fun _ => []) Field.program
    (Field.initialConfig d n) t
  rw [← Field.run_eq_any (inferInstance : DecidableEq Field.Stack)] at hf
  have hf' : ((advance fieldProgram)^[t])
      (⟨some (.prep .scanD), Field.prepEmbed none, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) = ⟨none, q.var, T⟩ := by
    simpa only [fieldProgram, stackCfg, S, T, q, hhalt] using hf
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs parseProgram fieldProgram
    Parser.Label.degree (.prep .scanD) false false (Field.prepEmbed none) q.var
    _ S T (d+n+2) t hp' hf'
  refine ⟨c, hc, hfirst, ?_⟩
  apply outputsWithin_of_raw_run (.inl ()) output start control program
    (MatrixUnaryArithmetic.encodeInput d n) (UnifiedFieldListMachine.packedBits d c n)
    steps _ (by omega)
  · simpa only [program, start, control, rawInit] using congrArg TM2.Cfg.l hrun
  · have hs := congrArg TM2.Cfg.stk hrun
    change (((advance program)^[steps])
      (rawInit (.inl ()) start control (MatrixUnaryArithmetic.encodeInput d n))).stk output = _
    change (((advance program)^[steps])
      (rawInit (.inl ()) start control (MatrixUnaryArithmetic.encodeInput d n))).stk = T at hs
    rw [hs]
    exact (bank_at fieldSlots (fun _ => []) q.stk _).trans hout

#print axioms machine_outputs

end CurrentAdditive.V42FiniteFieldMachine


