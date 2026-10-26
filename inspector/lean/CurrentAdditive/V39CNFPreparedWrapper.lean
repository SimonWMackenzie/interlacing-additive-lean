import CurrentAdditive.V39CNFClauseLoop
import EthInapproximability.CurrentPaper.EncodedComplexity
import EthInapproximability.CurrentPaper.ProtocolWordField
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! Physical setup of the actual clause evaluator from the prepared packet.
The parser's source is already the evaluator's assignment stack; its target
is already the evaluator's literal-stream stack. Its charged reversal and
restore therefore install the exact ready bank without an abstract copy. -/
namespace CurrentAdditive.V39CNFPreparedWrapper

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open EthInapproximability.CurrentPaper
open Turing TM2.Stmt BitMachineEncoding BitMachineComposition

abbrev Stack := V39CNFClauseLoop.Stack
inductive Outer where | entry | after
  deriving DecidableEq, Fintype
abbrev Label := V39CNFClauseLoop.Label ⊕ (ProtocolWordField.Label ⊕ Outer)
abbrev Control := V39CNFClauseLoop.Control × (ProtocolWordField.Control × Option Bool)

def source : Stack := .inl V39CNFLiteral.Stack.source
def assignment : Stack := .inl V39CNFLiteral.Stack.assignment
def saved : Stack := .inl V39CNFLiteral.Stack.saved
def output : Stack := .inr ()
def parserMap : Fin 3 ↪ Stack where
  toFun := fun k => if k = 0 then assignment else if k = 1 then saved else source
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> first | rfl | contradiction

def parserLabel (l : ProtocolWordField.Label) : Label := .inr (.inl l)
def parserControl (v : ProtocolWordField.Control) : Control :=
  (V39CNFClauseLoop.control 0 false, v, none)
def loopControl (v : V39CNFClauseLoop.Control) : Control := (v, (none, none), none)
def remember (v : Control) (b : Option Bool) : Control := (v.1, v.2.1, b)
def initial : Control := loopControl (V39CNFClauseLoop.control 0 false)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineInline.stmt Sum.inl loopControl Prod.fst none
      (V39CNFClauseLoop.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt parserMap parserLabel
      parserControl (fun v => v.2.1) (some (.inr (.inr .after)))
      (ProtocolWordField.program l)
  | .inr (.inr .entry) => pop assignment remember
      (branch (fun v => v.2.2.getD false)
        (load (fun _ => parserControl (none, none))
          (goto (fun _ => parserLabel .scan)))
        (push output (fun _ => false) halt))
  | .inr (.inr .after) => pop source remember
      (branch (fun v => v.2.2.getD false)
        (load (fun _ => initial) (goto (fun _ => .inl (.inr .loop))))
        (push output (fun _ => false) halt))

noncomputable def rawMachine : BitMachine.Machine :=
  ofFinite assignment output (.inr (.inr .entry)) initial program
noncomputable def machine : BitMachine.Machine := rawMachine
def run (t : ℕ) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :=
  ((advance program)^[t]) c
theorem run_add (s t : ℕ) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :
    run (s + t) c = run t (run s c) := by
  rw [run, show s + t = t + s by omega, Function.iterate_add_apply]
  rfl

def parserBank (input scratch target : List Bool) : Stack → List Bool :=
  Sum.elim (V39CNFLiteral.bank [] [] [] [] target input [] scratch) (fun _ => [])
def parserCfg (l : Option Label) (v : Control) (input scratch target : List Bool) :
    TM2.Cfg (fun _ : Stack => Bool) Label Control := ⟨l, v, parserBank input scratch target⟩

theorem parser_bank (input scratch target : List Bool) :
    BitMachineStackEmbedding.bank parserMap (fun _ => [])
      (ProtocolWordField.stackContents input scratch target) = parserBank input scratch target := by
  funext k
  cases k with
  | inr k =>
    rw [BitMachineStackEmbedding.bank_outside]
    · rfl
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp [parserMap, assignment, saved, source] at hi
  | inl k =>
    cases k with
    | inl k =>
      rw [BitMachineStackEmbedding.bank_outside]
      · fin_cases k <;> rfl
      · rintro ⟨i, hi⟩
        fin_cases i <;> simp [parserMap, assignment, saved, source,
          V39CNFLiteral.Stack.assignment, V39CNFLiteral.Stack.saved,
          V39CNFLiteral.Stack.source] at hi
    | inr k =>
      cases k with
      | source => exact BitMachineStackEmbedding.bank_at parserMap (fun _ => []) _ (2 : Fin 3)
      | assignment => exact BitMachineStackEmbedding.bank_at parserMap (fun _ => []) _ (0 : Fin 3)
      | saved => exact BitMachineStackEmbedding.bank_at parserMap (fun _ => []) _ (1 : Fin 3)
      | output =>
        rw [BitMachineStackEmbedding.bank_outside]
        · rfl
        · rintro ⟨i, hi⟩
          fin_cases i <;> simp [parserMap, assignment, saved, source,
            V39CNFLiteral.Stack.assignment, V39CNFLiteral.Stack.saved,
            V39CNFLiteral.Stack.source] at hi

theorem parser_cfg (l : Option ProtocolWordField.Label) (v : ProtocolWordField.Control)
    (input scratch target : List Bool) :
    BitMachineStackEmbedding.cfg parserMap (fun _ => []) parserLabel parserControl
      (some (.inr (.inr .after))) (ProtocolWordField.cfg l v input scratch target) =
      parserCfg (match l with | none => some (.inr (.inr .after)) | some l => some (parserLabel l))
        (parserControl v) input scratch target := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg ProtocolWordField.cfg parserCfg
  rw [parser_bank]
  cases l <;> rfl

theorem initial_entry (stream a : List Bool) :
    advance program (rawInit assignment (.inr (.inr .entry)) initial
      (true :: EncodedComplexity.pair stream a)) =
      parserCfg (some (parserLabel .scan)) (parserControl (none, none))
        (EncodedComplexity.pair stream a) [] [] := by
  simp only [advance, rawInit, program, TM2.step, TM2.stepAux, remember,
    Function.update_self, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_true, parserCfg, parserBank, initial, ite_true, ite_false]
  congr 1
  funext k
  cases k with
  | inr k => cases k; rfl
  | inl k =>
    cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => cases k <;> rfl

theorem after_ready (v : ProtocolWordField.Control) (stream a : List Bool) :
    advance program (parserCfg (some (.inr (.inr .after))) (parserControl v)
        a [] (true :: stream)) =
      BitMachineInline.cfg Sum.inl loopControl none
        (V39CNFClauseLoop.cfg (some (.inr .loop)) 0 false (V39CNFLiteral.ready stream a)) := by
  simp only [advance, parserCfg, parserBank, program, TM2.step, TM2.stepAux,
    source, V39CNFLiteral.bank, V39CNFLiteral.Stack.source, Sum.elim_inl,
    Sum.elim_inr, List.head?_cons, List.tail_cons, remember, parserControl,
    Option.getD_some, Bool.cond_true, BitMachineInline.cfg]
  congr 1
  funext k
  cases k with
  | inr k => cases k; rfl
  | inl k =>
    cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => cases k <;> rfl

theorem prepared_setup (stream a : List Bool) :
    ∃ t ≤ 2 * (EncodedComplexity.pair stream a).length + 4,
      run t (rawInit assignment (.inr (.inr .entry)) initial
        (true :: EncodedComplexity.pair stream a)) =
      BitMachineInline.cfg Sum.inl loopControl none
        (V39CNFClauseLoop.cfg (some (.inr .loop)) 0 false (V39CNFLiteral.ready stream a)) := by
  obtain ⟨t, ht, hp⟩ := ProtocolWordField.scan_correct
    (EncodedComplexity.pair stream a) none none [] []
  let c := ProtocolWordField.run t (ProtocolWordField.cfg (some .scan) (none, none)
    (EncodedComplexity.pair stream a) [] [])
  have hh : c.l = none := hp.1
  have hs : c.stk 0 = a ∧ c.stk 1 = [] ∧ c.stk 2 = true :: stream := by
    simpa only [ProtocolWordField.Post, EncodedComplexity.pair,
      EncodedCommunication.readField_append, List.reverse_nil,
      List.nil_append, List.append_nil] using hp.2
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs parserMap (fun _ => [])
    parserLabel parserControl (fun v => v.2.1) (fun _ => rfl)
    (some (.inr (.inr .after))) ProtocolWordField.program program (fun _ => rfl)
    (ProtocolWordField.cfg (some .scan) (none, none)
      (EncodedComplexity.pair stream a) [] []) t hh
  have hc : c = ProtocolWordField.cfg none c.var a [] (true :: stream) := by
    cases hce : c with
    | mk l v S =>
      rw [hce] at hh hs
      change l = none at hh
      change S 0 = a ∧ S 1 = [] ∧ S 2 = true :: stream at hs
      cases hh
      congr 1
      funext k
      fin_cases k
      · exact hs.1
      · exact hs.2.1
      · exact hs.2.2
  change ((advance program)^[u]) _ = BitMachineStackEmbedding.cfg _ _ _ _ _ c at hr
  rw [parser_cfg, hc, parser_cfg] at hr
  refine ⟨1 + u + 1, by simp only [List.length_nil] at ht; omega, ?_⟩
  rw [run_add (1 + u) 1, run_add 1 u]
  simp only [run, Function.iterate_one]
  rw [initial_entry, hr, after_ready]

theorem outputs_false : rawMachine.OutputsWithin [false] [false] 1 := by
  apply outputsWithin_of_raw_run assignment output (.inr (.inr .entry)) initial
    program [false] [false] 1 1 le_rfl
  · rfl
  · rfl

theorem outputs_clauses (cs : List EncodedCNF.Clause) (a : List Bool)
    (hv : ∀ c ∈ cs, c.Valid a.length) :
    machine.OutputsWithin
      (true :: EncodedComplexity.pair (EncodedCNF.clauseFields cs) a)
      [cs.all (fun c => c.eval a)]
      (410 * ((true :: EncodedComplexity.pair (EncodedCNF.clauseFields cs) a).length + 1) ^ 4) := by
  let stream := EncodedCNF.clauseFields cs
  let input := true :: EncodedComplexity.pair stream a
  obtain ⟨s, hs, hr⟩ := prepared_setup stream a
  obtain ⟨t, ht, hh, ho⟩ := V39CNFClauseLoop.canonical_run cs a hv
  obtain ⟨u, hu, he⟩ := BitMachineInline.outputs Sum.inl loopControl Prod.fst
    (fun _ => rfl) none V39CNFClauseLoop.program program (fun _ => rfl)
    (V39CNFClauseLoop.cfg (some (.inr .loop)) 0 false (V39CNFLiteral.ready stream a))
    t hh
  have hrun : run (s + u) (rawInit assignment (.inr (.inr .entry)) initial input) =
      BitMachineInline.cfg Sum.inl loopControl none
        (V39CNFClauseLoop.run t
          (V39CNFClauseLoop.cfg (some (.inr .loop)) 0 false (V39CNFLiteral.ready stream a))) := by
    rw [run, show s + u = u + s by omega, Function.iterate_add_apply]
    change ((advance program)^[u]) (run s _) = _
    rw [hr]
    exact he
  have hbase : stream.length + a.length + 1 ≤ input.length + 1 := by
    simp only [input, EncodedComplexity.pair, List.length_cons, List.length_append,
      EncodedCommunication.field_length]
    omega
  have hpow : (stream.length + a.length + 1) ^ 4 ≤ (input.length + 1) ^ 4 :=
    Nat.pow_le_pow_left hbase 4
  have hlin : input.length + 1 ≤ (input.length + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ input.length + 1) (show 1 ≤ 4 by decide)
  apply outputsWithin_of_raw_run assignment output (.inr (.inr .entry)) initial
    program input [cs.all (fun c => c.eval a)] (s + u) _
      (by change t ≤ 400 * (stream.length + a.length + 1) ^ 4 at ht
          have hi : (EncodedComplexity.pair stream a).length + 1 = input.length := rfl
          nlinarith)
  · change (run (s + u) _).l = none
    rw [hrun]
    simpa only [BitMachineInline.cfg, stream, hh]
  · change (run (s + u) _).stk output = _
    rw [hrun]
    exact ho

#print axioms prepared_setup
#print axioms outputs_false
#print axioms outputs_clauses

end CurrentAdditive.V39CNFPreparedWrapper
