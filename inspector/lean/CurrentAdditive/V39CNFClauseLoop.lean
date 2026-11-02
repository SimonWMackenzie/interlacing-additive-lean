import CurrentAdditive.V39CNFLiteral
import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-! A finite three-literal/OR controller, followed by clause conjunction.
The literal subroutine is the actual physical program V39CNFLiteral,
not a verifier callback. Malformed input is rejected by the separate
all-input preparation machine before this canonical stream is supplied. -/

namespace CurrentAdditive.V39CNFClauseLoop

open EthInapproximability.CurrentPaper
open Turing TM2.Stmt BitMachineEncoding BitMachineComposition


inductive Outer where | loop | after
  deriving DecidableEq, Fintype
abbrev Stack := V39CNFLiteral.Stack ⊕ Unit
abbrev Label := V39CNFLiteral.Label ⊕ Outer
abbrev Flags := Fin 3 × Bool × Bool
abbrev Control := V39CNFLiteral.Control × Flags

def phase (v : Control) : Fin 3 := v.2.1
def accumulated (v : Control) : Bool := v.2.2.1
def seen (v : Control) : Bool := v.2.2.2
def control (i : Fin 3) (b : Bool) : Control := (V39CNFLiteral.initial, i, b, false)
def finish (b : Control → Bool) : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  push (.inr ()) b halt

def call (i : Fin 3) : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  load (fun v => (V39CNFLiteral.initial, i, accumulated v, false)) (goto (fun _ => .inl V39CNFLiteral.start))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some Outer.after) (V39CNFLiteral.program l)
  | .inr .loop =>
      peek (.inl V39CNFLiteral.Stack.source) (fun v b => (v.1, 0, false, b.isSome))
        (branch seen (call 0) (finish (fun _ => true)))
  | .inr .after =>
      pop (.inl V39CNFLiteral.Stack.output)
        (fun v b => (v.1, phase v, accumulated v || b.getD false, false))
        (branch (fun v => decide (phase v = 0)) (call 1)
          (branch (fun v => decide (phase v = 1)) (call 2)
            (branch accumulated
              (load (fun _ => control 0 false) (goto (fun _ => .inr .loop)))
              (finish (fun _ => false)))))

def cfg (label : Option Label) (i : Fin 3) (b : Bool)
    (bank : V39CNFLiteral.Stack → List Bool) (out : List Bool := []) :
    TM2.Cfg (fun _ : Stack => Bool) Label Control :=
  ⟨label, control i b, Sum.elim bank (fun _ => out)⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :=
  ((advance program)^[t]) c

theorem run_add (a b : ℕ) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :
    run (a + b) c = run b (run a c) := by
  rw [run, show a + b = b + a by omega, Function.iterate_add_apply]
  rfl

theorem empty (assignment : List Bool) :
    (run 1 (cfg (some (.inr .loop)) 0 false (V39CNFLiteral.ready [] assignment))).l = none ∧
    (run 1 (cfg (some (.inr .loop)) 0 false (V39CNFLiteral.ready [] assignment))).stk (.inr ()) = [true] := by
  constructor <;> rfl

private theorem clear_bank (bank : V39CNFLiteral.Stack → List Bool) :
    Function.update (Sum.elim bank (fun _ : Unit => []))
        (.inl V39CNFLiteral.Stack.output) [] =
      Sum.elim (Function.update bank V39CNFLiteral.Stack.output []) (fun _ : Unit => []) := by
  funext k
  cases k with
  | inl k => by_cases h : k = V39CNFLiteral.Stack.output <;> simp [h, Function.update]
  | inr k => cases k; rfl

theorem after_first (bank : V39CNFLiteral.Stack → List Bool) (acc bit : Bool)
    (h : bank V39CNFLiteral.Stack.output = [bit]) :
    advance program (cfg (some (.inr .after)) 0 acc bank) =
      cfg (some (.inl V39CNFLiteral.start)) 1 (acc || bit)
        (Function.update bank V39CNFLiteral.Stack.output []) := by
  simp only [advance, cfg, control, program, TM2.step, TM2.stepAux,
    phase, accumulated, Sum.elim_inl, h, List.head?_cons, List.tail_cons,
    Option.getD_some, call]
  change (⟨some (.inl V39CNFLiteral.start), control 1 (acc || bit),
      Function.update (Sum.elim bank (fun _ : Unit => []))
        (.inl V39CNFLiteral.Stack.output) []⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Label Control) = _
  rw [clear_bank]
  rfl

theorem after_second (bank : V39CNFLiteral.Stack → List Bool) (acc bit : Bool)
    (h : bank V39CNFLiteral.Stack.output = [bit]) :
    advance program (cfg (some (.inr .after)) 1 acc bank) =
      cfg (some (.inl V39CNFLiteral.start)) 2 (acc || bit)
        (Function.update bank V39CNFLiteral.Stack.output []) := by
  simp only [advance, cfg, control, program, TM2.step, TM2.stepAux,
    phase, accumulated, Sum.elim_inl, h, List.head?_cons, List.tail_cons,
    Option.getD_some, call]
  change (⟨some (.inl V39CNFLiteral.start), control 2 (acc || bit),
      Function.update (Sum.elim bank (fun _ : Unit => []))
        (.inl V39CNFLiteral.Stack.output) []⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Label Control) = _
  rw [clear_bank]
  rfl

theorem after_third_good (bank : V39CNFLiteral.Stack → List Bool) (acc bit : Bool)
    (h : bank V39CNFLiteral.Stack.output = [bit]) (hgood : (acc || bit) = true) :
    advance program (cfg (some (.inr .after)) 2 acc bank) =
      cfg (some (.inr .loop)) 0 false
        (Function.update bank V39CNFLiteral.Stack.output []) := by
  simp only [advance, cfg, control, program, TM2.step, TM2.stepAux,
    phase, accumulated, Sum.elim_inl, h, List.head?_cons, List.tail_cons,
    Option.getD_some, call]
  change (bif acc || bit then _ else _) = _
  rw [hgood]
  change (⟨some (.inr .loop), control 0 false,
      Function.update (Sum.elim bank (fun _ : Unit => []))
        (.inl V39CNFLiteral.Stack.output) []⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Label Control) = _
  rw [clear_bank]
  rfl

theorem after_third_bad (bank : V39CNFLiteral.Stack → List Bool) (acc bit : Bool)
    (h : bank V39CNFLiteral.Stack.output = [bit]) (hbad : (acc || bit) = false) :
    (advance program (cfg (some (.inr .after)) 2 acc bank)).l = none ∧
    (advance program (cfg (some (.inr .after)) 2 acc bank)).stk (.inr ()) = [false] := by
  simp only [advance, cfg, control, program, TM2.step, TM2.stepAux,
    phase, accumulated, Sum.elim_inl, h, List.head?_cons, List.tail_cons,
    Option.getD_some, call, finish]
  rw [hbad]
  constructor <;> rfl

theorem enter (source assignment : List Bool) (h : source ≠ []) :
    advance program (cfg (some (.inr .loop)) 0 false
      (V39CNFLiteral.ready source assignment)) =
      cfg (some (.inl V39CNFLiteral.start)) 0 false
        (V39CNFLiteral.ready source assignment) := by
  cases source with
  | nil => contradiction
  | cons bit source => rfl

theorem clear_result (rest assignment : List Bool) (bit : Bool) :
    Function.update (V39CNFLiteral.resultBank rest assignment bit)
      V39CNFLiteral.Stack.output [] = V39CNFLiteral.ready rest assignment := by
  funext k
  by_cases hk : k = V39CNFLiteral.Stack.output
  · subst k; simp
  · simp [Function.update, V39CNFLiteral.resultBank, hk]

theorem append_run {a : ℕ} {c d : TM2.Cfg (fun _ : Stack => Bool) Label Control}
    (h : run a c = d) (b : ℕ) : run (a + b) c = run b d := by
  rw [run_add, h]

theorem append_step {a : ℕ} {c d : TM2.Cfg (fun _ : Stack => Bool) Label Control}
    (h : run a c = d) : run (a + 1) c = advance program d := by
  rw [run_add, h]
  rfl

theorem literal_run (l : EncodedCNF.Literal) (rest assignment : List Bool)
    (hvalid : l.variable < assignment.length) (i : Fin 3) (acc : Bool) :
    ∃ t ≤ V39CNFLiteral.coefficient *
        ((EncodedCNF.encodeLiteral l ++ rest).length + assignment.length + 1) ^
          V39CNFLiteral.exponent,
      run t (cfg (some (.inl V39CNFLiteral.start)) i acc
        (V39CNFLiteral.ready (EncodedCNF.encodeLiteral l ++ rest) assignment)) =
      cfg (some (.inr .after)) i acc
        (V39CNFLiteral.resultBank rest assignment (l.eval assignment)) := by
  obtain ⟨t, ht, he⟩ := V39CNFLiteral.canonical_run l assignment rest hvalid
  obtain ⟨u, hu, hr⟩ := BitMachineSubroutine.lift_outputs
    V39CNFLiteral.program program (some Outer.after) (fun _ => rfl)
    ((i, acc, false) : Flags) (fun _ : Unit => [])
    ⟨some V39CNFLiteral.start, V39CNFLiteral.initial,
      V39CNFLiteral.ready (EncodedCNF.encodeLiteral l ++ rest) assignment⟩ t (by
        change (V39CNFLiteral.run t _).l = none
        rw [he])
  change run u (cfg (some (.inl V39CNFLiteral.start)) i acc
      (V39CNFLiteral.ready (EncodedCNF.encodeLiteral l ++ rest) assignment)) =
    liftCfg (some Outer.after) (i, acc, false) (fun _ : Unit => [])
      (V39CNFLiteral.run t _) at hr
  rw [he] at hr
  exact ⟨u, hu.trans ht, hr⟩

def horizon (source assignment : List Bool) : ℕ :=
  V39CNFLiteral.coefficient * (source.length + assignment.length + 1) ^
    V39CNFLiteral.exponent

theorem horizon_mono {source tail assignment : List Bool}
    (h : tail.length ≤ source.length) : horizon tail assignment ≤ horizon source assignment := by
  unfold horizon
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

def clauseResult (c : EncodedCNF.Clause) (rest assignment : List Bool)
    (r : TM2.Cfg (fun _ : Stack => Bool) Label Control) : Prop :=
  if c.eval assignment then
    r = cfg (some (.inr .loop)) 0 false (V39CNFLiteral.ready rest assignment)
  else r.l = none ∧ r.stk (.inr ()) = [false]

theorem clause_run (c : EncodedCNF.Clause) (rest assignment : List Bool)
    (hv : c.Valid assignment.length) :
    ∃ t ≤ 3 * horizon (EncodedCNF.encodeClause c ++ rest) assignment + 4,
      clauseResult c rest assignment
        (run t (cfg (some (.inr .loop)) 0 false
          (V39CNFLiteral.ready (EncodedCNF.encodeClause c ++ rest) assignment))) := by
  let tail₂ := EncodedCNF.encodeLiteral c.third ++ rest
  let tail₁ := EncodedCNF.encodeLiteral c.second ++ tail₂
  let source := EncodedCNF.encodeLiteral c.first ++ tail₁
  have hsource : source = EncodedCNF.encodeClause c ++ rest := by
    simp only [source, tail₁, tail₂, EncodedCNF.encodeClause, List.append_assoc]
  have hnonempty : source ≠ [] := by simp [source, EncodedCNF.encodeLiteral]
  obtain ⟨t₁, ht₁, hr₁⟩ := literal_run c.first tail₁ assignment hv.1 0 false
  obtain ⟨t₂, ht₂, hr₂⟩ := literal_run c.second tail₂ assignment hv.2.1 1
    (false || c.first.eval assignment)
  obtain ⟨t₃, ht₃, hr₃⟩ := literal_run c.third rest assignment hv.2.2 2
    ((false || c.first.eval assignment) || c.second.eval assignment)
  have hc₁ := after_first (V39CNFLiteral.resultBank tail₁ assignment (c.first.eval assignment))
    false (c.first.eval assignment) (by simp)
  rw [clear_result] at hc₁
  have hc₂ := after_second (V39CNFLiteral.resultBank tail₂ assignment (c.second.eval assignment))
    (false || c.first.eval assignment) (c.second.eval assignment) (by simp)
  rw [clear_result] at hc₂
  have h₀ : run 1 (cfg (some (.inr .loop)) 0 false (V39CNFLiteral.ready source assignment)) =
      cfg (some (.inl V39CNFLiteral.start)) 0 false (V39CNFLiteral.ready source assignment) :=
    enter source assignment hnonempty
  have h₁ := (append_run h₀ t₁).trans hr₁
  have h₂ := (append_step h₁).trans hc₁
  have h₃ := (append_run h₂ t₂).trans hr₂
  have h₄ := (append_step h₃).trans hc₂
  have h₅ := (append_run h₄ t₃).trans hr₃
  have hl₁ : t₁ ≤ horizon source assignment := ht₁
  have hl₂ : t₂ ≤ horizon source assignment := ht₂.trans (horizon_mono (by
    simp only [source, tail₁, List.length_append]; omega))
  have hl₃ : t₃ ≤ horizon source assignment := ht₃.trans (horizon_mono (by
    simp only [source, tail₁, tail₂, List.length_append]; omega))
  refine ⟨1 + t₁ + 1 + t₂ + 1 + t₃ + 1, ?_, ?_⟩
  · rw [← hsource]
    omega
  · rw [← hsource]
    unfold clauseResult
    have hev : (((false || c.first.eval assignment) || c.second.eval assignment) ||
        c.third.eval assignment) = c.eval assignment := by
      simp [EncodedCNF.Clause.eval, Bool.or_assoc]
    cases hc : c.eval assignment with
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      have hstep := after_third_bad
        (V39CNFLiteral.resultBank rest assignment (c.third.eval assignment))
        ((false || c.first.eval assignment) || c.second.eval assignment)
        (c.third.eval assignment) (by simp) (hev.trans hc)
      rw [append_step h₅]
      exact hstep
    | true =>
      simp only [hc, ↓reduceIte]
      have hstep := after_third_good
        (V39CNFLiteral.resultBank rest assignment (c.third.eval assignment))
        ((false || c.first.eval assignment) || c.second.eval assignment)
        (c.third.eval assignment) (by simp) (hev.trans hc)
      rw [clear_result] at hstep
      exact (append_step h₅).trans hstep

def budget (cs : List EncodedCNF.Clause) (assignment : List Bool) : ℕ :=
  (cs.length + 1) * (3 * horizon (EncodedCNF.clauseFields cs) assignment + 4)

theorem clauses_run (cs : List EncodedCNF.Clause) (assignment : List Bool)
    (hv : ∀ c ∈ cs, c.Valid assignment.length) :
    ∃ t ≤ budget cs assignment,
      (run t (cfg (some (.inr .loop)) 0 false
        (V39CNFLiteral.ready (EncodedCNF.clauseFields cs) assignment))).l = none ∧
      (run t (cfg (some (.inr .loop)) 0 false
        (V39CNFLiteral.ready (EncodedCNF.clauseFields cs) assignment))).stk (.inr ()) =
          [cs.all (fun c => c.eval assignment)] := by
  induction cs with
  | nil =>
    refine ⟨1, ?_, ?_⟩
    · simp only [budget, List.length_nil, zero_add, one_mul]; omega
    · exact empty assignment
  | cons c cs ih =>
    obtain ⟨t, ht, hr⟩ := clause_run c (EncodedCNF.clauseFields cs) assignment
      (hv c (by simp))
    have htail : ∀ d ∈ cs, d.Valid assignment.length := fun d hd => hv d (by simp [hd])
    have hmono : horizon (EncodedCNF.clauseFields cs) assignment ≤
        horizon (EncodedCNF.clauseFields (c :: cs)) assignment := horizon_mono (by
      simp only [EncodedCNF.clauseFields, List.length_append]; omega)
    have ht' : t ≤ 3 * horizon (EncodedCNF.clauseFields (c :: cs)) assignment + 4 := ht
    cases hc : c.eval assignment with
    | false =>
      refine ⟨t, ?_, ?_⟩
      · exact ht'.trans (Nat.le_mul_of_pos_left _ (by omega))
      · simp only [clauseResult, hc, Bool.false_eq_true, ↓reduceIte] at hr
        simpa only [List.all_cons, hc, Bool.false_and] using hr
    | true =>
      obtain ⟨u, hu, he⟩ := ih htail
      have hu' : u ≤ (cs.length + 1) *
          (3 * horizon (EncodedCNF.clauseFields (c :: cs)) assignment + 4) :=
        hu.trans (Nat.mul_le_mul_left _ (by omega))
      refine ⟨t + u, ?_, ?_⟩
      · calc
          t + u ≤ (3 * horizon (EncodedCNF.clauseFields (c :: cs)) assignment + 4) +
              (cs.length + 1) *
                (3 * horizon (EncodedCNF.clauseFields (c :: cs)) assignment + 4) :=
            Nat.add_le_add ht' hu'
          _ = budget (c :: cs) assignment := by
            simp only [budget, List.length_cons]
            ring
      · simp only [clauseResult, hc, ↓reduceIte] at hr
        simp only [EncodedCNF.clauseFields]
        rw [append_run hr]
        simpa only [List.all_cons, hc, Bool.true_and] using he

theorem budget_bound (cs : List EncodedCNF.Clause) (assignment : List Bool) :
    budget cs assignment ≤
      400 * ((EncodedCNF.clauseFields cs).length + assignment.length + 1) ^ 4 := by
  let N := (EncodedCNF.clauseFields cs).length + assignment.length + 1
  have hn : 1 ≤ N := by omega
  have hl : cs.length + 1 ≤ N := by
    have h := EncodedCNF.clauseFields_length_lower cs
    omega
  have hn₂ : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hn
  have hq : 3 * horizon (EncodedCNF.clauseFields cs) assignment + 4 ≤ 304 * N ^ 2 := by
    unfold horizon V39CNFLiteral.coefficient V39CNFLiteral.exponent
    change 3 * (100 * N ^ 2) + 4 ≤ 304 * N ^ 2
    omega
  calc
    budget cs assignment ≤ N * (304 * N ^ 2) := Nat.mul_le_mul hl hq
    _ = 304 * N ^ 3 := by ring
    _ ≤ 400 * N ^ 4 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hn (by omega))

theorem canonical_run (cs : List EncodedCNF.Clause) (assignment : List Bool)
    (hv : ∀ c ∈ cs, c.Valid assignment.length) :
    ∃ t ≤ 400 * ((EncodedCNF.clauseFields cs).length + assignment.length + 1) ^ 4,
      (run t (cfg (some (.inr .loop)) 0 false
        (V39CNFLiteral.ready (EncodedCNF.clauseFields cs) assignment))).l = none ∧
      (run t (cfg (some (.inr .loop)) 0 false
        (V39CNFLiteral.ready (EncodedCNF.clauseFields cs) assignment))).stk (.inr ()) =
          [cs.all (fun c => c.eval assignment)] := by
  obtain ⟨t, ht, he⟩ := clauses_run cs assignment hv
  exact ⟨t, ht.trans (budget_bound cs assignment), he⟩

#print axioms literal_run
#print axioms clause_run
#print axioms clauses_run
#print axioms canonical_run

end CurrentAdditive.V39CNFClauseLoop
