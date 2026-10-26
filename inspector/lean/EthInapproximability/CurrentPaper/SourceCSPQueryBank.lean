import EthInapproximability.CurrentPaper.SourceCSPQueryRange

/-!
# One checked query call inside a fixed-arity row bank

Source: frozen v8 `06-eth.tex`, Boolean CSP conversion. This inlines the
actual preserving range validator at one selected query position. Each query
position owns private work stacks, so subsequent calls cannot observe its
residual bounded-subtraction counters. The all-query control loop is a
separate theorem and program.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPQueryBank

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack (q : Nat) := (Fin q × Fin 5) ⊕ Fin 2
abbrev Control := SourceCSPQueryRange.Control × Option Bool

inductive Label (q : Nat) where
  | start (i : Fin (q + 1))
  | check (i : Fin q) (l : SourceCSPQueryRange.Label)
  | after (i : Fin q)
  deriving DecidableEq, Fintype

def select {q : Nat} (i : Fin q) : SourceCSPQueryRange.Stack ↪ Stack q where
  toFun k := if k = 0 then .inl (i, 0)
    else if k = 1 then .inr 0
    else if k = 2 then .inl (i, 2)
    else if k = 3 then .inl (i, 3)
    else if k = 4 then .inl (i, 4)
    else .inl (i, 1)
  inj' := by intro x y h; fin_cases x <;> fin_cases y <;> simp_all

def startBank {q : Nat} (query : Fin q → List Bool) (cap : List Bool) :
    Stack q → List Bool :=
  Sum.elim (fun p => if p.2 = 0 then query p.1 else [])
    (fun k => if k = 0 then cap else [])

def program {q : Nat} : Label q →
    TM2.Stmt (fun _ : Stack q => Bool) (Label q) Control
  | .start i =>
      if h : i.val < q then
        .load (fun _ => (((none, none), (none, false)), none))
          (.goto (fun _ => .check ⟨i.val, h⟩
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))
      else .push (.inr 1) (fun _ => true) .halt
  | .check i l => stmt (select i) (.check i) (fun v => (v, none)) Prod.fst
      (some (.after i)) (SourceCSPQueryRange.program l)
  | .after i =>
      .pop (.inl (i, 1)) (fun v b => (v.1, b))
        (.branch (fun v => v.2.getD false)
          (.goto (fun _ => .start ⟨i.val + 1, by omega⟩))
          (.push (.inr 1) (fun _ => false) .halt))

abbrev Config (q : Nat) := TM2.Cfg (fun _ : Stack q => Bool) (Label q) Control

def run {q : Nat} (t : Nat) (c : Config q) := ((advance (program (q := q)))^[t]) c

theorem run_add {q : Nat} (t u : Nat) (c : Config q) :
    run (t + u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance (program (q := q))) u t c

theorem run_one {q : Nat} (c : Config q) : run 1 c = advance program c := rfl

theorem initial_bank {q : Nat} (i : Fin q) (query : Fin q → List Bool)
    (cap : List Bool) :
    bank (select i) (startBank query cap)
      (SourceCSPQueryRange.contents (query i) cap [] [] [] []) =
      startBank query cap := by
  apply bank_eq_self
  intro k
  fin_cases k <;> rfl

/-- One selected query call in an arbitrary foreign bank. Only the six
selected stacks need the literal initial contents; all other stacks are
preserved by the actual stack embedding. -/
theorem one_query_framed {q : Nat} (i : Fin q) (word cap : List Bool)
    (S : Stack q → List Bool)
    (hS : ∀ k : SourceCSPQueryRange.Stack,
      S (select i k) = SourceCSPQueryRange.contents word cap [] [] [] [] k) :
    ∃ t d, t ≤ 2 * word.length + 2 + (2 * cap.length + 2) + 1 +
          (cap.length + 1) * (4 * word.length + 5) + 1 ∧
      run t (⟨some (.check i (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
          (((none, none), (none, false)), none), S⟩ : Config q) =
        BitMachineStackEmbedding.cfg (select i) S (Label.check i)
          (fun v : SourceCSPQueryRange.Control => (v, (none : Option Bool)))
          (some (Label.after i)) d ∧
      d.l = none ∧ d.stk 0 = word ∧ d.stk 1 = cap ∧ d.stk 4 = [] ∧
      d.stk 5 = ProtocolBoundedUnary.result word cap [] := by
  obtain ⟨u, d, hu, hd, hh, hq, hc, hs, ho⟩ :=
    SourceCSPQueryRange.range_run word cap []
  have he := BitMachineStackEmbedding.outputs (select i) S
    (Label.check i) (fun v : SourceCSPQueryRange.Control =>
      (v, (none : Option Bool))) Prod.fst (fun _ => rfl)
    (some (Label.after i)) SourceCSPQueryRange.program program (fun _ => rfl)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
      ((none, none), (none, false)),
      SourceCSPQueryRange.contents word cap [] [] [] []⟩ :
      SourceCSPQueryRange.Config) u
  rw [hd] at he
  obtain ⟨t, ht, hr⟩ := he hh
  have hstart : BitMachineStackEmbedding.cfg (select i) S
      (Label.check i) (fun v : SourceCSPQueryRange.Control =>
        (v, (none : Option Bool))) (some (Label.after i))
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
        ((none, none), (none, false)),
        SourceCSPQueryRange.contents word cap [] [] [] []⟩ :
        SourceCSPQueryRange.Config) =
      (⟨some (.check i (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        (((none, none), (none, false)), none), S⟩ : Config q) := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
      BitMachineInline.cfg
    rw [bank_eq_self _ _ _ (fun k => (hS k).symm)]
  rw [hstart] at hr
  exact ⟨t, d, ht.trans hu, hr, hh, hq, hc, hs, ho⟩

def start {q : Nat} (i : Fin q) (query : Fin q → List Bool)
    (cap : List Bool) : Config q :=
  ⟨some (.check i (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
    (((none, none), (none, false)), none), startBank query cap⟩

/-- The selected physical call reaches its continuation with the original
binary query and cap intact and an exact status-plus-unary output. -/
theorem one_query_run {q : Nat} (i : Fin q) (query : Fin q → List Bool)
    (cap : List Bool) :
    ∃ t c, t ≤ 2 * (query i).length + 2 + (2 * cap.length + 2) + 1 +
          (cap.length + 1) * (4 * (query i).length + 5) + 1 ∧
      run t (start i query cap) = c ∧ c.l = some (.after i) ∧
      c.stk (.inl (i, 0)) = query i ∧ c.stk (.inr 0) = cap ∧
      c.stk (.inl (i, 4)) = [] ∧
      c.stk (.inl (i, 1)) = ProtocolBoundedUnary.result (query i) cap [] := by
  obtain ⟨u, d, hu, hd, hh, hq, hc, hs, ho⟩ :=
    SourceCSPQueryRange.range_run (query i) cap []
  have he := BitMachineStackEmbedding.outputs (select i) (startBank query cap)
    (.check i) (fun v => (v, none)) Prod.fst (fun _ => rfl)
    (some (.after i)) SourceCSPQueryRange.program program (fun _ => rfl)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
      ((none, none), (none, false)),
      SourceCSPQueryRange.contents (query i) cap [] [] [] []⟩ :
      SourceCSPQueryRange.Config) u
  rw [hd] at he
  obtain ⟨t, ht, hr⟩ := he hh
  let c := BitMachineStackEmbedding.cfg (select i) (startBank query cap)
    (Label.check i) (fun v : SourceCSPQueryRange.Control => (v, (none : Option Bool)))
    (some (Label.after i)) d
  have hstart : BitMachineStackEmbedding.cfg (select i) (startBank query cap)
      (.check i) (fun v => (v, none)) (some (.after i))
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
        ((none, none), (none, false)),
        SourceCSPQueryRange.contents (query i) cap [] [] [] []⟩ :
        SourceCSPQueryRange.Config) = start i query cap := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
      BitMachineInline.cfg start
    rw [initial_bank]
  rw [hstart] at hr
  refine ⟨t, c, ht.trans hu, hr, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [c, BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hh, Option.map_none]
  · change bank (select i) (startBank query cap) d.stk (select i 0) = _
    rw [bank_at]
    exact hq
  · change bank (select i) (startBank query cap) d.stk (select i 1) = _
    rw [bank_at]
    exact hc
  · change bank (select i) (startBank query cap) d.stk (select i 4) = _
    rw [bank_at]
    exact hs
  · change bank (select i) (startBank query cap) d.stk (select i 5) = _
    rw [bank_at]
    exact ho

theorem start_step {q : Nat} (i : Fin (q + 1)) (hi : i.val < q)
    (v : Control) (S : Stack q → List Bool) :
    advance program (⟨some (.start i), v, S⟩ : Config q) =
      ⟨some (.check ⟨i.val, hi⟩
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        (((none, none), (none, false)), none), S⟩ := by
  simp only [advance, TM2.step, program, hi, ↓reduceDIte,
    TM2.stepAux, Option.getD_some]

theorem after_success {q : Nat} (i : Fin q) (v : Control)
    (S : Stack q → List Bool) (unary : List Bool)
    (h : S (.inl (i, 1)) = true :: unary) :
    advance program (⟨some (.after i), v, S⟩ : Config q) =
      ⟨some (.start ⟨i.val + 1, by omega⟩), (v.1, some true),
        Function.update S (.inl (i, 1)) unary⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, h,
    List.head?_cons, Option.getD_some, cond_true, List.tail_cons]

theorem after_failure {q : Nat} (i : Fin q) (v : Control)
    (S : Stack q → List Bool) (unary : List Bool)
    (h : S (.inl (i, 1)) = false :: unary) :
    advance program (⟨some (.after i), v, S⟩ : Config q) =
      ⟨none, (v.1, some false),
        Function.update
          (Function.update S (.inl (i, 1)) unary) (.inr 1)
          (false :: S (.inr 1))⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, h,
    List.head?_cons, Option.getD_some, cond_false, List.tail_cons,
    Function.update_of_ne (by simp : (.inr (1 : Fin 2) : Stack q) ≠ .inl (i, 1))]

theorem finish_step {q : Nat} (v : Control) (S : Stack q → List Bool) :
    advance program (⟨some (.start (Fin.last q)), v, S⟩ : Config q) =
      ⟨none, v, Function.update S (.inr 1) (true :: S (.inr 1))⟩ := by
  simp only [advance, TM2.step, program, Fin.val_last,
    lt_self_iff_false, ↓reduceDIte, TM2.stepAux, Option.getD_some]

end EthInapproximability.CurrentPaper.SourceCSPQueryBank
