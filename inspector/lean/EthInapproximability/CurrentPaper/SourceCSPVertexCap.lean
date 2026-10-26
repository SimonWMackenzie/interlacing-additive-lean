import EthInapproximability.CurrentPaper.SourceCSPQueryRange
import EthInapproximability.CurrentPaper.BitMachineInline

/-!
# Physical bounded vertex-count guard and unary range cap

The original binary vertex count is compared against a supplied unary budget
(`q*m` in the enclosing converter). Only after bounded conversion does this
controller subtract one unary cell. Thus the zero-vertex case is rejected
before any query is tested against an `n-1` cap.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPVertexCap

open Turing BitMachineEncoding

inductive Label where
  | check : SourceCSPQueryRange.Label → Label
  | after
  | nonzero
  deriving DecidableEq, Fintype

abbrev Control := SourceCSPQueryRange.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 6 => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Fin 6 => Bool) Label Control
  | .check l => BitMachineInline.stmt .check (fun v => (v, none)) Prod.fst
      (some .after) (SourceCSPQueryRange.program l)
  | .after =>
      .pop 5 (fun v b => (v.1, b))
        (.branch (fun v => v.2.getD false)
          (.goto (fun _ => .nonzero))
          (.push 5 (fun _ => false) .halt))
  | .nonzero =>
      .pop 5 (fun v b => (v.1, b))
        (.branch (fun v => v.2.isSome)
          (.push 5 (fun _ => true) .halt)
          (.push 5 (fun _ => false) .halt))

def run (t : Nat) (c : Config) := ((advance program)^[t]) c

theorem run_one (c : Config) : run 1 c = advance program c := rfl

theorem run_add (t u : Nat) (c : Config) :
    run (t + u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance program) u t c

theorem after_success (v : Control) (S : Fin 6 → List Bool) (unary : List Bool)
    (h : S 5 = true :: unary) :
    advance program (⟨some .after, v, S⟩ : Config) =
      ⟨some .nonzero, (v.1, some true), Function.update S 5 unary⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, h,
    List.head?_cons, Option.getD_some, cond_true, List.tail_cons]

theorem after_failure (v : Control) (S : Fin 6 → List Bool) (unary : List Bool)
    (h : S 5 = false :: unary) :
    advance program (⟨some .after, v, S⟩ : Config) =
      ⟨none, (v.1, some false), Function.update S 5 (false :: unary)⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, h,
    List.head?_cons, Option.getD_some, cond_false, List.tail_cons,
    Function.update_idem, Function.update_self]

theorem nonzero_positive (v : Control) (S : Fin 6 → List Bool)
    (b : Bool) (tail : List Bool) (h : S 5 = b :: tail) :
    advance program (⟨some .nonzero, v, S⟩ : Config) =
      ⟨none, (v.1, some b), Function.update S 5 (true :: tail)⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, h,
    List.head?_cons, Option.isSome_some, cond_true, List.tail_cons,
    Function.update_idem, Function.update_self, Option.getD_some]

theorem nonzero_zero (v : Control) (S : Fin 6 → List Bool) (h : S 5 = []) :
    advance program (⟨some .nonzero, v, S⟩ : Config) =
      ⟨none, (v.1, none), Function.update S 5 [false]⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, h,
    List.head?_nil, Option.isSome_none, cond_false, List.tail_nil,
    Function.update_idem, Function.update_self, Option.getD_some]

/-- The bounded converter is physically inlined, with the exact original
binary vertex word and supplied unary size budget preserved. -/
theorem checked (word budget : List Bool) :
    ∃ t c, t ≤ 2 * word.length + 2 + (2 * budget.length + 2) + 1 +
          (budget.length + 1) * (4 * word.length + 5) + 1 ∧
      run t (⟨some (.check (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        (((none, none), (none, false)), none),
        SourceCSPQueryRange.contents word budget [] [] [] []⟩ : Config) = c ∧
      c.l = some .after ∧ c.stk 0 = word ∧ c.stk 1 = budget ∧
      c.stk 5 = ProtocolBoundedUnary.result word budget [] := by
  obtain ⟨t, d, ht, hr, hh, hw, hb, hs, ho⟩ :=
    SourceCSPQueryRange.range_run word budget []
  obtain ⟨u, hu, hrun⟩ := BitMachineInline.outputs Label.check
    (fun v => (v, (none : Option Bool))) Prod.fst (fun _ => rfl)
    (some Label.after) SourceCSPQueryRange.program program (fun _ => rfl)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
      ((none, none), (none, false)),
      SourceCSPQueryRange.contents word budget [] [] [] []⟩ :
      SourceCSPQueryRange.Config) t (by rw [hr, hh])
  rw [hr] at hrun
  let c : Config := BitMachineInline.cfg Label.check
    (fun v => (v, (none : Option Bool)))
    (some Label.after) d
  refine ⟨u, c, hu.trans ht, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [run, BitMachineInline.cfg] using hrun
  · simp only [c, BitMachineInline.cfg, hh]
  · exact hw
  · exact hb
  · exact ho

theorem positive_run (n : Nat) (budget : List Bool) (hn : 0 < n)
    (hbound : n ≤ budget.length) :
    ∃ t c, t ≤ 2 * n.bits.length + 2 +
          (2 * budget.length + 2) + 1 +
          (budget.length + 1) * (4 * n.bits.length + 5) + 3 ∧
      run t (⟨some (.check (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        (((none, none), (none, false)), none),
        SourceCSPQueryRange.contents n.bits budget [] [] [] []⟩ : Config) = c ∧
      c.l = none ∧ c.stk 0 = n.bits ∧ c.stk 1 = budget ∧
      c.stk 5 = true :: List.replicate (n - 1) true := by
  obtain ⟨t, c, ht, hr, hh, hw, hb, ho⟩ := checked n.bits budget
  have hresult : ProtocolBoundedUnary.result n.bits budget [] =
      true :: List.replicate n true := by
    simp [ProtocolBoundedUnary.result, hbound]
  have hout : c.stk 5 = true :: List.replicate n true := ho.trans hresult
  let S₁ := Function.update c.stk 5 (List.replicate n true)
  have hstep₁ : advance program (⟨some .after, c.var, c.stk⟩ : Config) =
      ⟨some .nonzero, (c.var.1, some true), S₁⟩ :=
    after_success c.var c.stk _ hout
  have hc : c = (⟨some .after, c.var, c.stk⟩ : Config) := by
    cases c with
    | mk l v S => simp only at hh ⊢; rw [hh]
  have hstep₁' : advance program c =
      ⟨some .nonzero, (c.var.1, some true), S₁⟩ := by
    rw [hc]
    exact hstep₁
  have hnrep : List.replicate n true = true :: List.replicate (n - 1) true := by
    cases n with
    | zero => omega
    | succ k => rfl
  have hS₁ : S₁ 5 = true :: List.replicate (n - 1) true := by
    change Function.update c.stk 5 (List.replicate n true) 5 = _
    rw [Function.update_self, hnrep]
  let S₂ := Function.update S₁ 5 (true :: List.replicate (n - 1) true)
  have hstep₂ : advance program (⟨some .nonzero, (c.var.1, some true), S₁⟩ : Config) =
      ⟨none, (c.var.1, some true), S₂⟩ := by
    simpa only [S₂] using nonzero_positive (c.var.1, some true) S₁ true _ hS₁
  refine ⟨t + 2, ⟨none, (c.var.1, some true), S₂⟩, by omega, ?_, rfl, ?_, ?_, ?_⟩
  · rw [show t + 2 = t + 1 + 1 by omega, run_add, run_add,
      hr, run_one, run_one, hstep₁', hstep₂]
  · change S₂ 0 = n.bits
    simp only [S₂, S₁, Function.update_of_ne (by decide : (0 : Fin 6) ≠ 5)]
    exact hw
  · change S₂ 1 = budget
    simp only [S₂, S₁, Function.update_of_ne (by decide : (1 : Fin 6) ≠ 5)]
    exact hb
  · change S₂ 5 = _
    exact Function.update_self _ _ _

theorem oversized_run (word budget : List Bool)
    (hbad : ¬ EncodedCommunication.bitsValue word ≤ budget.length) :
    ∃ t c, t ≤ 2 * word.length + 2 + (2 * budget.length + 2) + 1 +
          (budget.length + 1) * (4 * word.length + 5) + 2 ∧
      run t (⟨some (.check (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        (((none, none), (none, false)), none),
        SourceCSPQueryRange.contents word budget [] [] [] []⟩ : Config) = c ∧
      c.l = none ∧ c.stk 5 = false :: List.replicate budget.length true := by
  obtain ⟨t, c, ht, hr, hh, hw, hb, ho⟩ := checked word budget
  have hresult : ProtocolBoundedUnary.result word budget [] =
      false :: List.replicate budget.length true := by
    have hle : budget.length ≤ EncodedCommunication.bitsValue word := by omega
    simp [ProtocolBoundedUnary.result, hbad, hle]
  have hout := ho.trans hresult
  have hc : c = (⟨some .after, c.var, c.stk⟩ : Config) := by
    cases c with
    | mk l v S => simp only at hh ⊢; rw [hh]
  let S := Function.update c.stk 5 (false :: List.replicate budget.length true)
  refine ⟨t + 1, ⟨none, (c.var.1, some false), S⟩, by omega, ?_, rfl, ?_⟩
  · rw [run_add, hr, run_one]
    rw [hc]
    simpa only [S] using after_failure c.var c.stk _ hout
  · change S 5 = _
    exact Function.update_self _ _ _

theorem zero_run (budget : List Bool) :
    ∃ t c, t ≤ 2 * (0 : Nat).bits.length + 2 +
          (2 * budget.length + 2) + 1 +
          (budget.length + 1) * (4 * (0 : Nat).bits.length + 5) + 3 ∧
      run t (⟨some (.check (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        (((none, none), (none, false)), none),
        SourceCSPQueryRange.contents (0 : Nat).bits budget [] [] [] []⟩ : Config) = c ∧
      c.l = none ∧ c.stk 5 = [false] := by
  obtain ⟨t, c, ht, hr, hh, hw, hb, ho⟩ := checked (0 : Nat).bits budget
  have hresult : ProtocolBoundedUnary.result (0 : Nat).bits budget [] = [true] := by
    simp [ProtocolBoundedUnary.result, EncodedCommunication.bitsValue]
  have hout := ho.trans hresult
  have hc : c = (⟨some .after, c.var, c.stk⟩ : Config) := by
    cases c with
    | mk l v S => simp only at hh ⊢; rw [hh]
  let S₁ := Function.update c.stk 5 []
  have hs₁ : S₁ 5 = [] := Function.update_self _ _ _
  let S₂ := Function.update S₁ 5 [false]
  refine ⟨t + 2, ⟨none, (c.var.1, none), S₂⟩, by omega, ?_, rfl, ?_⟩
  · rw [show t + 2 = t + 1 + 1 by omega, run_add, run_add,
      hr, run_one, run_one, hc, after_success c.var c.stk [] hout,
      nonzero_zero (c.var.1, some true) S₁ hs₁]
  · change S₂ 5 = _
    exact Function.update_self _ _ _

/-- Every binary vertex word halts under the supplied unary size budget.
The success path produces exactly `n-1` unary cells; both zero and oversized
counts receive a leading `false` instead. -/
theorem guard_total (n : Nat) (budget : List Bool) :
    ∃ t c, t ≤ 2 * n.bits.length + 2 +
          (2 * budget.length + 2) + 1 +
          (budget.length + 1) * (4 * n.bits.length + 5) + 3 ∧
      run t (⟨some (.check (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        (((none, none), (none, false)), none),
        SourceCSPQueryRange.contents n.bits budget [] [] [] []⟩ : Config) = c ∧
      c.l = none ∧
      (c.stk 5).head? = some (decide (0 < n ∧ n ≤ budget.length)) ∧
      (0 < n ∧ n ≤ budget.length →
        c.stk 5 = true :: List.replicate (n - 1) true) := by
  by_cases hn : 0 < n
  · by_cases hb : n ≤ budget.length
    · obtain ⟨t, c, ht, hr, hh, hw, hbudget, hout⟩ :=
        positive_run n budget hn hb
      refine ⟨t, c, ht, hr, hh, ?_, ?_⟩
      · rw [hout]
        simp [hn, hb]
      · intro _
        exact hout
    · have hbad : ¬ EncodedCommunication.bitsValue n.bits ≤ budget.length := by
        simpa only [EncodedCommunication.bitsValue_bits] using hb
      obtain ⟨t, c, ht, hr, hh, hout⟩ := oversized_run n.bits budget hbad
      refine ⟨t, c, by omega, hr, hh, ?_, ?_⟩
      · rw [hout]
        simp [hb]
      · intro h
        exact False.elim (hb h.2)
  · have hz : n = 0 := by omega
    subst n
    obtain ⟨t, c, ht, hr, hh, hout⟩ := zero_run budget
    refine ⟨t, c, ht, hr, hh, ?_, ?_⟩
    · rw [hout]
      simp
    · intro h
      omega

end EthInapproximability.CurrentPaper.SourceCSPVertexCap
