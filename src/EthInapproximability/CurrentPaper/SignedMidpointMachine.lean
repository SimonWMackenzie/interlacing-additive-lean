import EthInapproximability.CurrentPaper.SignedMidpointPreparation
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# A framed signed midpoint comparator

Source: frozen v8 `06-eth.tex`, proof of `thm:main`. The answer word and
unary cap are physically present on separate Boolean stacks. The signed
field preparation and bounded binary comparison are inlined as finite tables.
The strict comparison pops exactly one cap cell; the bounded converter's
unary residue is then erased before a single decision bit is returned.

The source reduction must still compute and supply the cap `2Y+k` and frame
the approximation machine's output. This module never treats either as free.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointMachine

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Outer where
  | afterPrep | afterBound | clear
  deriving DecidableEq, Fintype

abbrev Label := SignedMidpointPreparation.Label ⊕ (ProtocolBoundedUnary.Label ⊕ Outer)
abbrev Control := SignedMidpointPreparation.Control ×
  (ProtocolBoundedUnary.Control × (Option Bool × Option Bool))
abbrev Stack := Fin 5
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Label Control

def outer (l : Outer) : Label := .inr (.inr l)
def decision (v : Control) : Option Bool := v.2.2.1
def popped (v : Control) : Option Bool := v.2.2.2
def setDecision (v : Control) (b : Option Bool) : Control :=
  (v.1, v.2.1, b, v.2.2.2)
def setPopped (v : Control) (b : Option Bool) : Control :=
  (v.1, v.2.1, v.2.2.1, b)

/-- Bounded converter stacks map to prepared magnitude, cap, scratch and
output, respectively. The signed-word remainder on stack 0 is foreign. -/
def boundStack : Fin 4 ↪ Stack :=
  ⟨![3, 1, 2, 4], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

def program : Label → Statement
  | .inl l => BitMachineInline.stmt Sum.inl
      (fun v => (v, (none, false), none, none)) Prod.fst
      (some (outer .afterPrep)) (SignedMidpointPreparation.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt boundStack
      (fun l => .inr (.inl l))
      (fun v => (none, v, none, none)) (fun v => v.2.1)
      (some (outer .afterBound)) (ProtocolBoundedUnary.program l)
  | .inr (.inr .afterPrep) =>
      pop 4 setDecision
        (branch (fun v => (decision v).isSome)
          (push 4 (fun v => (decision v).getD false) halt)
          (pop 1 setDecision
            (branch (fun v => (decision v).isSome)
              (load (fun v => (v.1, (none, false), none, none))
                (goto (fun _ => .inr (.inl .zeroScan))))
              (push 4 (fun _ => false) halt))))
  | .inr (.inr .afterBound) => pop 4 setDecision (goto (fun _ => outer .clear))
  | .inr (.inr .clear) =>
      pop 4 setPopped
        (branch (fun v => (popped v).isSome)
          (goto (fun _ => outer .clear))
          (push 4 (fun v => (decision v).getD false) halt))

def cfg (l : Option Label) (v : Control)
    (answer cap scratch magnitude out : List Bool) : Config :=
  ⟨l, v, ![answer, cap, scratch, magnitude, out]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

theorem run_succ (t : ℕ) (c : Config) : run (t + 1) c = run t (advance program c) := by
  exact Function.iterate_succ_apply _ _ _

theorem run_add (t u : ℕ) (c : Config) : run (t + u) c = run u (run t c) := by
  simp only [run, Nat.add_comm t u, Function.iterate_add_apply]

abbrev PrepConfig := SignedMidpointPreparation.Config

def prepFrame (c : PrepConfig) : Config :=
  BitMachineInline.cfg Sum.inl
    (fun v => (v, (none, false), none, none)) (some (outer .afterPrep)) c

theorem prepFrame_start (answer cap : List Bool) :
    prepFrame (SignedMidpointPreparation.cfg (some .sign) none answer cap [] [] []) =
      cfg (some (.inl .sign)) (none, (none, false), none, none) answer cap [] [] [] := rfl

theorem prepFrame_halted (c : PrepConfig) (hc : c.l = none) :
    prepFrame c = cfg (some (outer .afterPrep)) (c.var, (none, false), none, none)
      (c.stk 0) (c.stk 1) (c.stk 2) (c.stk 3) (c.stk 4) := by
  cases c with
  | mk l v S =>
      cases l with
      | none =>
          unfold prepFrame BitMachineInline.cfg cfg
          congr 1
          funext k; fin_cases k <;> rfl
      | some l => simp at hc

theorem prep_run (answer cap : List Bool) :
    ∃ t ≤ 3 * answer.length + 3, ∃ c : PrepConfig,
      run t (cfg (some (.inl .sign)) (none, (none, false), none, none)
        answer cap [] [] []) = prepFrame c ∧ c.l = none := by
  obtain ⟨t, ht, hc⟩ := SignedMidpointPreparation.total answer cap
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs Sum.inl
    (fun v => (v, (none, false), none, none)) Prod.fst (fun _ => rfl)
    (some (outer .afterPrep)) SignedMidpointPreparation.program program
    (fun _ => rfl)
    (SignedMidpointPreparation.cfg (some .sign) none answer cap [] [] []) t hc
  refine ⟨u, hu.trans ht, SignedMidpointPreparation.run t
    (SignedMidpointPreparation.cfg (some .sign) none answer cap [] [] []), ?_, hc⟩
  change run u (prepFrame _) = prepFrame _ at hr
  rwa [prepFrame_start] at hr

theorem prep_exact_run (answer cap : List Bool) (t : ℕ) (c : PrepConfig)
    (h : SignedMidpointPreparation.run t
      (SignedMidpointPreparation.cfg (some .sign) none answer cap [] [] []) = c)
    (hc : c.l = none) :
    ∃ u ≤ t,
      run u (cfg (some (.inl .sign)) (none, (none, false), none, none)
        answer cap [] [] []) = prepFrame c := by
  have hh : (SignedMidpointPreparation.run t
      (SignedMidpointPreparation.cfg (some .sign) none answer cap [] [] [])).l = none := by
    rw [h]; exact hc
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs Sum.inl
    (fun v => (v, (none, false), none, none)) Prod.fst (fun _ => rfl)
    (some (outer .afterPrep)) SignedMidpointPreparation.program program
    (fun _ => rfl)
    (SignedMidpointPreparation.cfg (some .sign) none answer cap [] [] []) t hh
  refine ⟨u, hu, ?_⟩
  change run u (prepFrame _) = prepFrame _ at hr
  rw [prepFrame_start] at hr
  change ((advance SignedMidpointPreparation.program)^[t])
    (SignedMidpointPreparation.cfg (some .sign) none answer cap [] [] []) = c at h
  rw [h] at hr
  exact hr

theorem prep_nonnegative (n : ℕ) (cap : List Bool) :
    ∃ t ≤ 3 * n.bits.length + 3,
      run t (cfg (some (.inl .sign)) (none, (none, false), none, none)
        (EncodedETHTail.encodeInteger (n : ℤ)) cap [] [] []) =
      cfg (some (outer .afterPrep)) (none, (none, false), none, none)
        [] cap [] (false :: n.bits) [] := by
  obtain ⟨u, hu, he⟩ := prep_exact_run _ cap _ _
    (SignedMidpointPreparation.encoded_nonnegative_run n cap) rfl
  refine ⟨u, hu, ?_⟩
  rw [he]
  exact prepFrame_halted _ rfl

theorem prep_negative (n : ℕ) (cap : List Bool) :
    ∃ t ≤ 1,
      run t (cfg (some (.inl .sign)) (none, (none, false), none, none)
        (EncodedETHTail.encodeInteger (Int.negSucc n)) cap [] [] []) =
      cfg (some (outer .afterPrep)) (some true, (none, false), none, none)
        (EncodedCommunication.natField (n + 1)) cap [] [] [true] := by
  obtain ⟨u, hu, he⟩ := prep_exact_run _ cap _ _
    (SignedMidpointPreparation.encoded_negative_run n cap) rfl
  refine ⟨u, hu, ?_⟩
  rw [he]
  exact prepFrame_halted _ rfl

theorem afterPrep_negative (answer cap : List Bool) :
    advance program (cfg (some (outer .afterPrep))
      (some true, (none, false), none, none) answer cap [] [] [true]) =
      cfg none (some true, (none, false), some true, none) answer cap [] [] [true] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, outer,
    decision, setDecision]

theorem afterPrep_empty_cap (answer magnitude : List Bool) :
    advance program (cfg (some (outer .afterPrep))
      (none, (none, false), none, none) answer [] [] magnitude []) =
      cfg none (none, (none, false), none, none) answer [] [] magnitude [false] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, outer,
    decision, setDecision]
  funext k; fin_cases k <;> rfl

theorem afterPrep_positive (answer magnitude cap : List Bool) (b : Bool) :
    advance program (cfg (some (outer .afterPrep))
      (none, (none, false), none, none) answer (b :: cap) [] magnitude []) =
      cfg (some (.inr (.inl .zeroScan)))
        (none, (none, false), none, none) answer cap [] magnitude [] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, outer,
    decision, setDecision]
  funext k; fin_cases k <;> rfl

theorem afterBound_step (answer cap scratch magnitude : List Bool)
    (v : ProtocolBoundedUnary.Control) (flag : Bool) (residue : List Bool) :
    advance program (cfg (some (outer .afterBound))
      (none, v, none, none) answer cap scratch magnitude (flag :: residue)) =
      cfg (some (outer .clear)) (none, v, some flag, none)
        answer cap scratch magnitude residue := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, outer,
    decision, setDecision]
  funext k; fin_cases k <;> rfl

theorem clear_cons (answer cap scratch magnitude : List Bool)
    (v : Control) (b : Bool) (residue : List Bool) :
    advance program (cfg (some (outer .clear)) v
      answer cap scratch magnitude (b :: residue)) =
      cfg (some (outer .clear)) (setPopped v (some b))
        answer cap scratch magnitude residue := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, outer,
    decision, popped, setPopped]
  funext k; fin_cases k <;> rfl

theorem clear_nil (answer cap scratch magnitude : List Bool) (v : Control) :
    advance program (cfg (some (outer .clear)) v
      answer cap scratch magnitude []) =
      cfg none (setPopped v none)
        answer cap scratch magnitude [(decision v).getD false] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, outer,
    decision, popped, setPopped]
  funext k; fin_cases k <;> rfl

theorem clear_run (answer cap scratch magnitude residue : List Bool) (v : Control) :
    run (residue.length + 1)
      (cfg (some (outer .clear)) v answer cap scratch magnitude residue) =
      cfg none (setPopped v none)
        answer cap scratch magnitude [(decision v).getD false] := by
  induction residue generalizing v with
  | nil => simpa [run] using clear_nil answer cap scratch magnitude v
  | cons b residue ih =>
      rw [List.length_cons, run_succ, clear_cons, ih]
      rfl

abbrev BoundConfig := TM2.Cfg (fun _ : Fin 4 => Bool)
  ProtocolBoundedUnary.Label ProtocolBoundedUnary.Control

def boundForeign (answer : List Bool) : Stack → List Bool :=
  fun k => if k = 0 then answer else []

noncomputable def boundFrame (answer : List Bool) (c : BoundConfig) : Config :=
  BitMachineStackEmbedding.cfg boundStack (boundForeign answer)
    (fun l => .inr (.inl l)) (fun v => (none, v, none, none))
    (some (outer .afterBound)) c

theorem boundBank (answer : List Bool) (S : Fin 4 → List Bool) :
    BitMachineStackEmbedding.bank boundStack (boundForeign answer) S =
      ![answer, S 1, S 2, S 0, S 3] := by
  funext k
  fin_cases k
  · have h : ¬ ∃ i : Fin 4, boundStack i = (0 : Stack) := by decide
    simpa [boundForeign] using
      (BitMachineStackEmbedding.bank_outside boundStack (boundForeign answer) S 0 h)
  · simpa only [boundStack, Matrix.cons_val_one] using
      (BitMachineStackEmbedding.bank_at boundStack (boundForeign answer) S (1 : Fin 4))
  · simpa only [boundStack, Matrix.cons_val_two] using
      (BitMachineStackEmbedding.bank_at boundStack (boundForeign answer) S (2 : Fin 4))
  · simpa only [boundStack, Matrix.cons_val_three] using
      (BitMachineStackEmbedding.bank_at boundStack (boundForeign answer) S (0 : Fin 4))
  · simpa only [boundStack, Matrix.cons_val_four] using
      (BitMachineStackEmbedding.bank_at boundStack (boundForeign answer) S (3 : Fin 4))

theorem boundFrame_initial (answer q cap : List Bool) :
    boundFrame answer (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false)
      q cap [] []) =
      cfg (some (.inr (.inl .zeroScan))) (none, (none, false), none, none)
        answer cap [] q [] := by
  unfold boundFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  rw [boundBank]
  rfl

theorem boundFrame_halted (answer : List Bool) (c : BoundConfig) (hc : c.l = none) :
    boundFrame answer c =
      cfg (some (outer .afterBound)) (none, c.var, none, none)
        answer (c.stk 1) (c.stk 2) (c.stk 0) (c.stk 3) := by
  unfold boundFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  rw [hc, boundBank]
  rfl

/-- The fixed bounded converter is actually executed on the prepared bank;
the foreign signed-word remainder is preserved. -/
theorem bounded_run (answer q cap : List Bool) :
    ∃ t ≤ (cap.length + 1) * (4 * q.length + 5), ∃ c : BoundConfig,
      run t (cfg (some (.inr (.inl .zeroScan)))
        (none, (none, false), none, none) answer cap [] q []) =
        cfg (some (outer .afterBound)) (none, c.var, none, none)
          answer (c.stk 1) (c.stk 2) (c.stk 0) (c.stk 3) ∧
      c.l = none ∧ c.stk 3 = ProtocolBoundedUnary.result q cap [] ∧
      (c.stk 1).length ≤ cap.length := by
  obtain ⟨t, c, ht, he, hc, ho, _, _, hcap⟩ :=
    ProtocolBoundedUnary.bounded_run_framed q cap []
  have hh : (ProtocolBoundedUnary.run t
      (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false) q cap [] [])).l = none := by
    rw [he]; exact hc
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs boundStack (boundForeign answer)
    (fun l => .inr (.inl l)) (fun v => (none, v, none, none)) (fun v => v.2.1)
    (fun _ => rfl) (some (outer .afterBound))
    ProtocolBoundedUnary.program program (fun _ => rfl)
    (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false) q cap [] []) t hh
  refine ⟨u, hu.trans ht, c, ?_, hc, ho, hcap⟩
  change run u (boundFrame answer _) = boundFrame answer _ at hr
  rw [boundFrame_initial] at hr
  change ((advance ProtocolBoundedUnary.program)^[t])
    (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false) q cap [] []) = c at he
  rw [he] at hr
  rwa [boundFrame_halted answer c hc] at hr

/-- On a positive canonical signed word, the local phase returns exactly one
bit. The unary cap cell removed before conversion implements the strict
midpoint, including the zero-cap case. -/
theorem positive_local (n : ℕ) (b : Bool) (cap : List Bool) :
    ∃ t ≤ 1 + (cap.length + 1) * (4 * (false :: n.bits).length + 5) +
        1 + (cap.length + 1),
      let c := run t (cfg (some (outer .afterPrep))
        (none, (none, false), none, none) [] (b :: cap) [] (false :: n.bits) [])
      c.l = none ∧ c.stk 4 =
        [decide (2 * (n : ℤ) < ((b :: cap).length : ℤ))] := by
  obtain ⟨tb, htb, c, hb, hc, hout, hcap⟩ :=
    bounded_run [] (false :: n.bits) cap
  let residue := List.replicate (min (2 * n) cap.length) true
  let flag := decide (2 * n ≤ cap.length)
  have hv : EncodedCommunication.bitsValue (false :: n.bits) = 2 * n := by
    simp [EncodedCommunication.bitsValue, Nat.bit_val]
  have hresult : c.stk 3 = flag :: residue := by
    simpa [ProtocolBoundedUnary.result, flag, residue, hv] using hout
  have hflag : flag = decide (2 * (n : ℤ) < ((b :: cap).length : ℤ)) := by
    have heq : (2 * n ≤ cap.length) =
        (2 * (n : ℤ) < ((b :: cap).length : ℤ)) := by
      apply propext
      simp only [List.length_cons]
      omega
    simp only [flag, ← heq]
  let start := cfg (some (outer .afterPrep))
    (none, (none, false), none, none) [] (b :: cap) [] (false :: n.bits) []
  let entered := cfg (some (.inr (.inl .zeroScan)))
    (none, (none, false), none, none) [] cap [] (false :: n.bits) []
  let returned := cfg (some (outer .afterBound))
    (none, c.var, none, none) [] (c.stk 1) (c.stk 2) (c.stk 0) (c.stk 3)
  let clearing := cfg (some (outer .clear))
    (none, c.var, some flag, none) [] (c.stk 1) (c.stk 2) (c.stk 0) residue
  have henter : advance program start = entered := by
    exact afterPrep_positive [] (false :: n.bits) cap b
  have hreturn : run tb entered = returned := hb
  have hclear : advance program returned = clearing := by
    dsimp only [returned, clearing]
    rw [hresult]
    exact afterBound_step [] (c.stk 1) (c.stk 2) (c.stk 0) c.var flag residue
  have hfinish := clear_run [] (c.stk 1) (c.stk 2) (c.stk 0) residue
    (none, c.var, some flag, none)
  have hfinal : run (1 + tb + 1 + (residue.length + 1)) start =
      cfg none (setPopped (none, c.var, some flag, none) none)
        [] (c.stk 1) (c.stk 2) (c.stk 0) [flag] := by
    rw [show 1 + tb + 1 + (residue.length + 1) =
      (1 + tb + 1) + (residue.length + 1) by omega,
      run_add]
    have hmid : run (1 + tb + 1) start = clearing := by
      rw [show 1 + tb + 1 = (1 + tb) + 1 by omega,
        run_add, show run 1 (run (1 + tb) start) =
          advance program (run (1 + tb) start) by rfl]
      have hprev : run (1 + tb) start = returned := by
        rw [run_add]
        change run tb (advance program start) = returned
        rw [henter, hreturn]
      rw [hprev, hclear]
    rw [hmid]
    simpa [decision] using hfinish
  refine ⟨1 + tb + 1 + (residue.length + 1), ?_, ?_⟩
  · have hlen : residue.length ≤ cap.length := by simp [residue]
    omega
  · dsimp only
    rw [hfinal]
    constructor
    · rfl
    · change [flag] = [decide (2 * (n : ℤ) < ((b :: cap).length : ℤ))]
      rw [hflag]

theorem negative_canonical (n : ℕ) (cap : List Bool) :
    ∃ t ≤ 2,
      let c := run t (cfg (some (.inl .sign))
        (none, (none, false), none, none)
        (EncodedETHTail.encodeInteger (Int.negSucc n)) cap [] [] [])
      c.l = none ∧ c.stk 4 =
        [decide (2 * (Int.negSucc n) < (cap.length : ℤ))] := by
  obtain ⟨tp, htp, hp⟩ := prep_negative n cap
  refine ⟨tp + 1, by omega, ?_⟩
  dsimp only
  rw [run_add, hp]
  simp only [run, Function.iterate_one, afterPrep_negative]
  have hcmp : (2 * (Int.negSucc n) < (cap.length : ℤ)) := by omega
  simp [cfg, hcmp]

theorem nonnegative_canonical (n : ℕ) (cap : List Bool) :
    ∃ t ≤ 20 * ((EncodedETHTail.encodeInteger (n : ℤ)).length + 1) *
        (cap.length + 1),
      let c := run t (cfg (some (.inl .sign))
        (none, (none, false), none, none)
        (EncodedETHTail.encodeInteger (n : ℤ)) cap [] [] [])
      c.l = none ∧ c.stk 4 =
        [decide (2 * (n : ℤ) < (cap.length : ℤ))] := by
  obtain ⟨tp, htp, hp⟩ := prep_nonnegative n cap
  have hlen : (EncodedETHTail.encodeInteger (n : ℤ)).length =
      2 * n.bits.length + 2 := by
    have hn : ¬ ((n : ℤ) < 0) := not_lt_of_ge (Int.natCast_nonneg n)
    simp [EncodedETHTail.encodeInteger, EncodedCommunication.natField,
      hn, EncodedCommunication.field_length]
  cases cap with
  | nil =>
      refine ⟨tp + 1, ?_, ?_⟩
      · rw [hlen]
        simp only [List.length_nil, zero_add, Nat.mul_one]
        omega
      · dsimp only
        rw [run_add, hp]
        simp only [run, Function.iterate_one, afterPrep_empty_cap]
        have hcmp : ¬ 2 * (n : ℤ) < (0 : ℤ) := by omega
        simp [cfg, hcmp]
  | cons b rest =>
      obtain ⟨tl, htl, hl⟩ := positive_local n b rest
      refine ⟨tp + tl, ?_, ?_⟩
      · rw [hlen]
        simp only [List.length_cons] at htl ⊢
        nlinarith
      · dsimp only
        rw [run_add, hp]
        exact hl

end EthInapproximability.CurrentPaper.SignedMidpointMachine
