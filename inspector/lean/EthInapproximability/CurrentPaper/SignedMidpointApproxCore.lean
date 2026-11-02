import EthInapproximability.CurrentPaper.SignedMidpointCapCost
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Generic approximation callback with preserved midpoint parameters

For any actual finite Boolean-stack approximation machine `M`, the new
finite program runs `M` on its own stack bank while preserving four foreign
stacks (unary `Y`, unary `k`, scratch and decision). It then switches to the
fixed cap-construction/comparison program with `M`'s physical output stack
as the signed answer. No new approximation runtime premise is introduced.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointApproxCore

open Turing BitMachineEncoding

variable (M : BitMachine.Machine)

abbrev Stack := Fin M.stackCount ⊕ Fin 4
abbrev Label := Fin M.labelCount ⊕ (Unit ⊕ SignedMidpointCapCompare.Label)
abbrev Control := Fin M.controlCount × SignedMidpointCapCompare.Control
abbrev Config := TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)
abbrev Statement := TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)

def localStack : Fin M.stackCount ↪ Stack M :=
  ⟨Sum.inl, Sum.inl_injective⟩

def compareStack : Fin 5 ↪ Stack M :=
  ⟨![.inl M.output, .inr 0, .inr 1, .inr 2, .inr 3], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def initialCompare : SignedMidpointCapCompare.Control :=
  (none, SignedMidpointPacket.initial)

def program : Label M → Statement M
  | .inl l => BitMachineStackEmbedding.stmt (localStack M) Sum.inl
      (fun v => (v, initialCompare)) Prod.fst
      (some (.inr (.inl ()))) (M.program l)
  | .inr (.inl ()) => .load (fun _ => (M.initial, initialCompare))
      (.goto (fun _ => .inr (.inr (.inl .double))))
  | .inr (.inr l) => BitMachineStackEmbedding.stmt (compareStack M)
      (fun l => .inr (.inr l)) (fun v => (M.initial, v)) Prod.snd
      none (SignedMidpointCapCompare.program l)

def run (t : ℕ) (c : Config M) := ((advance (program M))^[t]) c

def foreign (Y k : ℕ) : Stack M → List Bool :=
  Sum.elim (fun _ => []) ![List.replicate Y true, List.replicate k true, [], []]

noncomputable def start (table : List Bool) (Y k : ℕ) : Config M :=
  BitMachineStackEmbedding.cfg (localStack M) (foreign M Y k) Sum.inl
    (fun v => (v, initialCompare)) (some (.inr (.inl ()))) (M.init table)

theorem local_prefix (table answer : List Bool) (Y k bound : ℕ)
    (hM : M.OutputsWithin table answer bound) :
    ∃ t ≤ bound,
      run M t (start M table Y k) =
        BitMachineStackEmbedding.cfg (localStack M) (foreign M Y k) Sum.inl
          (fun v => (v, initialCompare)) (some (.inr (.inl ())))
          (M.run bound (M.init table)) := by
  have hh := (BitMachine.outputsWithin_at_bound M hM).1
  obtain ⟨t,ht,hr⟩ := BitMachineStackEmbedding.outputs (localStack M)
    (foreign M Y k) Sum.inl (fun v => (v, initialCompare)) Prod.fst
    (by intro v; rfl) (some (.inr (.inl ()))) M.program (program M)
    (by intro l; rfl) (M.init table) bound hh
  exact ⟨t,ht,hr⟩

def afterApprox (v : Fin M.controlCount) (S : Stack M → List Bool) : Config M :=
  ⟨some (.inr (.inl ())), (v, initialCompare), S⟩

def compareStart (S : Stack M → List Bool) : Config M :=
  ⟨some (.inr (.inr (.inl .double))), (M.initial, initialCompare), S⟩

theorem reset_step (v : Fin M.controlCount) (S : Stack M → List Bool) :
    advance (program M) (afterApprox M v S) = compareStart M S := by
  rfl

noncomputable def afterBank (table : List Bool) (Y k bound : ℕ) :
    Stack M → List Bool :=
  BitMachineStackEmbedding.bank (localStack M) (foreign M Y k)
    (M.run bound (M.init table)).stk

theorem afterBank_answer (table answer : List Bool) (Y k bound : ℕ)
    (hM : M.OutputsWithin table answer bound) :
    afterBank M table Y k bound (compareStack M 0) = answer := by
  have ho := (BitMachine.outputsWithin_at_bound M hM).2
  change BitMachineStackEmbedding.bank (localStack M) (foreign M Y k)
    (M.run bound (M.init table)).stk ((localStack M) M.output) = answer
  rw [BitMachineStackEmbedding.bank_at]
  exact ho

theorem afterBank_parameters (table : List Bool) (Y k bound : ℕ) :
    afterBank M table Y k bound (compareStack M 1) = List.replicate Y true ∧
    afterBank M table Y k bound (compareStack M 2) = List.replicate k true ∧
    afterBank M table Y k bound (compareStack M 3) = [] ∧
    afterBank M table Y k bound (compareStack M 4) = [] := by
  have hout (j : Fin 4) :
      afterBank M table Y k bound (.inr j) = (foreign M Y k) (.inr j) := by
    apply BitMachineStackEmbedding.bank_outside
    intro h
    obtain ⟨x,hx⟩ := h
    cases hx
  refine ⟨?_,?_,?_,?_⟩
  · simpa [compareStack, foreign] using hout 0
  · simpa [compareStack, foreign] using hout 1
  · simpa [compareStack, foreign] using hout 2
  · simpa [compareStack, foreign] using hout 3

theorem afterBank_cap (table answer : List Bool) (Y k bound : ℕ)
    (hM : M.OutputsWithin table answer bound) :
    BitMachineStackEmbedding.bank (compareStack M)
      (afterBank M table Y k bound)
      (SignedMidpointCapCompare.inputBank answer Y k) =
        afterBank M table Y k bound := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro j
  have ha := afterBank_answer M table answer Y k bound hM
  have ⟨hY,hk,hs,ho⟩ := afterBank_parameters M table Y k bound
  fin_cases j <;> simp_all [SignedMidpointCapCompare.inputBank]

theorem local_endpoint (table answer : List Bool) (Y k bound : ℕ)
    (hM : M.OutputsWithin table answer bound) :
    ∃ t ≤ bound,
      run M t (start M table Y k) =
        afterApprox M (M.run bound (M.init table)).var
          (afterBank M table Y k bound) := by
  obtain ⟨t,ht,hr⟩ := local_prefix M table answer Y k bound hM
  refine ⟨t,ht,?_⟩
  rw [hr]
  have hh := (BitMachine.outputsWithin_at_bound M hM).1
  simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, hh, afterApprox, afterBank]

theorem reset_prefix (table answer : List Bool) (Y k bound : ℕ)
    (hM : M.OutputsWithin table answer bound) :
    ∃ t ≤ bound + 1,
      run M t (start M table Y k) =
        compareStart M (afterBank M table Y k bound) := by
  obtain ⟨t,ht,hr⟩ := local_endpoint M table answer Y k bound hM
  refine ⟨t+1, by omega, ?_⟩
  have hadd : run M (t+1) (start M table Y k) =
      advance (program M) (run M t (start M table Y k)) := by
    exact Function.iterate_succ_apply' _ _ _
  rw [hadd, hr, reset_step]

theorem compare_start_eq_embed (table answer : List Bool)
    (Y k bound : ℕ) (hM : M.OutputsWithin table answer bound) :
    compareStart M (afterBank M table Y k bound) =
      BitMachineStackEmbedding.cfg (compareStack M)
        (afterBank M table Y k bound)
        (fun l => (.inr (.inr l) : Label M))
        (fun v => (M.initial,v)) none
        (⟨some (.inl .double), initialCompare,
          SignedMidpointCapCompare.inputBank answer Y k⟩ :
          SignedMidpointCapCompare.Config) := by
  have hb := afterBank_cap M table answer Y k bound hM
  simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, compareStart, hb]

theorem compare_suffix (table : List Bool) (a : ℤ) (Y k bound : ℕ)
    (hM : M.OutputsWithin table (EncodedETHTail.encodeInteger a) bound) :
    ∃ t ≤ SignedMidpointCapPacket.fuel
        (SignedMidpointCapCompare.inputBank (EncodedETHTail.encodeInteger a) Y k),
      (run M t (compareStart M (afterBank M table Y k bound))).l = none ∧
      (run M t (compareStart M (afterBank M table Y k bound))).stk (.inr 3) =
        [decide (2*a < (2*Y+k : ℤ))] := by
  let S := afterBank M table Y k bound
  let c : SignedMidpointCapCompare.Config :=
    ⟨some (.inl .double), initialCompare,
      SignedMidpointCapCompare.inputBank (EncodedETHTail.encodeInteger a) Y k⟩
  let f := SignedMidpointCapPacket.fuel
    (SignedMidpointCapCompare.inputBank (EncodedETHTail.encodeInteger a) Y k)
  have hh : (SignedMidpointCapCompare.run f c).l = none :=
    SignedMidpointCapPacket.canonical_halt a Y k
  obtain ⟨t,ht,hr⟩ := BitMachineStackEmbedding.outputs (compareStack M) S
    (fun l => (.inr (.inr l) : Label M))
    (fun v => (M.initial,v)) Prod.snd (by intro v; rfl) none
    SignedMidpointCapCompare.program (program M) (by intro l; rfl)
    c f hh
  have hc := compare_start_eq_embed M table (EncodedETHTail.encodeInteger a)
    Y k bound hM
  have hout : (SignedMidpointCapCompare.run f c).stk 4 =
      [decide (2*a < (2*Y+k : ℤ))] := by
    have h := SignedMidpointCapPacket.final_decision a Y k
    rw [SignedMidpointCapPacket.finalPacket,
      BankFieldProjection.result_encode] at h
    exact h
  refine ⟨t,ht,?_,?_⟩
  · change (((advance (program M))^[t]) (compareStart M S)).l = none
    rw [hc, hr]
    have hh' : ((advance SignedMidpointCapCompare.program)^[f] c).l = none := hh
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hh']
  · change (((advance (program M))^[t]) (compareStart M S)).stk (.inr 3) = _
    rw [hc, hr]
    change (BitMachineStackEmbedding.bank (compareStack M) S
      (SignedMidpointCapCompare.run f c).stk)
      ((compareStack M) (4 : Fin 5)) = _
    rw [BitMachineStackEmbedding.bank_at]
    exact hout

/-- One actual finite program runs the supplied approximation machine,
preserves the two unary parameter banks, constructs `2Y+k`, and returns the
strict signed comparison. Its transition count charges both executions and
the single control-reset step. -/
theorem callback_run (table : List Bool) (a : ℤ) (Y k bound : ℕ)
    (hM : M.OutputsWithin table (EncodedETHTail.encodeInteger a) bound) :
    ∃ t ≤ bound + 1 + SignedMidpointCapPacket.fuel
        (SignedMidpointCapCompare.inputBank (EncodedETHTail.encodeInteger a) Y k),
      (run M t (start M table Y k)).l = none ∧
      (run M t (start M table Y k)).stk (.inr 3) =
        [decide (2*a < (2*Y+k : ℤ))] := by
  obtain ⟨u,hu,hprefix⟩ := reset_prefix M table (EncodedETHTail.encodeInteger a)
    Y k bound hM
  obtain ⟨v,hv,hhalt,hout⟩ := compare_suffix M table a Y k bound hM
  refine ⟨u+v, by omega, ?_, ?_⟩
  · have hadd : run M (u+v) (start M table Y k) =
        run M v (run M u (start M table Y k)) := by
      simp only [run, Nat.add_comm u v, Function.iterate_add_apply]
    rw [hadd, hprefix]
    exact hhalt
  · have hadd : run M (u+v) (start M table Y k) =
        run M v (run M u (start M table Y k)) := by
      simp only [run, Nat.add_comm u v, Function.iterate_add_apply]
    rw [hadd, hprefix]
    exact hout

end EthInapproximability.CurrentPaper.SignedMidpointApproxCore
