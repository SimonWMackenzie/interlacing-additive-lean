import CurrentAdditive.RawRatPairAssembler

namespace CurrentAdditive.RawRatPostMachinePair

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CodeDCodec CodeDPairProductTargetV2

abbrev Stack (M : BitMachine.Machine) := Fin M.stackCount ⊕ Fin 5
abbrev Bank (M : BitMachine.Machine) := Stack M → List Bool
abbrev AsmLabel :=
  BitMachineRawSequence.Label
    (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
    (BitMachineBankSerialize.Label 2)
abbrev AsmControl := (Option Bool × Option Bool) × Option Bool

def mSlots (M : BitMachine.Machine) : Fin M.stackCount ↪ Stack M where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def asmStart : AsmLabel :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
def asmInitial : AsmControl := ((none,none),none)

def locate (M : BitMachine.Machine) (s : Fin M.stackCount)
    (hs : s ≠ M.output) : RawRatPairAssembler.Stack 0 ↪ Stack M where
  toFun
    | .inl i => ![Sum.inl M.output, Sum.inl s,
        Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4] i
    | .inr i => Fin.elim0 i
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            fin_cases a <;> fin_cases b <;>
              simp_all [Ne.symm hs]
        | inr b => exact Fin.elim0 b
    | inr a => exact Fin.elim0 a

def stageM (M : BitMachine.Machine) : Fin M.labelCount →
    TM2.Stmt (fun _ : Stack M => Bool) (Fin M.labelCount)
      (Fin M.controlCount) :=
  fun l => BitMachineStackEmbedding.stmt (mSlots M) id id id none (M.program l)

def stagePair (M : BitMachine.Machine) (s : Fin M.stackCount)
    (hs : s ≠ M.output) : AsmLabel →
    TM2.Stmt (fun _ : Stack M => Bool) AsmLabel AsmControl :=
  fun l => BitMachineStackEmbedding.stmt (locate M s hs) id id id none
    (RawRatPairAssembler.program 0 l)

def program (M : BitMachine.Machine) (s : Fin M.stackCount)
    (hs : s ≠ M.output) :=
  BitMachineRawSequence.program (stageM M) (stagePair M s hs)
    asmStart M.initial asmInitial

def initialBank (M : BitMachine.Machine) (input : List Bool) : Bank M :=
  Sum.elim (M.init input).stk (fun _ => [])

def afterBank (M : BitMachine.Machine) (input : List Bool) (t : Nat) : Bank M :=
  Sum.elim (M.run t (M.init input)).stk (fun _ => [])

theorem stageM_start (M : BitMachine.Machine) (input : List Bool) :
    BitMachineStackEmbedding.cfg (mSlots M)
      (initialBank M input) id id none (M.init input) =
    ⟨some M.start, M.initial, initialBank M input⟩ := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  rfl

theorem stageM_end (M : BitMachine.Machine) (input : List Bool)
    (t : Nat) (hh : (M.run t (M.init input)).l = none) :
    BitMachineStackEmbedding.cfg (mSlots M)
      (initialBank M input) id id none (M.run t (M.init input)) =
    ⟨none, (M.run t (M.init input)).var, afterBank M input t⟩ := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  simp only [hh]
  congr 1
  funext j
  cases j with
  | inl j =>
      change BitMachineStackEmbedding.bank (mSlots M)
        (initialBank M input) (M.run t (M.init input)).stk
          (mSlots M j) = _
      rw [BitMachineStackEmbedding.bank_at]
      rfl
  | inr j =>
      have ho : ¬ ∃ k : Fin M.stackCount,
          mSlots M k = (.inr j : Stack M) := by
        rintro ⟨k,hk⟩
        cases hk
      rw [BitMachineStackEmbedding.bank_outside _ _ _ _ ho]
      rfl

theorem stageM_run (M : BitMachine.Machine) (input : List Bool)
    (t : Nat) (hh : (M.run t (M.init input)).l = none) :
    ∃ u ≤ t,
      ((advance (stageM M))^[u])
        (⟨some M.start, M.initial, initialBank M input⟩ :
          TM2.Cfg (fun _ : Stack M => Bool) _ _) =
        ⟨none, (M.run t (M.init input)).var,
          afterBank M input t⟩ := by
  have hhalt : ((advance M.program)^[t] (M.init input)).l = none := by
    simpa only [BitMachine.Machine.run, BitMachine.Machine.step,
      advance] using hh
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs
    (mSlots M) (initialBank M input) id id id
    (by intro v; rfl) none M.program (stageM M)
    (by intro l; rfl) (M.init input) t hhalt
  refine ⟨u,hu,?_⟩
  change ((advance (stageM M))^[u])
      (BitMachineStackEmbedding.cfg (mSlots M)
        (initialBank M input) id id none (M.init input)) =
      BitMachineStackEmbedding.cfg (mSlots M)
        (initialBank M input) id id none (M.run t (M.init input)) at hr
  rw [stageM_start, stageM_end M input t hh] at hr
  exact hr

theorem stagePair_start (M : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (input : List Bool) (t : Nat) (q saved : List Bool)
    (hq : (M.run t (M.init input)).stk M.output = q)
    (hsv : (M.run t (M.init input)).stk s = saved) :
    BitMachineStackEmbedding.cfg (locate M s hs)
      (afterBank M input t) id id none
      (⟨some asmStart, asmInitial,
        RawRatPairAssembler.initialBank q saved (Fin.elim0)⟩ :
        TM2.Cfg (fun _ : RawRatPairAssembler.Stack 0 => Bool) _ _) =
    ⟨some asmStart, asmInitial, afterBank M input t⟩ := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  cases k with
  | inl k =>
      fin_cases k <;>
        simp [RawRatPairAssembler.initialBank, locate, afterBank, hq, hsv]
  | inr k => exact Fin.elim0 k

noncomputable def finalBank (M : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (input : List Bool) (t : Nat) (q saved : List Bool)
    (S' : BitMachineBankSerialize.Bank 2) : Bank M :=
  BitMachineStackEmbedding.bank (locate M s hs) (afterBank M input t)
    (RawRatPairAssembler.completedBank q saved (Fin.elim0) S')

theorem stagePair_run (M : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (input : List Bool) (t : Nat) (q saved : List Bool)
    (hq : (M.run t (M.init input)).stk M.output = q)
    (hsv : (M.run t (M.init input)).stk s = saved) :
    ∃ u ≤ 6*(q.length+saved.length+2),
      ∃ S' : BitMachineBankSerialize.Bank 2,
      ((advance (stagePair M s hs))^[u])
        (⟨some asmStart, asmInitial, afterBank M input t⟩ :
          TM2.Cfg (fun _ : Stack M => Bool) _ _) =
        ⟨none, asmInitial, finalBank M s hs input t q saved S'⟩ := by
  obtain ⟨a,ha,S',hr⟩ := RawRatPairAssembler.assembly_run
    q saved (Fin.elim0)
  have hh : (((advance (RawRatPairAssembler.program 0))^[a])
      (⟨some asmStart, asmInitial,
        RawRatPairAssembler.initialBank q saved (Fin.elim0)⟩ :
        TM2.Cfg (fun _ : RawRatPairAssembler.Stack 0 => Bool) _ _)).l = none := by
    simpa [asmStart, asmInitial] using congrArg (fun c => c.l) hr
  have hr' : ((advance (RawRatPairAssembler.program 0))^[a])
      (⟨some asmStart, asmInitial,
        RawRatPairAssembler.initialBank q saved (Fin.elim0)⟩ :
        TM2.Cfg (fun _ : RawRatPairAssembler.Stack 0 => Bool) _ _) =
      ⟨none, asmInitial,
        RawRatPairAssembler.completedBank q saved (Fin.elim0) S'⟩ := by
    simpa [asmStart, asmInitial] using hr
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs
    (locate M s hs) (afterBank M input t) id id id
    (by intro v; rfl) none (RawRatPairAssembler.program 0)
    (stagePair M s hs) (by intro l; rfl)
    (⟨some asmStart, asmInitial,
      RawRatPairAssembler.initialBank q saved (Fin.elim0)⟩ :
      TM2.Cfg (fun _ : RawRatPairAssembler.Stack 0 => Bool) _ _)
    a hh
  refine ⟨u,hu.trans ha,S',?_⟩
  rw [stagePair_start M s hs input t q saved hq hsv, hr'] at he
  simpa [finalBank, BitMachineStackEmbedding.cfg,
    BitMachineInline.cfg] using he

theorem post_run (M : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (input q saved : List Bool) (T : Nat)
    (hM : M.OutputsWithin input q T)
    (hsv : (M.run T (M.init input)).stk s = saved) :
    ∃ t ≤ T + 6*(q.length+saved.length+2)+1,
      ∃ S' : BitMachineBankSerialize.Bank 2,
      ((advance (program M s hs))^[t])
        (⟨some (BitMachineRawSequence.leftLabel M.start),
          (M.initial,asmInitial), initialBank M input⟩ :
          TM2.Cfg (fun _ : Stack M => Bool) _ _) =
        ⟨none,(M.initial,asmInitial),
          finalBank M s hs input T q saved S'⟩ := by
  have hbound := BitMachine.outputsWithin_at_bound M hM
  obtain ⟨a,ha,hfirst⟩ := stageM_run M input T hbound.1
  obtain ⟨b,hb,S',hsecond⟩ := stagePair_run
    M s hs input T q saved hbound.2 hsv
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    (stageM M) (stagePair M s hs)
    M.start asmStart M.initial (M.run T (M.init input)).var
    asmInitial asmInitial
    (initialBank M input) (afterBank M input T)
    (finalBank M s hs input T q saved S') a b hfirst hsecond
  exact ⟨t,by omega,S',by simpa only [program] using hr⟩

theorem final_output (M : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (input : List Bool) (T : Nat) (q saved : List Bool)
    (S' : BitMachineBankSerialize.Bank 2) :
    finalBank M s hs input T q saved S' (.inr 4) =
      RawRatPairAssembler.pairWord q saved := by
  have hk : locate M s hs (.inl 6) = (.inr 4 : Stack M) := rfl
  rw [← hk, finalBank, BitMachineStackEmbedding.bank_at]
  exact RawRatPairAssembler.completed_output q saved (Fin.elim0) S'

theorem final_source (M : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (input : List Bool) (T : Nat) (q saved : List Bool)
    (S' : BitMachineBankSerialize.Bank 2) :
    finalBank M s hs input T q saved S' (.inl M.output) = q ∧
    finalBank M s hs input T q saved S' (.inl s) = saved := by
  constructor
  · have hk : locate M s hs (.inl 0) = (.inl M.output : Stack M) := rfl
    rw [← hk, finalBank, BitMachineStackEmbedding.bank_at]
    exact RawRatPairAssembler.completed_sourceX q saved (Fin.elim0) S'
  · have hk : locate M s hs (.inl 1) = (.inl s : Stack M) := rfl
    rw [← hk, finalBank, BitMachineStackEmbedding.bank_at]
    exact RawRatPairAssembler.completed_sourceY q saved (Fin.elim0) S'

theorem final_other (M : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (input : List Bool) (T : Nat) (q saved : List Bool)
    (S' : BitMachineBankSerialize.Bank 2)
    (j : Fin M.stackCount) (hjo : j ≠ M.output) (hjs : j ≠ s) :
    finalBank M s hs input T q saved S' (.inl j) =
      (M.run T (M.init input)).stk j := by
  have ho : ¬ ∃ k : RawRatPairAssembler.Stack 0,
      locate M s hs k = (.inl j : Stack M) := by
    rintro ⟨k,hk⟩
    cases k with
    | inl k =>
        fin_cases k <;> simp_all [locate]
    | inr k => exact Fin.elim0 k
  rw [finalBank, BitMachineStackEmbedding.bank_outside _ _ _ _ ho]
  rfl

theorem post_outputs (M : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (input q saved : List Bool) (T : Nat)
    (hM : M.OutputsWithin input q T)
    (hsv : (M.run T (M.init input)).stk s = saved) :
    ∃ t ≤ T + 6*(q.length+saved.length+2)+1,
      let c := ((advance (program M s hs))^[t])
        (⟨some (BitMachineRawSequence.leftLabel M.start),
          (M.initial,asmInitial), initialBank M input⟩ :
          TM2.Cfg (fun _ : Stack M => Bool) _ _)
      c.l = none ∧
      c.stk (.inr 4) = RawRatPairAssembler.pairWord q saved ∧
      c.stk (.inl M.output) = q ∧ c.stk (.inl s) = saved ∧
      (∀ j : Fin M.stackCount, j ≠ M.output → j ≠ s →
        c.stk (.inl j) = (M.run T (M.init input)).stk j) := by
  obtain ⟨t,ht,S',hr⟩ := post_run M s hs input q saved T hM hsv
  refine ⟨t,ht,?_⟩
  dsimp only
  rw [hr]
  have hsrc := final_source M s hs input T q saved S'
  exact ⟨rfl, final_output M s hs input T q saved S',
    hsrc.1, hsrc.2, fun j hjo hjs =>
      final_other M s hs input T q saved S' j hjo hjs⟩

theorem post_pairBytes (M : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (input : List Bool) (x y : RawRat) (T : Nat)
    (hM : M.OutputsWithin input (encodeRawRat x) T)
    (hsv : (M.run T (M.init input)).stk s = encodeRawRat y) :
    ∃ t ≤ T + 6*((encodeRawRat x).length+(encodeRawRat y).length+2)+1,
      let c := ((advance (program M s hs))^[t])
        (⟨some (BitMachineRawSequence.leftLabel M.start),
          (M.initial,asmInitial), initialBank M input⟩ :
          TM2.Cfg (fun _ : Stack M => Bool) _ _)
      c.l = none ∧ c.stk (.inr 4) = pairBytes x y ∧
      c.stk (.inl M.output) = encodeRawRat x ∧
      c.stk (.inl s) = encodeRawRat y ∧
      (∀ j : Fin M.stackCount, j ≠ M.output → j ≠ s →
        c.stk (.inl j) = (M.run T (M.init input)).stk j) := by
  simpa only [RawRatPairAssembler.pairWord_exact] using
    (post_outputs M s hs input (encodeRawRat x) (encodeRawRat y)
      T hM hsv)

#print axioms post_outputs
#print axioms post_pairBytes

end CurrentAdditive.RawRatPostMachinePair
