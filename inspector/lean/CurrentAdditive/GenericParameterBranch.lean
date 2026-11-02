import EthInapproximability.CurrentPaper.ExactParameterBranchInstall

/-! A genuine persistent-bank type generalization of the existing ETH
branch installer. The existing source and specialized API are unchanged.
Its already generic physical copy operation and run theorem are reused
directly; the rest is the same finite controller on an arbitrary Base. -/
namespace CurrentAdditive.GenericParameterBranch
open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
export EthInapproximability.CurrentPaper.ExactParameterBranchInstall
  (copyProgram copy_run PairLabel PairControl Label Control startLabel startControl)

variable {Base : Type*} [DecidableEq Base]
abbrev Stack (M : BitMachine.Machine) (Base : Type*) := Base ⊕ (Fin M.stackCount ⊕ Fin 3)

instance (M : BitMachine.Machine) : DecidableEq (Stack M Base) := by
  dsimp [Stack]
  infer_instance

def machineSlots (M : BitMachine.Machine) : Fin M.stackCount ↪ Stack M Base where
  toFun k := .inr (.inl k)
  inj' := by
    intro x y h
    cases h
    rfl

def inSlots (M : BitMachine.Machine) (source : Base) : Fin 3 ↪ Stack M Base where
  toFun
    | 0 => .inl source
    | 1 => machineSlots M M.input
    | _ => .inr (.inr 0)
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [machineSlots]

def outSlots (M : BitMachine.Machine) (target : Base) : Fin 3 ↪ Stack M Base where
  toFun
    | 0 => machineSlots M M.output
    | 1 => .inl target
    | _ => .inr (.inr 1)
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [machineSlots]

def initial (M : BitMachine.Machine) (B : Base → List Bool) :
    Stack M Base → List Bool := Sum.elim B (fun _ => [])

def afterIn (M : BitMachine.Machine) (B : Base → List Bool)
    (bits : List Bool) : Stack M Base → List Bool :=
  Function.update (initial M B) (machineSlots M M.input) bits

def inputProgram (M : BitMachine.Machine) (source : Base) :=
  copyProgram (inSlots M source)

theorem run_input (M : BitMachine.Machine) (B : Base → List Bool)
    (source : Base) (bits : List Bool) (hsource : B source = bits) :
    ∃ t ≤ 2 * bits.length + 2,
      ((advance (inputProgram M source))^[t])
        (⟨some .scan, none, initial M B⟩ :
          TM2.Cfg (fun _ : Stack M Base => Bool) BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, afterIn M B bits⟩ := by
  have hsource' : initial M B ((inSlots M source) 0) = bits := hsource
  have htarget : initial M B ((inSlots M source) 1) = [] := rfl
  have hscratch : initial M B ((inSlots M source) 2) = [] := rfl
  exact copy_run (inSlots M source) (initial M B) bits
    hsource' htarget hscratch

theorem frame_input (M : BitMachine.Machine) (B : Base → List Bool)
    (bits : List Bool) :
    ExactParameterMachineFrame.inputBank M (machineSlots M)
      (afterIn M B bits) bits = afterIn M B bits := by
  classical
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  by_cases hk : k = M.input
  · subst k
    simp [BitMachine.Machine.init, afterIn, machineSlots]
  · simp [BitMachine.Machine.init, afterIn, initial, machineSlots, hk]

def machineProgram (M : BitMachine.Machine) :=
  ExactParameterMachineFrame.program M (machineSlots (Base := Base) M)

noncomputable def afterMachine (M : BitMachine.Machine) (B : Base → List Bool)
    (bits : List Bool) (T : ℕ) : Stack M Base → List Bool :=
  ExactParameterMachineFrame.terminalBank M (machineSlots M)
    (afterIn M B bits) bits T

theorem run_machine (M : BitMachine.Machine) (B : Base → List Bool)
    (bits result : List Bool) (T : ℕ)
    (h : M.OutputsWithin bits result T) :
    ((advance (machineProgram M))^[T])
      (⟨some M.start, M.initial, afterIn M B bits⟩ :
        TM2.Cfg (fun _ : Stack M Base => Bool) (Fin M.labelCount)
          (Fin M.controlCount)) =
      ⟨none, (M.run T (M.init bits)).var, afterMachine M B bits T⟩ := by
  have hr := ExactParameterMachineFrame.run M (machineSlots M)
    (afterIn M B bits) bits T
  rw [frame_input] at hr
  have hh := (BitMachine.outputsWithin_at_bound M h).1
  rw [hh] at hr
  exact hr

theorem afterMachine_output (M : BitMachine.Machine) (B : Base → List Bool)
    (bits result : List Bool) (T : ℕ)
    (h : M.OutputsWithin bits result T) :
    afterMachine M B bits T (machineSlots M M.output) = result :=
  ExactParameterMachineFrame.output M (machineSlots M)
    (afterIn M B bits) bits result T h

theorem afterMachine_base (M : BitMachine.Machine) (B : Base → List Bool)
    (bits : List Bool) (T : ℕ) (j : Base) :
    afterMachine M B bits T (.inl j) = B j := by
  rw [afterMachine, ExactParameterMachineFrame.foreign_at]
  · simp [afterIn, initial, machineSlots]
  · intro ⟨k, hk⟩
    cases hk

theorem afterMachine_scratch (M : BitMachine.Machine) (B : Base → List Bool)
    (bits : List Bool) (T : ℕ) (j : Fin 3) :
    afterMachine M B bits T (.inr (.inr j)) = [] := by
  rw [afterMachine, ExactParameterMachineFrame.foreign_at]
  · simp [afterIn, initial, machineSlots]
  · intro ⟨k, hk⟩
    cases hk

def outputProgram (M : BitMachine.Machine) (target : Base) :=
  copyProgram (outSlots M target)

noncomputable def terminal (M : BitMachine.Machine) (B : Base → List Bool)
    (target : Base) (bits result : List Bool) (T : ℕ) :
    Stack M Base → List Bool :=
  Function.update (afterMachine M B bits T) (.inl target) result

theorem run_output (M : BitMachine.Machine) (B : Base → List Bool)
    (target : Base) (bits result : List Bool) (T : ℕ)
    (h : M.OutputsWithin bits result T) (htarget : B target = []) :
    ∃ t ≤ 2 * result.length + 2,
      ((advance (outputProgram M target))^[t])
        (⟨some .scan, none, afterMachine M B bits T⟩ :
          TM2.Cfg (fun _ : Stack M Base => Bool) BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, terminal M B target bits result T⟩ := by
  apply copy_run (outSlots M target) (afterMachine M B bits T) result
  · exact afterMachine_output M B bits result T h
  · simpa [outSlots] using (afterMachine_base M B bits T target).trans htarget
  · exact afterMachine_scratch M B bits T 1

theorem terminal_target (M : BitMachine.Machine) (B : Base → List Bool)
    (target : Base) (bits result : List Bool) (T : ℕ) :
    terminal M B target bits result T (.inl target) = result := by
  simp [terminal]

theorem terminal_base_other (M : BitMachine.Machine) (B : Base → List Bool)
    (target : Base) (bits result : List Bool) (T : ℕ)
    (j : Base) (hj : j ≠ target) :
    terminal M B target bits result T (.inl j) = B j := by
  simp [terminal, hj, afterMachine_base]

def pairProgram (M : BitMachine.Machine) (source : Base) :
    PairLabel M → TM2.Stmt (fun _ : Stack M Base => Bool)
      (PairLabel M) (PairControl M) :=
  BitMachineRawSequence.program (inputProgram M source) (machineProgram M)
    M.start none M.initial

def program (M : BitMachine.Machine) (source target : Base) :
    Label M → TM2.Stmt (fun _ : Stack M Base => Bool) (Label M) (Control M) :=
  BitMachineRawSequence.program (pairProgram M source)
    (outputProgram M target) .scan (none, M.initial) none

/-- One source-preserving branch installation consists of two charged copies,
one actual fixed-machine run, and two finite-control handoffs. -/
theorem run_install (M : BitMachine.Machine) (B : Base → List Bool)
    (source target : Base) (bits result : List Bool) (T : ℕ)
    (hsource : B source = bits) (htarget : B target = [])
    (h : M.OutputsWithin bits result T) :
    ∃ t ≤ 2 * bits.length + T + 2 * result.length + 6,
      ((advance (program M source target))^[t])
        (⟨some (startLabel M), startControl M, initial M B⟩ :
          TM2.Cfg (fun _ : Stack M Base => Bool) (Label M) (Control M)) =
        ⟨none, startControl M,
          terminal M B target bits result T⟩ := by
  obtain ⟨ti, hti, hri⟩ := run_input M B source bits hsource
  have hrm := run_machine M B bits result T h
  obtain ⟨tp, htp, hrp⟩ := BitMachineRawSequence.runs
    (inputProgram M source) (machineProgram M) .scan M.start
    none none M.initial (M.run T (M.init bits)).var
    (initial M B) (afterIn M B bits) (afterMachine M B bits T)
    ti T hri hrm
  obtain ⟨tout, htout, hro⟩ := run_output M B target bits result T h htarget
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (pairProgram M source) (outputProgram M target) (.inl .scan) .scan
    (none, M.initial) (none, (M.run T (M.init bits)).var)
    none none
    (initial M B) (afterMachine M B bits T)
    (terminal M B target bits result T) tp tout hrp hro
  refine ⟨t, by omega, ?_⟩
  simpa only [program, startLabel, startControl] using hr

def framedProgram {J : Type*} [DecidableEq J] (M : BitMachine.Machine)
    (source target : Base) (ι : Stack M Base ↪ J) (l : Label M) :
    TM2.Stmt (fun _ : J => Bool) (Label M) (Control M) :=
  BitMachineStackEmbedding.stmt ι id id id none (program M source target l)

/-- A branch installer can be placed into any larger bank with fresh local
cells. The entire ambient bank, including every foreign stack, is tracked. -/
theorem run_install_framed {J : Type*} [DecidableEq J]
    (M : BitMachine.Machine) (B : Base → List Bool)
    (source target : Base) (bits result : List Bool) (T : ℕ)
    (ι : Stack M Base ↪ J) (foreign : J → List Bool)
    (hsource : B source = bits) (htarget : B target = [])
    (h : M.OutputsWithin bits result T) :
    ∃ t ≤ 2 * bits.length + T + 2 * result.length + 6,
      ((advance (framedProgram M source target ι))^[t])
        (⟨some (startLabel M), startControl M,
          BitMachineStackEmbedding.bank ι foreign (initial M B)⟩ :
          TM2.Cfg (fun _ : J => Bool) (Label M) (Control M)) =
        ⟨none, startControl M,
          BitMachineStackEmbedding.bank ι foreign
            (terminal M B target bits result T)⟩ := by
  classical
  obtain ⟨u, hu, hr⟩ := run_install M B source target bits result T
    hsource htarget h
  have hh : (((advance (program M source target))^[u])
      (⟨some (startLabel M), startControl M, initial M B⟩ :
        TM2.Cfg (fun _ : Stack M Base => Bool) (Label M) (Control M))).l = none := by
    rw [hr]
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs ι foreign
    id id id (by intro v; rfl) none
    (program M source target) (framedProgram M source target ι)
    (by intro l; rfl)
    (⟨some (startLabel M), startControl M, initial M B⟩ :
      TM2.Cfg (fun _ : Stack M Base => Bool) (Label M) (Control M)) u hh
  rw [hr] at he
  refine ⟨t, ht.trans hu, ?_⟩
  simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg] using he

theorem framed_foreign {J : Type*} [DecidableEq J]
    (M : BitMachine.Machine) (B : Base → List Bool)
    (target : Base) (bits result : List Bool) (T : ℕ)
    (ι : Stack M Base ↪ J) (foreign : J → List Bool)
    (j : J) (hj : ¬ ∃ k, ι k = j) :
    BitMachineStackEmbedding.bank ι foreign
      (terminal M B target bits result T) j = foreign j :=
  BitMachineStackEmbedding.bank_outside ι foreign _ j hj

/-- Ambient form for repeatedly installing branches. Persistent Base words
are read from the actual current bank; only this branch's fresh auxiliary
cells must be empty. Earlier branch auxiliaries outside `ι` are preserved. -/
theorem run_install_framed_from_ambient {J : Type*} [DecidableEq J]
    (M : BitMachine.Machine) (source target : Base)
    (bits result : List Bool) (T : ℕ)
    (ι : Stack M Base ↪ J) (S : J → List Bool)
    (hsource : S (ι (.inl source)) = bits)
    (htarget : S (ι (.inl target)) = [])
    (hfresh : ∀ k : Fin M.stackCount ⊕ Fin 3,
      S (ι (.inr k)) = [])
    (h : M.OutputsWithin bits result T) :
    let B : Base → List Bool := fun j => S (ι (.inl j))
    ∃ t ≤ 2 * bits.length + T + 2 * result.length + 6,
      ((advance (framedProgram M source target ι))^[t])
        (⟨some (startLabel M), startControl M, S⟩ :
          TM2.Cfg (fun _ : J => Bool) (Label M) (Control M)) =
        ⟨none, startControl M,
          BitMachineStackEmbedding.bank ι S
            (terminal M B target bits result T)⟩ := by
  classical
  dsimp only
  let B : Base → List Bool := fun j => S (ι (.inl j))
  have hplace : BitMachineStackEmbedding.bank ι S (initial M B) = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    cases k with
    | inl j => rfl
    | inr j => exact (hfresh j).symm
  obtain ⟨t, ht, hr⟩ := run_install_framed M B source target bits result T
    ι S hsource htarget h
  rw [hplace] at hr
  exact ⟨t, ht, hr⟩

theorem ambient_target {J : Type*} [DecidableEq J]
    (M : BitMachine.Machine) (target : Base)
    (B : Base → List Bool) (bits result : List Bool) (T : ℕ)
    (ι : Stack M Base ↪ J) (S : J → List Bool) :
    BitMachineStackEmbedding.bank ι S
      (terminal M B target bits result T) (ι (.inl target)) = result := by
  rw [BitMachineStackEmbedding.bank_at, terminal_target]

theorem ambient_base_other {J : Type*} [DecidableEq J]
    (M : BitMachine.Machine) (target j : Base) (hj : j ≠ target)
    (B : Base → List Bool) (bits result : List Bool) (T : ℕ)
    (ι : Stack M Base ↪ J) (S : J → List Bool) :
    BitMachineStackEmbedding.bank ι S
      (terminal M B target bits result T) (ι (.inl j)) = B j := by
  rw [BitMachineStackEmbedding.bank_at]
  exact terminal_base_other M B target bits result T j hj

theorem terminal_source (M : BitMachine.Machine) (B : Base → List Bool)
    (source target : Base) (bits result : List Bool) (T : ℕ)
    (hsource : B source = bits) (hdistinct : source ≠ target) :
    terminal M B target bits result T (.inl source) = bits := by
  rw [terminal_base_other M B target bits result T source hdistinct]
  exact hsource

end CurrentAdditive.GenericParameterBranch
