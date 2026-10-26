import EthInapproximability.CurrentPaper.ExactParameterMachineFrame
import EthInapproximability.CurrentPaper.MatrixExactSamplerHeaderSequence
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
# Physical installation of one source-derived parameter branch

The persistent source is a unary decoded edge-count stack. A literal copy
feeds a fixed finite bit machine on fresh local stacks; a second literal copy
puts its computed output into an empty persistent destination. Every phase is
an actual Boolean-stack controller and every cell moved is charged.
-/

namespace EthInapproximability.CurrentPaper.ExactParameterBranchInstall

open Turing BitMachineEncoding

def copyProgram {K : Type*} [DecidableEq K] (ι : Fin 3 ↪ K)
    (l : BitMachineCopy.Label) :
    TM2.Stmt (fun _ : K => Bool) BitMachineCopy.Label (Option Bool) :=
  BitMachineStackEmbedding.stmt ι id id id none (BitMachineCopy.program l)

/-- Copying preserves the source, writes to an initially empty target, and
clears its scratch stack. The bank equality is exact, not just pointwise at
the destination. -/
theorem copy_run {K : Type*} [DecidableEq K] (ι : Fin 3 ↪ K)
    (S : K → List Bool) (bits : List Bool)
    (hsource : S (ι 0) = bits) (htarget : S (ι 1) = [])
    (hscratch : S (ι 2) = []) :
    ∃ t ≤ 2 * bits.length + 2,
      ((advance (copyProgram ι))^[t])
        (⟨some .scan, none, S⟩ :
          TM2.Cfg (fun _ : K => Bool) BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, Function.update S (ι 1) bits⟩ := by
  classical
  let c := BitMachineCopy.cfg (some .scan) none bits [] []
  have hbank : BitMachineStackEmbedding.bank ι S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;> simp [c, BitMachineCopy.cfg,
      BitMachineCopy.stackContents, hsource, htarget, hscratch]
  have hhalt : (((advance BitMachineCopy.program)^[2 * bits.length + 2]) c).l =
      none := by
    change (BitMachineCopy.run (2 * bits.length + 2) c).l = none
    rw [show c = BitMachineCopy.cfg (some .scan) none bits [] [] from rfl,
      BitMachineCopy.run_correct]
    rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs ι S
    id id id (by intro v; rfl) none
    BitMachineCopy.program (copyProgram ι) (by intro l; rfl)
    c (2 * bits.length + 2) hhalt
  have hlocal : ((advance BitMachineCopy.program)^[2 * bits.length + 2]) c =
      BitMachineCopy.cfg none none bits bits [] := by
    change BitMachineCopy.run (2 * bits.length + 2) c = _
    simpa only [List.append_nil] using
      BitMachineCopy.run_correct none bits []
  rw [hlocal] at he
  change ((advance (copyProgram ι))^[t])
      ⟨some .scan, none, BitMachineStackEmbedding.bank ι S c.stk⟩ =
      ⟨none, none,
        BitMachineStackEmbedding.bank ι S
          (BitMachineCopy.cfg none none bits bits []).stk⟩ at he
  have hupdate : (BitMachineCopy.cfg none none bits bits []).stk =
      Function.update c.stk 1 bits := by
    funext k
    fin_cases k <;> rfl
  rw [hbank, hupdate, BitMachineStackEmbedding.bank_update, hbank] at he
  exact ⟨t, ht, he⟩

abbrev Base := MatrixExactSamplerHeaderBridge.Stack ⊕ Fin 1
abbrev Stack (M : BitMachine.Machine) := Base ⊕ (Fin M.stackCount ⊕ Fin 3)

instance (M : BitMachine.Machine) : DecidableEq (Stack M) := by
  dsimp [Stack, Base]
  infer_instance

def machineSlots (M : BitMachine.Machine) : Fin M.stackCount ↪ Stack M where
  toFun k := .inr (.inl k)
  inj' := by
    intro x y h
    cases h
    rfl

def inSlots (M : BitMachine.Machine) (source : Base) : Fin 3 ↪ Stack M where
  toFun
    | 0 => .inl source
    | 1 => machineSlots M M.input
    | _ => .inr (.inr 0)
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [machineSlots]

def outSlots (M : BitMachine.Machine) (target : Base) : Fin 3 ↪ Stack M where
  toFun
    | 0 => machineSlots M M.output
    | 1 => .inl target
    | _ => .inr (.inr 1)
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [machineSlots]

def initial (M : BitMachine.Machine) (B : Base → List Bool) :
    Stack M → List Bool := Sum.elim B (fun _ => [])

def afterIn (M : BitMachine.Machine) (B : Base → List Bool)
    (bits : List Bool) : Stack M → List Bool :=
  Function.update (initial M B) (machineSlots M M.input) bits

def inputProgram (M : BitMachine.Machine) (source : Base) :=
  copyProgram (inSlots M source)

theorem run_input (M : BitMachine.Machine) (B : Base → List Bool)
    (source : Base) (bits : List Bool) (hsource : B source = bits) :
    ∃ t ≤ 2 * bits.length + 2,
      ((advance (inputProgram M source))^[t])
        (⟨some .scan, none, initial M B⟩ :
          TM2.Cfg (fun _ : Stack M => Bool) BitMachineCopy.Label (Option Bool)) =
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
  ExactParameterMachineFrame.program M (machineSlots M)

noncomputable def afterMachine (M : BitMachine.Machine) (B : Base → List Bool)
    (bits : List Bool) (T : ℕ) : Stack M → List Bool :=
  ExactParameterMachineFrame.terminalBank M (machineSlots M)
    (afterIn M B bits) bits T

theorem run_machine (M : BitMachine.Machine) (B : Base → List Bool)
    (bits result : List Bool) (T : ℕ)
    (h : M.OutputsWithin bits result T) :
    ((advance (machineProgram M))^[T])
      (⟨some M.start, M.initial, afterIn M B bits⟩ :
        TM2.Cfg (fun _ : Stack M => Bool) (Fin M.labelCount)
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
    Stack M → List Bool :=
  Function.update (afterMachine M B bits T) (.inl target) result

theorem run_output (M : BitMachine.Machine) (B : Base → List Bool)
    (target : Base) (bits result : List Bool) (T : ℕ)
    (h : M.OutputsWithin bits result T) (htarget : B target = []) :
    ∃ t ≤ 2 * result.length + 2,
      ((advance (outputProgram M target))^[t])
        (⟨some .scan, none, afterMachine M B bits T⟩ :
          TM2.Cfg (fun _ : Stack M => Bool) BitMachineCopy.Label (Option Bool)) =
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

abbrev PairLabel (M : BitMachine.Machine) :=
  BitMachineRawSequence.Label BitMachineCopy.Label (Fin M.labelCount)
abbrev PairControl (M : BitMachine.Machine) :=
  BitMachineRawSequence.Control (Option Bool) (Fin M.controlCount)

def pairProgram (M : BitMachine.Machine) (source : Base) :
    PairLabel M → TM2.Stmt (fun _ : Stack M => Bool)
      (PairLabel M) (PairControl M) :=
  BitMachineRawSequence.program (inputProgram M source) (machineProgram M)
    M.start none M.initial

abbrev Label (M : BitMachine.Machine) :=
  BitMachineRawSequence.Label (PairLabel M) BitMachineCopy.Label
abbrev Control (M : BitMachine.Machine) :=
  BitMachineRawSequence.Control (PairControl M) (Option Bool)

def program (M : BitMachine.Machine) (source target : Base) :
    Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M) :=
  BitMachineRawSequence.program (pairProgram M source)
    (outputProgram M target) .scan (none, M.initial) none

def startLabel (M : BitMachine.Machine) : Label M := .inl (.inl .scan)
def startControl (M : BitMachine.Machine) : Control M :=
  ((none, M.initial), none)

/-- One source-preserving branch installation consists of two charged copies,
one actual fixed-machine run, and two finite-control handoffs. -/
theorem run_install (M : BitMachine.Machine) (B : Base → List Bool)
    (source target : Base) (bits result : List Bool) (T : ℕ)
    (hsource : B source = bits) (htarget : B target = [])
    (h : M.OutputsWithin bits result T) :
    ∃ t ≤ 2 * bits.length + T + 2 * result.length + 6,
      ((advance (program M source target))^[t])
        (⟨some (startLabel M), startControl M, initial M B⟩ :
          TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)) =
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
    (source target : Base) (ι : Stack M ↪ J) (l : Label M) :
    TM2.Stmt (fun _ : J => Bool) (Label M) (Control M) :=
  BitMachineStackEmbedding.stmt ι id id id none (program M source target l)

/-- A branch installer can be placed into any larger bank with fresh local
cells. The entire ambient bank, including every foreign stack, is tracked. -/
theorem run_install_framed {J : Type*} [DecidableEq J]
    (M : BitMachine.Machine) (B : Base → List Bool)
    (source target : Base) (bits result : List Bool) (T : ℕ)
    (ι : Stack M ↪ J) (foreign : J → List Bool)
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
        TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M))).l = none := by
    rw [hr]
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs ι foreign
    id id id (by intro v; rfl) none
    (program M source target) (framedProgram M source target ι)
    (by intro l; rfl)
    (⟨some (startLabel M), startControl M, initial M B⟩ :
      TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)) u hh
  rw [hr] at he
  refine ⟨t, ht.trans hu, ?_⟩
  simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg] using he

theorem framed_foreign {J : Type*} [DecidableEq J]
    (M : BitMachine.Machine) (B : Base → List Bool)
    (target : Base) (bits result : List Bool) (T : ℕ)
    (ι : Stack M ↪ J) (foreign : J → List Bool)
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
    (ι : Stack M ↪ J) (S : J → List Bool)
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
    (ι : Stack M ↪ J) (S : J → List Bool) :
    BitMachineStackEmbedding.bank ι S
      (terminal M B target bits result T) (ι (.inl target)) = result := by
  rw [BitMachineStackEmbedding.bank_at, terminal_target]

theorem ambient_base_other {J : Type*} [DecidableEq J]
    (M : BitMachine.Machine) (target j : Base) (hj : j ≠ target)
    (B : Base → List Bool) (bits result : List Bool) (T : ℕ)
    (ι : Stack M ↪ J) (S : J → List Bool) :
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

end EthInapproximability.CurrentPaper.ExactParameterBranchInstall
