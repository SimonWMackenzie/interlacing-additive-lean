import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.CutoffInputEncoding
import EthInapproximability.CurrentPaper.CutoffProbeMachine
import EthInapproximability.CurrentPaper.CutoffProbePreparation

/-!
# Preparing a bounded clock probe without free bank initialization

Source: frozen v8 `05-iteration.tex`, the consecutive bounded cutoff runs.
The permanent bank stores an active bit, a unary budget, and the accepted
prefix's binary counter. This controller preserves it while physically
constructing the next cutoff input and a fresh cap for the probe.
-/

namespace EthInapproximability.CurrentPaper.ClockInputPreparation

noncomputable section

open Turing TM2.Stmt BitMachineEncoding BitMachineStackEmbedding

variable (M : BitMachine.Machine)

abbrev Next := CutoffInputEncoding.nextMachine
abbrev Temp := Fin Next.stackCount ⊕ (CutoffProbeMachine.Stack M ⊕ Unit)
abbrev Stack := Fin 3 ⊕ Temp M

def nextKey (i : Fin Next.stackCount) : Stack M := .inr (.inl i)
def probeKey (i : CutoffProbeMachine.Stack M) : Stack M := .inr (.inr (.inl i))
def scratchKey : Stack M := .inr (.inr (.inr ()))

def nextEmbed : Fin Next.stackCount ↪ Stack M :=
  ⟨nextKey M, by intro a b h; cases h; rfl⟩

inductive CopyPhase where
  | count
  deriving DecidableEq, Fintype

def copySource : CopyPhase → Stack M
  | .count => .inl 2

def copyTarget : CopyPhase → Stack M
  | .count => nextKey M Next.input

def copyEmbed (phase : CopyPhase) : Fin 3 ↪ Stack M where
  toFun i := if i = 0 then copySource M phase else if i = 1 then copyTarget M phase else scratchKey M
  inj' := by
    intro i j h
    cases phase <;> fin_cases i <;> fin_cases j <;>
      simp_all [copySource, copyTarget, nextKey, probeKey, scratchKey]

def packedKey : Stack M := probeKey M (.inl (CutoffProbeMachine.sim M).input)
def capKey : Stack M := probeKey M (.inr (.inr 0))

def packEmbed : Fin 5 ↪ Stack M where
  toFun i := if i = 0 then nextKey M Next.output else if i = 1 then .inl 1
    else if i = 2 then scratchKey M else if i = 3 then packedKey M else capKey M
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [nextKey, scratchKey, packedKey, capKey, probeKey]

inductive Label where
  | copyStart : CopyPhase → Label
  | copy : CopyPhase → BitMachineCopy.Label → Label
  | nextStart
  | next : Fin Next.labelCount → Label
  | packStart
  | pack : CutoffProbePreparation.Label → Label
  | done
  deriving DecidableEq, Fintype

inductive Control where
  | copying : Option Bool → Control
  | next : Fin Next.controlCount → Control
  | packing : Option Bool → Control
  deriving DecidableEq, Fintype

def readCopy : Control → Option Bool
  | .copying b => b
  | .next _ => none
  | .packing _ => none

def readNext : Control → Fin Next.controlCount
  | .copying _ => Next.initial
  | .next v => v
  | .packing _ => Next.initial

def readPack : Control → Option Bool
  | .packing b => b
  | _ => none

def afterCopy : CopyPhase → Label
  | .count => .nextStart

def program : Label → TM2.Stmt (fun _ : Stack M => Bool) Label Control
  | .copyStart phase => load (fun _ => .copying none) (goto (fun _ => .copy phase .scan))
  | .copy phase l => stmt (copyEmbed M phase) (.copy phase) Control.copying readCopy
      (some (afterCopy phase)) (BitMachineCopy.program l)
  | .nextStart => load (fun _ => .next Next.initial) (goto (fun _ => .next Next.start))
  | .next l => stmt (nextEmbed M) Label.next Control.next readNext
      (some .packStart) (Next.program l)
  | .packStart => load (fun _ => .packing none) (goto (fun _ => .pack .scanBits))
  | .pack l => stmt (packEmbed M) Label.pack Control.packing readPack
      (some .done) (CutoffProbePreparation.program l)
  | .done => halt

abbrev Config := TM2.Cfg (fun _ : Stack M => Bool) Label Control

def run (t : ℕ) (c : Config M) := ((advance (program M))^[t]) c

theorem run_add (t u : ℕ) (c : Config M) : run M (t + u) c = run M u (run M t c) := by
  rw [Nat.add_comm]
  exact Function.iterate_add_apply _ _ _ _

theorem copy_phase (phase : CopyPhase) (S : Stack M → List Bool)
    (hscratch : S (scratchKey M) = []) :
    ∃ t ≤ 2 * (S (copySource M phase)).length + 2,
      run M t ⟨some (.copy phase .scan), .copying none, S⟩ =
        ⟨some (afterCopy phase), .copying none,
          Function.update S (copyTarget M phase)
            (S (copySource M phase) ++ S (copyTarget M phase))⟩ := by
  let q := S (copySource M phase)
  let target := S (copyTarget M phase)
  let localStart := BitMachineCopy.cfg (some .scan) none q target []
  let localEnd := BitMachineCopy.cfg none none q (q ++ target) []
  have hr : BitMachineCopy.run (2 * q.length + 2) localStart = localEnd :=
    BitMachineCopy.run_correct none q target
  have hh : (BitMachineCopy.run (2 * q.length + 2) localStart).l = none := by rw [hr]; rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs (copyEmbed M phase) S
    (.copy phase) Control.copying readCopy (fun _ => rfl) (some (afterCopy phase))
    BitMachineCopy.program (program M) (fun _ => rfl) localStart (2 * q.length + 2) hh
  change run M t (BitMachineStackEmbedding.cfg _ _ _ _ _ localStart) =
    BitMachineStackEmbedding.cfg _ _ _ _ _ (BitMachineCopy.run _ localStart) at he
  rw [hr] at he
  have hbank : BitMachineStackEmbedding.bank (copyEmbed M phase) S localStart.stk = S := by
    apply bank_eq_self
    intro i
    fin_cases i <;> simp [localStart, BitMachineCopy.cfg, BitMachineCopy.stackContents,
      copyEmbed, q, target, hscratch]
  have hlocal : localEnd.stk = Function.update localStart.stk 1 (q ++ target) := by
    funext i
    fin_cases i <;> simp [localStart, localEnd, BitMachineCopy.cfg, BitMachineCopy.stackContents]
  have hbank' : BitMachineStackEmbedding.bank (copyEmbed M phase) S localEnd.stk =
      Function.update S (copyTarget M phase) (q ++ target) := by
    rw [hlocal, bank_update, hbank]
    rfl
  refine ⟨t, ht, ?_⟩
  change run M t ⟨some (.copy phase .scan), .copying none,
      bank (copyEmbed M phase) S localStart.stk⟩ =
        ⟨some (afterCopy phase), .copying none, bank (copyEmbed M phase) S localEnd.stk⟩ at he
  rw [hbank, hbank'] at he
  exact he

theorem next_phase (q : List Bool) (S : Stack M → List Bool)
    (hS : ∀ i, S (nextKey M i) = (Next.init q).stk i) :
    ∃ t ≤ 7 * q.length + 12, ∃ c : Next.Config,
      run M t ⟨some (.next Next.start), .next Next.initial, S⟩ =
        ⟨some .packStart, .next c.var, bank (nextEmbed M) S c.stk⟩ ∧
      c.stk Next.output = CutoffInputEncoding.nextInput q ∧
      ∀ i, (c.stk i).length ≤ q.length + (7 * q.length + 12) * Next.pushBound := by
  let bound := 7 * q.length + 12
  let c := Next.run bound (Next.init q)
  obtain ⟨hh, ho⟩ := BitMachine.outputsWithin_at_bound Next (CutoffInputEncoding.next_outputs q)
  have hh' : c.l = none := hh
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs (nextEmbed M) S
    Label.next Control.next readNext (fun _ => rfl) (some .packStart)
    Next.program (program M) (fun _ => rfl) (Next.init q) bound hh'
  have hbank : bank (nextEmbed M) S (Next.init q).stk = S := by
    apply bank_eq_self
    exact fun i => (hS i).symm
  change run M t ⟨some (.next Next.start), .next Next.initial,
      bank (nextEmbed M) S (Next.init q).stk⟩ =
        BitMachineStackEmbedding.cfg (nextEmbed M) S Label.next Control.next
          (some .packStart) c at he
  rw [hbank] at he
  refine ⟨t, ht, c, ?_, ho, ?_⟩
  · simpa only [BitMachineStackEmbedding.cfg, stackCfg, BitMachineInline.cfg, hh'] using he
  · intro i
    have h := BitMachine.run_length Next (Next.init q) i bound
    have hi : ((Next.init q).stk i).length ≤ q.length := by
      simp only [BitMachine.Machine.init]
      split <;> simp
    exact h.trans (Nat.add_le_add_right hi _)

theorem pack_phase (S : Stack M → List Bool)
    (hscratch : S (scratchKey M) = [])
    (hpacked : S (packedKey M) = []) (hcap : S (capKey M) = []) :
    ∃ t ≤ 2 * (S (nextKey M Next.output)).length + 2 * (S (.inl 1)).length + 4,
      run M t ⟨some (.pack .scanBits), .packing none, S⟩ =
        ⟨some .done, .packing none,
          Function.update (Function.update S (packedKey M)
            (BoundedBitMachine.packed (S (.inl 1)).length (S (nextKey M Next.output))))
            (capKey M) (List.replicate (S (.inl 1)).length true)⟩ := by
  let bits := S (nextKey M Next.output)
  let budget := S (.inl 1)
  let localStart := CutoffProbePreparation.cfg (some .scanBits) none bits budget [] [] []
  let localEnd := CutoffProbePreparation.cfg none none bits budget []
    (BoundedBitMachine.packed budget.length bits) (List.replicate budget.length true)
  let bound := 2 * bits.length + 2 * budget.length + 4
  have hr : CutoffProbePreparation.run bound localStart = localEnd :=
    CutoffProbePreparation.run_correct bits budget
  have hh : (CutoffProbePreparation.run bound localStart).l = none := by rw [hr]; rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs (packEmbed M) S
    Label.pack Control.packing readPack (fun _ => rfl) (some .done)
    CutoffProbePreparation.program (program M) (fun _ => rfl) localStart bound hh
  change run M t (BitMachineStackEmbedding.cfg _ _ _ _ _ localStart) =
    BitMachineStackEmbedding.cfg _ _ _ _ _ (CutoffProbePreparation.run _ localStart) at he
  rw [hr] at he
  have hbank : bank (packEmbed M) S localStart.stk = S := by
    apply bank_eq_self
    intro i
    fin_cases i <;> simp [localStart, CutoffProbePreparation.cfg, packEmbed,
      bits, budget, hscratch, hpacked, hcap]
  have hlocal : localEnd.stk = Function.update
      (Function.update localStart.stk 3 (BoundedBitMachine.packed budget.length bits))
      4 (List.replicate budget.length true) := by
    funext i
    fin_cases i <;> simp [localStart, localEnd, CutoffProbePreparation.cfg]
  have hbank' : bank (packEmbed M) S localEnd.stk =
      Function.update (Function.update S (packedKey M)
        (BoundedBitMachine.packed budget.length bits)) (capKey M)
          (List.replicate budget.length true) := by
    rw [hlocal, bank_update, bank_update, hbank]
    rfl
  refine ⟨t, ht, ?_⟩
  change run M t ⟨some (.pack .scanBits), .packing none,
      bank (packEmbed M) S localStart.stk⟩ =
        ⟨some .done, .packing none, bank (packEmbed M) S localEnd.stk⟩ at he
  rw [hbank, hbank'] at he
  exact he

def readyBank (active budget count : List Bool) : Stack M → List Bool :=
  Sum.elim ![active, budget, count] (fun _ => [])

def copiedBank (active budget count : List Bool) : Stack M → List Bool :=
  Function.update (readyBank M active budget count) (nextKey M Next.input) count

def preparedBank (active budget count : List Bool) (c : Next.Config) : Stack M → List Bool :=
  Function.update (Function.update
    (bank (nextEmbed M) (copiedBank M active budget count) c.stk)
    (packedKey M) (BoundedBitMachine.packed budget.length (CutoffInputEncoding.nextInput count)))
    (capKey M) (List.replicate budget.length true)

theorem next_bank_permanent (S : Stack M → List Bool) (T : Fin Next.stackCount → List Bool)
    (i : Fin 3) : bank (nextEmbed M) S T (.inl i) = S (.inl i) := by
  apply bank_outside
  simp [nextEmbed, nextKey]

theorem next_bank_probe (S : Stack M → List Bool) (T : Fin Next.stackCount → List Bool)
    (i : CutoffProbeMachine.Stack M) :
    bank (nextEmbed M) S T (probeKey M i) = S (probeKey M i) := by
  apply bank_outside
  simp [nextEmbed, nextKey, probeKey]

theorem next_bank_scratch (S : Stack M → List Bool) (T : Fin Next.stackCount → List Bool) :
    bank (nextEmbed M) S T (scratchKey M) = S (scratchKey M) := by
  apply bank_outside
  simp [nextEmbed, nextKey, scratchKey]

theorem prepared_permanent (active budget count : List Bool) (c : Next.Config) (i : Fin 3) :
    preparedBank M active budget count c (.inl i) = ![active,budget,count] i := by
  simp [preparedBank, packedKey, capKey, probeKey, next_bank_permanent,
    copiedBank, nextKey, readyBank, -Sum.elim_update_right]

theorem prepared_scratch (active budget count : List Bool) (c : Next.Config) :
    preparedBank M active budget count c (scratchKey M) = [] := by
  unfold preparedBank
  rw [Function.update_of_ne (by simp [scratchKey, capKey, probeKey]),
    Function.update_of_ne (by simp [scratchKey, packedKey, probeKey]), next_bank_scratch]
  simp [copiedBank, nextKey, scratchKey, readyBank, -Sum.elim_update_right]

theorem prepared_next (active budget count : List Bool) (c : Next.Config)
    (i : Fin Next.stackCount) :
    preparedBank M active budget count c (nextKey M i) = c.stk i := by
  simp only [preparedBank]
  rw [Function.update_of_ne (by simp [nextKey, capKey, probeKey]),
    Function.update_of_ne (by simp [nextKey, packedKey, probeKey])]
  exact bank_at (nextEmbed M) _ _ i

theorem prepared_probe (active budget count : List Bool) (c : Next.Config)
    (i : CutoffProbeMachine.Stack M) :
    preparedBank M active budget count c (probeKey M i) =
      (CutoffProbeMachine.start M
        (BoundedBitMachine.packed budget.length (CutoffInputEncoding.nextInput count))
        (List.replicate budget.length true)).stk i := by
  rw [CutoffProbeMachine.start_eq]
  unfold preparedBank
  cases i with
  | inl i =>
      rw [Function.update_of_ne (by simp [probeKey, capKey])]
      by_cases h : i = (CutoffProbeMachine.sim M).input
      · subst i
        simp [packedKey, CutoffProbeMachine.start, CutoffProbeMachine.cfg,
          BitMachine.Machine.init]
      · rw [Function.update_of_ne (by simpa [probeKey, packedKey] using h), next_bank_probe]
        simp [copiedBank, nextKey, probeKey, readyBank, CutoffProbeMachine.start,
          CutoffProbeMachine.cfg, BitMachine.Machine.init, h, -Sum.elim_update_right]
  | inr i =>
      cases i with
      | inl i =>
          rw [Function.update_of_ne (by simp [probeKey, capKey]),
            Function.update_of_ne (by simp [probeKey, packedKey]), next_bank_probe]
          fin_cases i <;> simp [copiedBank, nextKey, probeKey, readyBank,
            CutoffProbeMachine.start, CutoffProbeMachine.cfg, CutoffProbeMachine.bank,
            -Sum.elim_update_right]
      | inr i =>
          by_cases h : i = 0
          · subst i
            simp [capKey, CutoffProbeMachine.cfg, CutoffProbeMachine.bank]
          · rw [Function.update_of_ne (by simpa [probeKey, capKey] using h),
              Function.update_of_ne (by simp [probeKey, packedKey]), next_bank_probe]
            fin_cases i <;> simp_all [copiedBank, nextKey, probeKey, readyBank,
              CutoffProbeMachine.cfg, CutoffProbeMachine.bank, -Sum.elim_update_right]

theorem preparation_run (active budget count : List Bool) :
    ∃ t ≤ 20 * (count.length + budget.length + 2), ∃ c : Next.Config,
      run M t ⟨some (.copyStart .count), .copying none, readyBank M active budget count⟩ =
        ⟨none, .packing none, preparedBank M active budget count c⟩ ∧
      (∀ i, (c.stk i).length ≤ count.length + (7 * count.length + 12) * Next.pushBound) := by
  have hs : readyBank M active budget count (scratchKey M) = [] := rfl
  obtain ⟨t₁, ht₁, h₁⟩ := copy_phase M .count (readyBank M active budget count) hs
  have h₁' : run M t₁ ⟨some (.copy .count .scan), .copying none,
      readyBank M active budget count⟩ =
      ⟨some .nextStart, .copying none, copiedBank M active budget count⟩ := by
    simpa only [afterCopy, copySource, copyTarget, readyBank, Sum.elim_inl,
      Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero,
      nextKey, Sum.elim_inr, List.append_nil, copiedBank] using h₁
  have hi : ∀ i, copiedBank M active budget count (nextKey M i) = (Next.init count).stk i := by
    intro i
    by_cases h : i = Next.input
    · subst i; simp [copiedBank, BitMachine.Machine.init]
    · have hn : nextKey M i ≠ nextKey M Next.input := by simpa [nextKey] using h
      simp only [copiedBank, Function.update_of_ne hn, BitMachine.Machine.init, h, if_false]
      rfl
  obtain ⟨t₂, ht₂, c, h₂, ho, hc⟩ := next_phase M count (copiedBank M active budget count) hi
  let S := bank (nextEmbed M) (copiedBank M active budget count) c.stk
  have hss : S (scratchKey M) = [] := by
    dsimp only [S]
    rw [next_bank_scratch]
    simp [copiedBank, scratchKey, nextKey, readyBank, -Sum.elim_update_right]
  have hsp : S (packedKey M) = [] := by
    change S (probeKey M _) = []
    dsimp only [S]
    rw [next_bank_probe]
    simp [copiedBank, probeKey, nextKey, readyBank, -Sum.elim_update_right]
  have hsc : S (capKey M) = [] := by
    change S (probeKey M _) = []
    dsimp only [S]
    rw [next_bank_probe]
    simp [copiedBank, probeKey, nextKey, readyBank, -Sum.elim_update_right]
  have hsb : S (.inl 1) = budget := by
    dsimp only [S]
    rw [next_bank_permanent]
    simp [copiedBank, nextKey, readyBank, -Sum.elim_update_right]
  have hso : S (nextKey M Next.output) = CutoffInputEncoding.nextInput count :=
    (bank_at (nextEmbed M) _ _ _).trans ho
  obtain ⟨t₃, ht₃, h₃⟩ := pack_phase M S hss hsp hsc
  rw [hsb, hso] at h₃ ht₃
  have h₃' : run M t₃ ⟨some (.pack .scanBits), .packing none, S⟩ =
      ⟨some .done, .packing none, preparedBank M active budget count c⟩ := h₃
  have hstart : run M 1 ⟨some (.copyStart .count), .copying none,
      readyBank M active budget count⟩ =
      ⟨some (.copy .count .scan), .copying none, readyBank M active budget count⟩ := rfl
  have hnext : run M 1 ⟨some .nextStart, .copying none, copiedBank M active budget count⟩ =
      ⟨some (.next Next.start), .next Next.initial, copiedBank M active budget count⟩ := rfl
  have hpack : run M 1 ⟨some .packStart, .next c.var, S⟩ =
      ⟨some (.pack .scanBits), .packing none, S⟩ := rfl
  have hdone : run M 1 ⟨some .done, .packing none, preparedBank M active budget count c⟩ =
      ⟨none, .packing none, preparedBank M active budget count c⟩ := rfl
  refine ⟨1 + t₁ + 1 + t₂ + 1 + t₃ + 1, ?_, c, ?_, hc⟩
  · have hlen : (CutoffInputEncoding.nextInput count).length ≤ 2 * count.length + 4 := by
      simp only [CutoffInputEncoding.nextInput, CutoffInputEncoding.word,
        List.length_append, CutoffInputEncoding.digits_length, List.length_cons, List.length_nil]
      have h := CutoffInputEncoding.successor_length_le count
      omega
    have ht₁' : t₁ ≤ 2 * count.length + 2 := ht₁
    omega
  · rw [run_add, run_add, run_add, run_add, run_add, run_add,
      hstart, h₁', hnext, h₂, hpack, h₃', hdone]

end
end EthInapproximability.CurrentPaper.ClockInputPreparation
