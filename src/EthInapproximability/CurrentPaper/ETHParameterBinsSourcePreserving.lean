import EthInapproximability.CurrentPaper.ETHParameterBinsStandalone
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! A physical source-preserving wrapper around the fixed bin chain. The
source word is copied into an initially empty bin-machine input; the
source-preserving copy and complete bin chain are one sequenced program. -/

namespace EthInapproximability.CurrentPaper.ETHBinsSourcePreservingScratch

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

set_option maxHeartbeats 1000000

abbrev Stack := Fin 1 ⊕ (Fin ETHBinsStandaloneScratch.machine.stackCount ⊕ Unit)
abbrev Label := BitMachineRawSequence.Label BitMachineCopy.Label
  (Fin ETHBinsStandaloneScratch.machine.labelCount)
abbrev Control := Option Bool × Fin ETHBinsStandaloneScratch.machine.controlCount

def sourceKey : Stack := .inl 0
def inputKey : Stack := .inr (.inl ETHBinsStandaloneScratch.machine.input)
def outputKey : Stack := .inr (.inl ETHBinsStandaloneScratch.machine.output)
def scratchKey : Stack := .inr (.inr ())

def copyEmbed : Fin 3 ↪ Stack where
  toFun := ![sourceKey,inputKey,scratchKey]
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;>
    simp [sourceKey,inputKey,scratchKey] at h ⊢

def binEmbed : Fin ETHBinsStandaloneScratch.machine.stackCount ↪ Stack :=
  ⟨fun k => .inr (.inl k), by intro a b h; exact Sum.inl_injective (Sum.inr_injective h)⟩

def copyProgram := fun l => stackStmt copyEmbed (BitMachineCopy.program l)
def binProgram := fun l => stackStmt binEmbed (ETHBinsStandaloneScratch.machine.program l)
def program := BitMachineRawSequence.program copyProgram binProgram
  ETHBinsStandaloneScratch.machine.start none ETHBinsStandaloneScratch.machine.initial

def initialBank (n : ℕ) : Stack → List Bool :=
  bank copyEmbed (fun _ => [])
    (BitMachineCopy.cfg (some .scan) none (ETHBinsStandaloneScratch.unary n) [] []).stk
def afterCopyBank (n : ℕ) : Stack → List Bool :=
  bank copyEmbed (fun _ => [])
    (BitMachineCopy.cfg none none (ETHBinsStandaloneScratch.unary n) (ETHBinsStandaloneScratch.unary n) []).stk

def totalTime (n : ℕ) : ℕ := 2*n+2 + ETHBinsStandaloneScratch.totalTime n + 1

theorem initial_source (n : ℕ) : initialBank n sourceKey = ETHBinsStandaloneScratch.unary n := by
  change bank copyEmbed (fun _ => []) _ (copyEmbed 0) = _
  rw [bank_at]
  rfl

theorem initial_other (n : ℕ) (k : Stack) (hk : k ≠ sourceKey) :
    initialBank n k = [] := by
  by_cases h : ∃ j : Fin 3, copyEmbed j = k
  · obtain ⟨j,rfl⟩ := h
    fin_cases j
    · exact (hk rfl).elim
    · change bank copyEmbed (fun _ => []) _ (copyEmbed 1) = _
      rw [bank_at]; rfl
    · change bank copyEmbed (fun _ => []) _ (copyEmbed 2) = _
      rw [bank_at]; rfl
  · exact bank_outside copyEmbed (fun _ => []) _ k h

theorem initial_spec (n : ℕ) :
    initialBank n = fun k => if k = sourceKey then ETHBinsStandaloneScratch.unary n else [] := by
  funext k
  by_cases hk : k = sourceKey
  · subst k; simpa using initial_source n
  · simpa [hk] using initial_other n k hk

theorem after_copy_source (n : ℕ) :
    afterCopyBank n sourceKey = ETHBinsStandaloneScratch.unary n := by
  change bank copyEmbed (fun _ => []) _ (copyEmbed 0) = _
  rw [bank_at]; rfl

theorem after_copy_restrict (n : ℕ) :
    (ETHBinsStandaloneScratch.machine.init (ETHBinsStandaloneScratch.unary n)).stk =
      fun k => afterCopyBank n (binEmbed k) := by
  funext k
  by_cases hk : k = ETHBinsStandaloneScratch.machine.input
  · subst k
    change (ETHBinsStandaloneScratch.machine.init (ETHBinsStandaloneScratch.unary n)).stk ETHBinsStandaloneScratch.machine.input =
      bank copyEmbed (fun _ => [])
        (BitMachineCopy.cfg none none (ETHBinsStandaloneScratch.unary n)
          (ETHBinsStandaloneScratch.unary n) []).stk (copyEmbed 1)
    rw [bank_at]
    simp [BitMachine.Machine.init,BitMachineCopy.cfg]
  · have hout : ¬ ∃ j : Fin 3, copyEmbed j = binEmbed k := by
      rintro ⟨j,hj⟩
      fin_cases j
      · simp [copyEmbed,binEmbed,sourceKey] at hj
      · simp [copyEmbed,binEmbed,inputKey] at hj
        exact hk hj.symm
      · simp [copyEmbed,binEmbed,scratchKey] at hj
    change (ETHBinsStandaloneScratch.machine.init (ETHBinsStandaloneScratch.unary n)).stk k =
      bank copyEmbed (fun _ => []) _ (binEmbed k)
    rw [bank_outside copyEmbed (fun _ => []) _ _ hout]
    simp [BitMachine.Machine.init,hk]

/-- Entire physical terminal bin bank, including source preservation. -/
theorem bins_run (n : ℕ) :
    ∃ t ≤ totalTime n, ∃ v : Fin ETHBinsStandaloneScratch.machine.controlCount,
      ∃ F : Stack → List Bool,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none,ETHBinsStandaloneScratch.machine.initial),initialBank n⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none,(none,v),F⟩ ∧
      F sourceKey = ETHBinsStandaloneScratch.unary n ∧
      F outputKey = ETHBinsStandaloneScratch.unary (ETHBinsStandaloneScratch.bins n) := by
  have hc := BitMachineCopy.run_correct none (ETHBinsStandaloneScratch.unary n) []
  have hc' :
      ((advance copyProgram)^[2*n+2])
        (⟨some BitMachineCopy.Label.scan,none,initialBank n⟩ :
          TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
        ⟨none,none,afterCopyBank n⟩ := by
    have he := BitMachineStackRun.run copyEmbed (fun _ => [])
      BitMachineCopy.program
      (BitMachineCopy.cfg (some .scan) none (ETHBinsStandaloneScratch.unary n) [] []) (2*n+2)
    have hc0 : ((advance BitMachineCopy.program)^[2*n+2])
        (BitMachineCopy.cfg (some .scan) none (ETHBinsStandaloneScratch.unary n) [] []) =
        BitMachineCopy.cfg none none (ETHBinsStandaloneScratch.unary n)
          (ETHBinsStandaloneScratch.unary n) [] := by
      simpa only [BitMachineCopy.run,ETHBinsStandaloneScratch.unary,
        List.length_replicate,List.append_nil] using hc
    rw [hc0] at he
    simpa only [copyProgram,stackCfg,initialBank,afterCopyBank,
      List.length_replicate,ETHBinsStandaloneScratch.unary] using he
  obtain ⟨tb,htb,hhalt,hout⟩ := ETHBinsStandaloneScratch.bins_outputs n
  let c := ETHBinsStandaloneScratch.machine.run tb (ETHBinsStandaloneScratch.machine.init (ETHBinsStandaloneScratch.unary n))
  have hrun : ((advance ETHBinsStandaloneScratch.machine.program)^[tb])
      (ETHBinsStandaloneScratch.machine.init (ETHBinsStandaloneScratch.unary n)) = c := rfl
  have hb :
      ((advance binProgram)^[tb])
        (⟨some ETHBinsStandaloneScratch.machine.start,ETHBinsStandaloneScratch.machine.initial,afterCopyBank n⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (Fin ETHBinsStandaloneScratch.machine.labelCount) (Fin ETHBinsStandaloneScratch.machine.controlCount)) =
        ⟨none,c.var,bank binEmbed (afterCopyBank n) c.stk⟩ := by
    have he := BitMachineStackRun.run binEmbed (afterCopyBank n)
      ETHBinsStandaloneScratch.machine.program (ETHBinsStandaloneScratch.machine.init (ETHBinsStandaloneScratch.unary n)) tb
    have hbase := bank_eq_self binEmbed (afterCopyBank n)
      (ETHBinsStandaloneScratch.machine.init (ETHBinsStandaloneScratch.unary n)).stk
      (fun k => congrFun (after_copy_restrict n) k)
    rw [hrun] at he
    change ((advance binProgram)^[tb])
      ⟨some ETHBinsStandaloneScratch.machine.start,
        ETHBinsStandaloneScratch.machine.initial,
        bank binEmbed (afterCopyBank n)
          (ETHBinsStandaloneScratch.machine.init (ETHBinsStandaloneScratch.unary n)).stk⟩ =
      ⟨c.l,c.var,bank binEmbed (afterCopyBank n) c.stk⟩ at he
    rw [hbase] at he
    have hcl : c.l = none := hhalt
    simpa only [hcl] using he
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    copyProgram binProgram BitMachineCopy.Label.scan ETHBinsStandaloneScratch.machine.start
    none none ETHBinsStandaloneScratch.machine.initial c.var
    (initialBank n) (afterCopyBank n)
    (bank binEmbed (afterCopyBank n) c.stk)
    (2*n+2) tb hc' hb
  refine ⟨t, ?_, c.var, bank binEmbed (afterCopyBank n) c.stk,
    ?_, ?_, ?_⟩
  · dsimp [totalTime]
    omega
  · simpa only [program] using hr
  · have houtside : ¬ ∃ k, binEmbed k = sourceKey := by
      rintro ⟨k,hk⟩
      simp [binEmbed,sourceKey] at hk
    rw [bank_outside binEmbed _ _ _ houtside]
    exact after_copy_source n
  · change bank binEmbed (afterCopyBank n) c.stk
      (binEmbed ETHBinsStandaloneScratch.machine.output) = _
    rw [bank_at]
    exact hout

end
end EthInapproximability.CurrentPaper.ETHBinsSourcePreservingScratch
