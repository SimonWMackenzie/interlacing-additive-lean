import Paper2.CodeRecursiveLoop
import Paper2.CodeAtomCountInput

/-! First physical seed phases: ticket p from the public delimiter-free
count, followed by a source-preserving copy of that count for row syntax. -/

set_option maxHeartbeats 1000000

namespace Paper2.CodeRecursiveSeedPrep

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.CodeRecursiveLoop

def publicBase (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    Stack → List Bool :=
  fun i => if i = 12 then List.replicate q₂ true else
    if i = 16 then List.replicate q₁ true else
    if i = 17 then List.replicate s true else
    if i = 18 then List.replicate n true else
    if i = 31 then List.replicate w true else
    if i = 32 then List.replicate Q true else
    if i = 63 then List.replicate p true else
    if i = 64 then fuel else []

def afterTicket (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    Stack → List Bool :=
  Function.update (publicBase n s q₁ q₂ w Q p fuel) 33
    (encodeCode (.ticket p))

def afterCountCopy (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    Stack → List Bool :=
  Function.update (afterTicket n s q₁ q₂ w Q p fuel) 41
    (List.replicate p true)

def ticketIndex : Fin 3 ↪ Stack where
  toFun i := ![63,33,44] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def ticketProgram : CodeAtomCountInput.Label →
    TM2.Stmt (fun _ : Stack => Bool)
      CodeAtomCountInput.Label CodeAtomCountInput.Control :=
  fun l => BitMachineStackEmbedding.stackStmt ticketIndex
    (CodeAtomCountInput.program l)

theorem ticket_initial_bank (n s q₁ q₂ w Q p : Nat)
    (fuel : List Bool) :
    BitMachineStackEmbedding.bank ticketIndex
      (publicBase n s q₁ q₂ w Q p fuel)
      (CodeAtomCountInput.initial p).stk =
    publicBase n s q₁ q₂ w Q p fuel := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i <;> simp [ticketIndex, CodeAtomCountInput.initial,
    BitMachineCopy.cfg, BitMachineCopy.stackContents, publicBase]

theorem ticket_result_bank (n s q₁ q₂ w Q p : Nat)
    (fuel : List Bool) :
    BitMachineStackEmbedding.bank ticketIndex
      (publicBase n s q₁ q₂ w Q p fuel)
      (CodeAtomCountInput.final p).stk =
    afterTicket n s q₁ q₂ w Q p fuel := by
  have hstk : (CodeAtomCountInput.final p).stk =
      Function.update (CodeAtomCountInput.initial p).stk
        (1 : Fin 3) (encodeCode (.ticket p)) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update, ticket_initial_bank]
  rfl

theorem ticket_run (n s q₁ q₂ w Q p : Nat)
    (fuel : List Bool) :
    ∃ t ≤ 2*p+8,
      ((advance ticketProgram)^[t])
        (⟨(CodeAtomCountInput.initial p).l,
          (CodeAtomCountInput.initial p).var,
          publicBase n s q₁ q₂ w Q p fuel⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (CodeAtomCountInput.final p).var,
          afterTicket n s q₁ q₂ w Q p fuel⟩ := by
  obtain ⟨t,ht,hr⟩ := CodeAtomCountInput.run_ticket_count p
  have h := BitMachineStackRun.run ticketIndex
    (publicBase n s q₁ q₂ w Q p fuel)
    CodeAtomCountInput.program (CodeAtomCountInput.initial p) t
  rw [hr] at h
  exact ⟨t,ht,by
    simpa only [ticketProgram, BitMachineStackEmbedding.stackCfg,
      ticket_initial_bank, ticket_result_bank] using h⟩

def countIndex : Fin 3 ↪ Stack where
  toFun i := ![63,41,42] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def countProgram : BitMachineCopy.Label →
    TM2.Stmt (fun _ : Stack => Bool)
      BitMachineCopy.Label (Option Bool) :=
  fun l => BitMachineStackEmbedding.stackStmt countIndex
    (BitMachineCopy.program l)

theorem count_initial_bank (n s q₁ q₂ w Q p : Nat)
    (fuel : List Bool) :
    BitMachineStackEmbedding.bank countIndex
      (afterTicket n s q₁ q₂ w Q p fuel)
      (BitMachineCopy.cfg (some .scan) none
        (List.replicate p true) [] []).stk =
    afterTicket n s q₁ q₂ w Q p fuel := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i <;> simp [countIndex, afterTicket, publicBase,
    BitMachineCopy.cfg, BitMachineCopy.stackContents]

theorem count_result_bank (n s q₁ q₂ w Q p : Nat)
    (fuel : List Bool) :
    BitMachineStackEmbedding.bank countIndex
      (afterTicket n s q₁ q₂ w Q p fuel)
      (BitMachineCopy.cfg none none
        (List.replicate p true) (List.replicate p true) []).stk =
    afterCountCopy n s q₁ q₂ w Q p fuel := by
  have hstk :
      (BitMachineCopy.cfg none none
        (List.replicate p true) (List.replicate p true) []).stk =
      Function.update
        (BitMachineCopy.cfg (some .scan) none
          (List.replicate p true) [] []).stk
        (1 : Fin 3) (List.replicate p true) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update, count_initial_bank]
  rfl

theorem count_run (n s q₁ q₂ w Q p : Nat)
    (fuel : List Bool) :
    ((advance countProgram)^[2*p+2])
      (⟨some .scan, none,
        afterTicket n s q₁ q₂ w Q p fuel⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, afterCountCopy n s q₁ q₂ w Q p fuel⟩ := by
  have h := BitMachineStackRun.run countIndex
    (afterTicket n s q₁ q₂ w Q p fuel)
    BitMachineCopy.program
    (BitMachineCopy.cfg (some .scan) none
      (List.replicate p true) [] []) (2*p+2)
  have hc := BitMachineCopy.run_correct none
    (List.replicate p true) []
  simp only [List.length_replicate, List.append_nil] at hc
  rw [← BitMachineCopy.run, hc] at h
  simpa only [countProgram, BitMachineStackEmbedding.stackCfg,
    count_initial_bank, count_result_bank] using h

def ticketStart : CodeAtomCountInput.Label :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel CodeAtomCountInput.InitLabel.write)

def program := BitMachineRawSequence.program ticketProgram countProgram
  BitMachineCopy.Label.scan (((),none),()) none

theorem run_exact (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    ∃ t ≤ (2*p+8)+(2*p+2)+1,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel ticketStart),
          ((((),none),()),none),
          publicBase n s q₁ q₂ w Q p fuel⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((((),none),()),none),
          afterCountCopy n s q₁ q₂ w Q p fuel⟩ := by
  obtain ⟨ta,hta,ha⟩ := ticket_run n s q₁ q₂ w Q p fuel
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    ticketProgram countProgram
    ticketStart .scan
    (((),none),()) (((),none),()) none none
    (publicBase n s q₁ q₂ w Q p fuel)
    (afterTicket n s q₁ q₂ w Q p fuel)
    (afterCountCopy n s q₁ q₂ w Q p fuel)
    ta (2*p+2) (by simpa [CodeAtomCountInput.initial] using ha)
    (count_run n s q₁ q₂ w Q p fuel)
  exact ⟨t, by omega, hr⟩

#print axioms run_exact

end Paper2.CodeRecursiveSeedPrep
