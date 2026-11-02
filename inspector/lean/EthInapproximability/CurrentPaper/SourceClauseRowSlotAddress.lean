import EthInapproximability.CurrentPaper.SourceClauseRowSchedule

/-!
# Physical unary source-row clause slot

For unary `n`, processed row `r`, and tuple ordinal `k`, the two literal
multiply-add machines produce `n*(1+a*a)` and `r*(a^q)+k`. An explicit
transfer places the first output as the second machine's output suffix. The
second then prepends its address, leaving exactly the source clause slot
`n+n*a*a+r*a^q+k` in unary. Alphabet size and arity are fixed parameters.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowSlotAddress

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := Fin 6 ⊕ (Fin 6 ⊕ Fin 1)
def firstEmbedding : Fin 6 ↪ Stack := Function.Embedding.inl
def secondEmbedding : Fin 6 ↪ Stack where
  toFun k := .inr (.inl k)
  inj' := by intro x y h; exact Sum.inl.inj (Sum.inr.inj h)

def source : Stack := .inl 5
def temp : Stack := .inr (.inr 0)
def target : Stack := .inr (.inl 5)
def targets : List Stack := [target]

inductive CopyLabel where
  | scan | restore | finish
  deriving DecidableEq, Fintype

def copyProgram : CopyLabel → TM2.Stmt (fun _ : Stack => Bool) CopyLabel
    (Unit × Option Bool)
  | .scan => BitMachineBroadcast.scanStep source temp .scan .restore
  | .restore => BitMachineBroadcast.restoreStep temp targets .restore .finish
  | .finish => .halt

def firstSize (n a : ℕ) := n * (1 + a * a)
def secondSize (r a q k : ℕ) := r * a ^ q + k
def slot (n r a q k : ℕ) := n + n * (a * a) + r * a ^ q + k

def initial (n r a q k : ℕ) : Stack → List Bool :=
  Sum.elim
    (MatrixAddressMachine.cfg (some .outer) false
      (List.replicate n true) (List.replicate (1 + a * a) true)
      [] [] [] []).stk
    (Sum.elim
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate r true) (List.replicate (a ^ q) true)
        (List.replicate k true) [] [] []).stk
      (fun _ => []))

def firstDone (n r a q k : ℕ) : Stack → List Bool :=
  Sum.elim
    (MatrixAddressMachine.cfg none false
      (List.replicate n true) (List.replicate (1 + a * a) true)
      [] [] [] (List.replicate (firstSize n a) true)).stk
    (Sum.elim
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate r true) (List.replicate (a ^ q) true)
        (List.replicate k true) [] [] []).stk
      (fun _ => []))

def transferred (n r a q k : ℕ) : Stack → List Bool :=
  BitMachineBroadcast.copied source temp targets
    (List.replicate (firstSize n a) true) (firstDone n r a q k)

noncomputable def finalBank (n r a q k : ℕ) : Stack → List Bool :=
  bank secondEmbedding (transferred n r a q k)
    (MatrixAddressMachine.cfg none false
      (List.replicate r true) (List.replicate (a ^ q) true)
      (List.replicate k true) [] []
      (List.replicate (secondSize r a q k) true ++
        List.replicate (firstSize n a) true)).stk

def firstProgram (l : MatrixAddressMachine.Label) :=
  stackStmt firstEmbedding (MatrixAddressMachine.program l)
def secondProgram (l : MatrixAddressMachine.Label) :=
  stackStmt secondEmbedding (MatrixAddressMachine.program l)

def program := BitMachineRawSequence.program
  (BitMachineRawSequence.program firstProgram copyProgram CopyLabel.scan
    false ((), none))
  secondProgram
  MatrixAddressMachine.Label.outer (false, ((), none)) false

theorem first_initial (n r a q k : ℕ) :
    bank firstEmbedding (initial n r a q k)
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate n true) (List.replicate (1 + a * a) true)
        [] [] [] []).stk = initial n r a q k := by
  apply bank_eq_self
  intro i
  rfl

theorem first_final (n r a q k : ℕ) :
    bank firstEmbedding (initial n r a q k)
      (MatrixAddressMachine.cfg none false
        (List.replicate n true) (List.replicate (1 + a * a) true)
        [] [] [] (List.replicate (firstSize n a) true)).stk =
      firstDone n r a q k := by
  funext i
  cases i with
  | inl i => exact bank_at firstEmbedding _ _ i
  | inr i =>
      rw [bank_outside]
      · rfl
      · intro ⟨u, h⟩; cases h

theorem first_run (n r a q k : ℕ) :
    ((advance firstProgram)^[MatrixAddressMachine.exactTime n (1+a*a) 0])
      (⟨some .outer, false, initial n r a q k⟩ :
        TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool) =
      ⟨none, false, firstDone n r a q k⟩ := by
  have h := MatrixAddressMachine.address_run n (1+a*a) 0 false []
  simp only [MatrixAddressMachine.run, List.replicate_zero,
    Nat.add_zero, List.append_nil, firstSize] at h
  have he := BitMachineStackRun.run firstEmbedding (initial n r a q k)
    MatrixAddressMachine.program
    (MatrixAddressMachine.cfg (some .outer) false
      (List.replicate n true) (List.replicate (1 + a*a) true)
      [] [] [] []) (MatrixAddressMachine.exactTime n (1+a*a) 0)
  rw [h] at he
  simp only [stackCfg] at he
  change ((advance firstProgram)^[MatrixAddressMachine.exactTime n (1+a*a) 0])
    (⟨some .outer, false,
      bank firstEmbedding (initial n r a q k)
        (MatrixAddressMachine.cfg (some .outer) false
          (List.replicate n true) (List.replicate (1+a*a) true)
          [] [] [] []).stk⟩ :
      TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool) =
    ⟨none, false,
      bank firstEmbedding (initial n r a q k)
        (MatrixAddressMachine.cfg none false
          (List.replicate n true) (List.replicate (1+a*a) true)
          [] [] [] (List.replicate (firstSize n a) true)).stk⟩ at he
  rw [first_initial, first_final] at he
  exact he

theorem copy_run (n r a q k : ℕ) :
    ((advance copyProgram)^[2 * firstSize n a + 3])
      (⟨some .scan, ((), none), firstDone n r a q k⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)) =
      ⟨none, ((), none), transferred n r a q k⟩ := by
  have h := BitMachineBroadcast.broadcast_run copyProgram source temp
    (by decide) targets (by simp [targets])
    (by simp [source, targets, target])
    (by simp [temp, targets, target])
    .scan .restore .finish rfl rfl () none
    (List.replicate (firstSize n a) true) (firstDone n r a q k) rfl rfl
  rw [show 2 * firstSize n a + 3 =
    (2 * (List.replicate (firstSize n a) true).length + 2) + 1 by simp,
    Function.iterate_succ_apply']
  change advance copyProgram
    (BitMachineBroadcast.run copyProgram
      (2 * (List.replicate (firstSize n a) true).length + 2)
      (⟨some .scan, ((), none), firstDone n r a q k⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool))) = _
  rw [h]
  simp [advance, TM2.step, copyProgram, transferred]

theorem second_initial (n r a q k : ℕ) :
    bank secondEmbedding (transferred n r a q k)
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate r true) (List.replicate (a ^ q) true)
        (List.replicate k true) [] []
        (List.replicate (firstSize n a) true)).stk =
      transferred n r a q k := by
  apply bank_eq_self
  intro i
  fin_cases i <;>
    simp [transferred, BitMachineBroadcast.copied, source, temp, target,
      secondEmbedding,
      targets, firstDone, MatrixAddressMachine.cfg]

theorem second_run (n r a q k : ℕ) :
    ((advance secondProgram)^[MatrixAddressMachine.exactTime r (a^q) k])
      (⟨some .outer, false, transferred n r a q k⟩ :
        TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool) =
      ⟨none, false, finalBank n r a q k⟩ := by
  have h := MatrixAddressMachine.address_run r (a^q) k false
    (List.replicate (firstSize n a) true)
  change ((advance MatrixAddressMachine.program)^[MatrixAddressMachine.exactTime r (a^q) k])
    (MatrixAddressMachine.cfg (some .outer) false
      (List.replicate r true) (List.replicate (a^q) true)
      (List.replicate k true) [] []
      (List.replicate (firstSize n a) true)) =
    MatrixAddressMachine.cfg none false
      (List.replicate r true) (List.replicate (a^q) true)
      (List.replicate k true) [] []
      (List.replicate (secondSize r a q k) true ++
        List.replicate (firstSize n a) true) at h
  have he := BitMachineStackRun.run secondEmbedding (transferred n r a q k)
    MatrixAddressMachine.program
    (MatrixAddressMachine.cfg (some .outer) false
      (List.replicate r true) (List.replicate (a ^ q) true)
      (List.replicate k true) [] []
      (List.replicate (firstSize n a) true))
    (MatrixAddressMachine.exactTime r (a^q) k)
  rw [h] at he
  simp only [stackCfg, second_initial, finalBank] at he
  exact he

def cost (n r a q k : ℕ) : ℕ :=
  MatrixAddressMachine.exactTime n (1+a*a) 0 +
  (2 * firstSize n a + 3) +
  MatrixAddressMachine.exactTime r (a^q) k + 2

theorem run (n r a q k : ℕ) :
    ∃ T ≤ cost n r a q k,
      ((advance program)^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)),
          ((false, ((), none)), false), initial n r a q k⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label MatrixAddressMachine.Label CopyLabel)
              MatrixAddressMachine.Label)
            ((Bool × (Unit × Option Bool)) × Bool)) =
        ⟨none, ((false, ((), none)), false), finalBank n r a q k⟩ := by
  obtain ⟨tab, htab, hab⟩ := BitMachineRawSequence.runs
    firstProgram copyProgram MatrixAddressMachine.Label.outer CopyLabel.scan
    false false ((), none) ((), none)
    (initial n r a q k) (firstDone n r a q k) (transferred n r a q k)
    (MatrixAddressMachine.exactTime n (1+a*a) 0) (2 * firstSize n a + 3)
    (first_run n r a q k) (copy_run n r a q k)
  obtain ⟨T, hT, hrun⟩ := BitMachineRawSequence.runs
    (BitMachineRawSequence.program firstProgram copyProgram CopyLabel.scan
      false ((), none)) secondProgram
    (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
    MatrixAddressMachine.Label.outer
    (false, ((), none)) (false, ((), none)) false false
    (initial n r a q k) (transferred n r a q k) (finalBank n r a q k)
    tab (MatrixAddressMachine.exactTime r (a^q) k) hab (second_run n r a q k)
  exact ⟨T, by dsimp [cost] at *; omega, hrun⟩

theorem final_slot (n r a q k : ℕ) :
    finalBank n r a q k (.inr (.inl 5)) =
      List.replicate (slot n r a q k) true := by
  change finalBank n r a q k (secondEmbedding 5) = _
  rw [finalBank, bank_at]
  change List.replicate (secondSize r a q k) true ++
    List.replicate (firstSize n a) true =
      List.replicate (slot n r a q k) true
  rw [← List.replicate_add]
  congr 1
  dsimp [firstSize, secondSize, slot]
  ring

end EthInapproximability.CurrentPaper.SourceClauseRowSlotAddress
