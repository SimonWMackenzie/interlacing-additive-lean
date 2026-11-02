import EthInapproximability.CurrentPaper.MatrixAddressMachine
import EthInapproximability.CurrentPaper.SourceUnaryBinaryCall
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-!
# Physical multiply-add followed by canonical binary label writing

Source: frozen v8 `06-eth.tex`, Boolean source conversion and variable labels.
The three unary arguments are preserved. Multiplication, conversion, cleanup,
and the connecting transition are all executed by finite Boolean-stack code.
This is an arithmetic subroutine, not a claim that the whole source converter
has been implemented.
-/

namespace EthInapproximability.CurrentPaper.SourceLabelAddressMachine

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable abbrev counter := SourceUnaryBinaryCall.counter
abbrev Stack := Fin 5 ⊕ BitMachineIteration.Stack counter

def addressEmbedding : Fin 6 ↪ Stack where
  toFun k := if h : k.val < 5 then .inl ⟨k.val, h⟩ else .inr (.inr 0)
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

def binaryEmbedding : BitMachineIteration.Stack counter ↪ Stack :=
  Function.Embedding.inr

def ambient (r w c : ℕ) (S : BitMachineIteration.Stack counter → List Bool) :
    Stack → List Bool :=
  Sum.elim ![List.replicate r true, List.replicate w true,
    List.replicate c true, [], []] S

def inputs (r w c : ℕ) : Stack → List Bool := ambient r w c (fun _ => [])

noncomputable def outputs (r w c : ℕ) : Stack → List Bool :=
  ambient r w c (BitMachineIteration.finished counter (r * w + c).bits).stk

def addressProgram (l : MatrixAddressMachine.Label) :=
  stackStmt addressEmbedding (MatrixAddressMachine.program l)

noncomputable def binaryProgram (l : BitMachineIteration.Label counter) :=
  stackStmt binaryEmbedding (BitMachineIteration.program counter l)

noncomputable def program := BitMachineRawSequence.program addressProgram binaryProgram
  (.inr .testFuel) false (counter.initial, none)

abbrev Label := BitMachineRawSequence.Label MatrixAddressMachine.Label
  (BitMachineIteration.Label counter)
abbrev Control := Bool × BitMachineIteration.Control counter
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

theorem binary_bank (r w c : ℕ) (S : BitMachineIteration.Stack counter → List Bool) :
    bank binaryEmbedding (inputs r w c) S = ambient r w c S := by
  funext k
  cases k with
  | inl k =>
      rw [bank_outside]
      · rfl
      · intro ⟨j, h⟩; cases h
  | inr k => exact bank_at binaryEmbedding (inputs r w c) S k

theorem address_initial (r w c : ℕ) :
    bank addressEmbedding (inputs r w c)
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate r true) (List.replicate w true) (List.replicate c true)
        [] [] []).stk = inputs r w c := by
  apply bank_eq_self
  intro k
  fin_cases k <;> rfl

theorem address_final (r w c : ℕ) :
    bank addressEmbedding (inputs r w c)
      (MatrixAddressMachine.cfg none false
        (List.replicate r true) (List.replicate w true) (List.replicate c true)
        [] [] (List.replicate (r * w + c) true)).stk =
      ambient r w c
        (BitMachineIteration.ready counter [] (List.replicate (r * w + c) true)).stk := by
  have he : (MatrixAddressMachine.cfg none false
      (List.replicate r true) (List.replicate w true) (List.replicate c true)
      [] [] (List.replicate (r * w + c) true)).stk =
      Function.update (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate r true) (List.replicate w true) (List.replicate c true)
        [] [] []).stk 5 (List.replicate (r * w + c) true) := by
    funext k; fin_cases k <;> simp [MatrixAddressMachine.cfg]
  rw [he, bank_update, address_initial, SourceUnaryBinaryCall.initial_bank]
  funext k
  cases k with
  | inl k => simp [addressEmbedding, inputs, ambient]
  | inr k =>
      by_cases h : k = .inr 0
      · subst k; simp [addressEmbedding, ambient]
      · simp [addressEmbedding, inputs, ambient, h]

/-- Every component transition, and the single handoff transition, is charged.
The final bank includes the unchanged three arguments and empty work stacks. -/
theorem label_run (r w c : ℕ) :
    ∃ t ≤ MatrixAddressMachine.exactTime r w c +
        UnaryBinaryEncoding.coefficient * (r * w + c + 1) ^ 2 + 1,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel .outer),
          (false, (counter.initial, none)), inputs r w c⟩ : Config) =
        ⟨none, (false, (counter.initial, none)), outputs r w c⟩ := by
  let middle := ambient r w c
    (BitMachineIteration.ready counter [] (List.replicate (r * w + c) true)).stk
  have ha := BitMachineStackRun.run addressEmbedding (inputs r w c)
    MatrixAddressMachine.program
    (MatrixAddressMachine.cfg (some .outer) false (List.replicate r true)
      (List.replicate w true) (List.replicate c true) [] [] [])
    (MatrixAddressMachine.exactTime r w c)
  have hx := MatrixAddressMachine.address_run r w c false []
  simp only [List.append_nil] at hx
  rw [show ((advance MatrixAddressMachine.program)^[MatrixAddressMachine.exactTime r w c])
      (MatrixAddressMachine.cfg (some .outer) false (List.replicate r true)
        (List.replicate w true) (List.replicate c true) [] [] []) = _ from hx] at ha
  simp only [stackCfg, address_initial, address_final] at ha
  obtain ⟨tb, htb, hb⟩ := SourceUnaryBinaryCall.raw_run (List.replicate (r * w + c) true)
  have hb' := BitMachineStackRun.run binaryEmbedding (inputs r w c)
    (BitMachineIteration.program counter)
    (BitMachineIteration.ready counter [] (List.replicate (r * w + c) true)) tb
  rw [show ((advance (BitMachineIteration.program counter))^[tb])
      (BitMachineIteration.ready counter [] (List.replicate (r * w + c) true)) = _ from hb]
    at hb'
  simp only [stackCfg, binary_bank, List.length_replicate] at hb'
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs addressProgram binaryProgram .outer
    (.inr .testFuel) false false (counter.initial, none) (counter.initial, none)
    (inputs r w c) middle (outputs r w c)
    (MatrixAddressMachine.exactTime r w c) tb ha hb'
  refine ⟨t, ?_, hr⟩
  simp only [List.length_replicate] at htb
  omega

end EthInapproximability.CurrentPaper.SourceLabelAddressMachine
