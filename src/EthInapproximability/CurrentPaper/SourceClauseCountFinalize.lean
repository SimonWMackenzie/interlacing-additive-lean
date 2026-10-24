import EthInapproximability.CurrentPaper.SourceClauseUnitMachine
import EthInapproximability.CurrentPaper.SourceUnaryBinaryCall

/-!
# Physical emitted-clause count conversion and CNF finalization

Source: frozen v8 `06-eth.tex` and `B-effectivity-details.tex`.
The clause writer increments a unary counter once for each emitted 3-clause.
This machine physically converts that counter to a canonical binary word and
then runs the proved finalizer. It keeps the reverse payload and optional
output suffix in foreign stacks during the conversion. No binary clause-count
word or completed encoded CNF is an input to this program.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseCountFinalize

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable abbrev counter := SourceUnaryBinaryCall.counter
abbrev Stack := Fin 4 ⊕ BitMachineIteration.Stack counter
abbrev Label := BitMachineRawSequence.Label
  (BitMachineIteration.Label counter) SourceClauseMachine.Label
abbrev Control := BitMachineIteration.Control counter × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def countEmbedding : BitMachineIteration.Stack counter ↪ Stack :=
  Function.Embedding.inr

noncomputable def finalizerEmbedding : SourceClauseMachine.Stack ↪ Stack where
  toFun k := if k = 0 then .inl 0 else if k = 1 then
    .inr (.inl counter.input) else if k = 2 then .inl 1 else if k = 3 then
      .inl 2 else .inl 3
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

def outer (n : Nat) (reversePayload output : List Bool) : Fin 4 → List Bool :=
  ![List.replicate n true, reversePayload, [], output]

noncomputable def inputBank (n count : Nat) (reversePayload output : List Bool) :
    Stack → List Bool :=
  Sum.elim (outer n reversePayload output)
    (BitMachineIteration.ready counter [] (List.replicate count true)).stk

noncomputable def convertedBank (n count : Nat) (reversePayload output : List Bool) :
    Stack → List Bool :=
  Sum.elim (outer n reversePayload output)
    (BitMachineIteration.finished counter count.bits).stk

noncomputable def countProgram (l : BitMachineIteration.Label counter) :=
  stackStmt countEmbedding (BitMachineIteration.program counter l)

noncomputable def finalizerProgram (l : SourceClauseMachine.Label) :=
  stackStmt finalizerEmbedding (SourceClauseMachine.program l)

noncomputable def program := BitMachineRawSequence.program countProgram
  finalizerProgram .payload (counter.initial, none) none

theorem counter_bank (S T : BitMachineIteration.Stack counter → List Bool)
    (n : Nat) (reversePayload output : List Bool) :
    bank countEmbedding (Sum.elim (outer n reversePayload output) S) T =
      Sum.elim (outer n reversePayload output) T := by
  funext k
  cases k with
  | inr j => exact bank_at countEmbedding _ T j
  | inl j =>
      rw [bank_outside]
      · rfl
      · intro ⟨u, h⟩; cases h

theorem finalizer_initial (n count : Nat) (reversePayload output : List Bool) :
    bank finalizerEmbedding (convertedBank n count reversePayload output)
      (SourceClauseMachine.cfg (some .payload) none
        (List.replicate n true) count.bits reversePayload [] output).stk =
      convertedBank n count reversePayload output := by
  apply bank_eq_self
  intro k
  simp only [convertedBank, SourceUnaryBinaryCall.final_bank]
  fin_cases k <;>
    simp [finalizerEmbedding, SourceClauseMachine.cfg,
      SourceClauseMachine.contents, outer]

/-- The two physical programs run on one finite Boolean-stack bank. The
complete final bank is exposed; in particular the output stack is projected
without discarding foreign-stack information. -/
theorem count_and_finalize (n count : Nat) (reversePayload output : List Bool) :
    ∃ t ≤ UnaryBinaryEncoding.coefficient * (count + 1) ^ 2 +
        (reversePayload.length + 3 * count.bits.length + n + 5) + 1,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inr .testFuel)),
          ((counter.initial, none), none), inputBank n count reversePayload output⟩ : Config) =
        ⟨none, ((counter.initial, none), none),
          bank finalizerEmbedding (convertedBank n count reversePayload output)
            (SourceClauseMachine.cfg none none [] [] [] []
              (EncodedGraph.unary n ++ EncodedCommunication.natField count ++
                reversePayload.reverse ++ output)).stk⟩ := by
  obtain ⟨ta, hta, ha⟩ :=
    SourceUnaryBinaryCall.raw_run (List.replicate count true)
  change ((advance (BitMachineIteration.program counter))^[ta])
      (BitMachineIteration.ready counter [] (List.replicate count true)) =
      BitMachineIteration.finished counter (List.replicate count true).length.bits at ha
  simp only [List.length_replicate] at ha
  have ha' := BitMachineStackRun.run countEmbedding
    (inputBank n count reversePayload output)
    (BitMachineIteration.program counter)
    (BitMachineIteration.ready counter [] (List.replicate count true)) ta
  rw [ha] at ha'
  simp only [stackCfg] at ha'
  have hi : bank countEmbedding (inputBank n count reversePayload output)
      (BitMachineIteration.ready counter [] (List.replicate count true)).stk =
      inputBank n count reversePayload output := by
    exact counter_bank _ _ n reversePayload output
  have hf : bank countEmbedding (inputBank n count reversePayload output)
      (BitMachineIteration.finished counter count.bits).stk =
      convertedBank n count reversePayload output := by
    exact counter_bank _ _ n reversePayload output
  rw [hi, hf] at ha'
  change ((advance countProgram)^[ta])
    (⟨some (.inr .testFuel), (counter.initial, none),
      inputBank n count reversePayload output⟩ :
      TM2.Cfg (fun _ : Stack => Bool) (BitMachineIteration.Label counter)
        (BitMachineIteration.Control counter)) =
    ⟨none, (counter.initial, none), convertedBank n count reversePayload output⟩ at ha'
  have hb := SourceClauseMachine.finalize n count reversePayload output
  have hb' := BitMachineStackRun.run finalizerEmbedding
    (convertedBank n count reversePayload output)
    SourceClauseMachine.program
    (SourceClauseMachine.cfg (some .payload) none
      (List.replicate n true) count.bits reversePayload [] output)
    (reversePayload.length + 3 * count.bits.length + n + 5)
  change ((advance SourceClauseMachine.program)^[
      reversePayload.length + 3 * count.bits.length + n + 5])
      (SourceClauseMachine.cfg (some .payload) none
        (List.replicate n true) count.bits reversePayload [] output) = _ at hb
  rw [hb] at hb'
  simp only [stackCfg, finalizer_initial] at hb'
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs countProgram
    finalizerProgram (.inr .testFuel) .payload
    (counter.initial, none) (counter.initial, none)
    none none (inputBank n count reversePayload output)
    (convertedBank n count reversePayload output)
    (bank finalizerEmbedding (convertedBank n count reversePayload output)
      (SourceClauseMachine.cfg none none [] [] [] []
        (EncodedGraph.unary n ++ EncodedCommunication.natField count ++
          reversePayload.reverse ++ output)).stk)
    ta (reversePayload.length + 3 * count.bits.length + n + 5) ha' hb'
  refine ⟨t, ?_, hr⟩
  simp only [List.length_replicate] at hta
  omega

theorem count_and_finalize_output (n count : Nat)
    (reversePayload output : List Bool) :
    ∃ t ≤ UnaryBinaryEncoding.coefficient * (count + 1) ^ 2 +
        reversePayload.length + 3 * count.bits.length + n + 6,
      let c := ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inr .testFuel)),
          ((counter.initial, none), none), inputBank n count reversePayload output⟩ : Config)
      c.l = none ∧ c.stk (.inl 3) =
        EncodedGraph.unary n ++ EncodedCommunication.natField count ++
          reversePayload.reverse ++ output := by
  obtain ⟨t, ht, hr⟩ := count_and_finalize n count reversePayload output
  refine ⟨t, by omega, ?_⟩
  rw [hr]
  constructor
  · rfl
  · change bank finalizerEmbedding (convertedBank n count reversePayload output)
        (SourceClauseMachine.cfg none none [] [] [] []
          (EncodedGraph.unary n ++ EncodedCommunication.natField count ++
            reversePayload.reverse ++ output)).stk (.inl 3) = _
    rw [show (.inl 3 : Stack) = finalizerEmbedding 4 by
      simp [finalizerEmbedding], bank_at]
    rfl

end EthInapproximability.CurrentPaper.SourceClauseCountFinalize
