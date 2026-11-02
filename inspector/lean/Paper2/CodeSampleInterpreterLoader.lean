import Paper2.CodeGeneratorSampleJoin
import Paper2.CodeFullPadding
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

/-! Physical copy of the *reached* compiled sample code into the real
interpreter's initial scanner input. Public tape/B/R are explicit bank inputs. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeSampleInterpreterLoader

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

abbrev SampleStack := CodeGeneratorSampleJoin.Stack
abbrev ConsumerStack := CodeFullPadding.Stack
abbrev Stack := SampleStack ⊕ (ConsumerStack ⊕ Fin 1)

def sampleSlots : SampleStack ↪ Stack :=
  ⟨Sum.inl, by intro a b h; exact Sum.inl_injective h⟩
def consumerSlots : ConsumerStack ↪ Stack :=
  ⟨fun k => .inr (.inl k), by intro a b h; cases h; rfl⟩
def source : Stack := sampleSlots (CodeGeneratorSampleTransfer.sample 10)
def target : Stack := consumerSlots (CodeHeaderDraw.h 0)
def scratch : Stack := .inr (.inr 0)

def copySlot : Fin 3 → Stack
  | 0 => source
  | 1 => target
  | _ => scratch

theorem copySlot_injective : Function.Injective copySlot := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [copySlot, source, target, scratch, sampleSlots, consumerSlots]

def copySlots : Fin 3 ↪ Stack := ⟨copySlot, copySlot_injective⟩
noncomputable def copyProgram := MatrixStage4ScalarPreparationOps.copyProgram copySlots

def foreign (tape : List Bool) (B R : Nat) : Stack → List Bool
  | .inl _ => []
  | .inr (.inl j) => CodeAdminDraw.foreign tape B R j
  | .inr (.inr _) => []

noncomputable def initialBank (S : SampleStack → List Bool)
    (tape : List Bool) (B R : Nat) : Stack → List Bool :=
  bank sampleSlots (foreign tape B R) S

noncomputable def loadedBank (S : SampleStack → List Bool)
    (tape : List Bool) (B R : Nat) (root : Code) : Stack → List Bool :=
  Function.update (initialBank S tape B R) target (encodeCode root)

theorem source_at (S : SampleStack → List Bool)
    (tape : List Bool) (B R : Nat) :
    initialBank S tape B R source =
      S (CodeGeneratorSampleTransfer.sample 10) := by
  simp [initialBank, source, bank_at]

theorem target_empty (S : SampleStack → List Bool)
    (tape : List Bool) (B R : Nat) :
    initialBank S tape B R target = [] := by
  simp [initialBank, target, bank_outside, foreign,
    consumerSlots, sampleSlots, CodeAdminDraw.foreign, CodeHeaderDraw.h]

theorem scratch_empty (S : SampleStack → List Bool)
    (tape : List Bool) (B R : Nat) :
    initialBank S tape B R scratch = [] := by
  simp [initialBank, scratch, bank_outside, foreign, sampleSlots]

theorem copy_run (S : SampleStack → List Bool)
    (tape : List Bool) (B R : Nat) (root : Code)
    (hS : S (CodeGeneratorSampleTransfer.sample 10) = encodeCode root) :
    ((advance copyProgram)^[2*(encodeCode root).length+2])
      (⟨some .scan,none,initialBank S tape B R⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,none,loadedBank S tape B R root⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run copySlots
    (initialBank S tape B R) (scratch_empty S tape B R)
  rw [show initialBank S tape B R (copySlots 0) = encodeCode root
      from (source_at S tape B R).trans hS,
    show initialBank S tape B R (copySlots 1) = []
      from target_empty S tape B R, List.append_nil] at h
  simpa only [copyProgram, copySlots, copySlot, loadedBank] using h

private theorem admin_initial_bank (root : Code) :
    (CodeAdminNormalization.stateCfg (GeneratorCode.initial root)).stk =
      Function.update (fun _ : CodeAdminMachine.Stack => [])
        (.inl 0) (encodeCode root) := by
  funext j
  rcases j with j | j
  · fin_cases j <;>
      simp [CodeAdminNormalization.stateCfg,
        CodeAdminNormalization.todoWord, GeneratorCode.initial,
        CodeAdminMachine.ready, CodeAdminMachine.cfg,
        CodeScanner.bank, CodeHeaderMachine.contents]
  · cases j
    simp [CodeAdminNormalization.stateCfg,
      CodeAdminNormalization.todoWord, GeneratorCode.initial,
      CodeAdminMachine.ready, CodeAdminMachine.cfg,
      CodeScanner.bank, CodeHeaderMachine.contents]

theorem consumer_start_bank (root : Code) (tape : List Bool) (B R : Nat) :
    (CodeFullPadding.start (GeneratorCode.initial root) tape B R).stk =
      Function.update (CodeAdminDraw.foreign tape B R)
        (CodeHeaderDraw.h 0) (encodeCode root) := by
  change bank CodeAdminDraw.adminSlot (CodeAdminDraw.foreign tape B R)
    (CodeAdminNormalization.stateCfg (GeneratorCode.initial root)).stk = _
  rw [admin_initial_bank, bank_update]
  have hblank : bank CodeAdminDraw.adminSlot
      (CodeAdminDraw.foreign tape B R)
      (fun _ : CodeAdminMachine.Stack => []) =
      CodeAdminDraw.foreign tape B R := by
    apply bank_eq_self
    intro j
    cases j with
    | inl j => cases j <;> simp [CodeAdminDraw.adminSlot, CodeAdminDraw.foreign]
    | inr j => cases j <;> simp [CodeAdminDraw.adminSlot, CodeAdminDraw.foreign]
  rw [hblank]
  rfl

/-- The physically copied code word is exactly the first-order interpreter's
real scanner input, with its tape and B/R words untouched. -/
theorem loaded_consumer (S : SampleStack → List Bool)
    (tape : List Bool) (B R : Nat) (root : Code) (j : ConsumerStack) :
    loadedBank S tape B R root (consumerSlots j) =
      (CodeFullPadding.start (GeneratorCode.initial root) tape B R).stk j := by
  classical
  rw [consumer_start_bank]
  have hbase : initialBank S tape B R (consumerSlots j) =
      CodeAdminDraw.foreign tape B R j := by
    rw [initialBank, bank_outside]
    · rfl
    · rintro ⟨k,h⟩; cases h
  by_cases hj : j = CodeHeaderDraw.h 0
  · subst j
    simp [loadedBank, target, hbase]
  · have hne : consumerSlots j ≠ target := by
      intro h
      exact hj (consumerSlots.injective h)
    simp [loadedBank, hne, hj, hbase]

theorem loaded_consumer_bank (S : SampleStack → List Bool)
    (tape : List Bool) (B R : Nat) (root : Code) :
    (fun j => loadedBank S tape B R root (consumerSlots j)) =
      (CodeFullPadding.start (GeneratorCode.initial root) tape B R).stk := by
  funext j
  exact loaded_consumer S tape B R root j

theorem sample_retained (S : SampleStack → List Bool)
    (tape : List Bool) (B R : Nat) (root : Code) (j : SampleStack) :
    loadedBank S tape B R root (sampleSlots j) = S j := by
  have hne : sampleSlots j ≠ target := by
    intro h; cases h
  rw [loadedBank, Function.update_of_ne hne, initialBank, bank_at]

#print axioms copy_run
#print axioms loaded_consumer
#print axioms loaded_consumer_bank
#print axioms sample_retained

end Paper2.CodeSampleInterpreterLoader
