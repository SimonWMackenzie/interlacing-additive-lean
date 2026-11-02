import CurrentAdditive.RoundedCodePolynomial
import EthInapproximability.CurrentPaper.DimensionNatUnary

/-! The interpreter's accumulator is physically reversed. This final charged
two-stack reversal puts literal forward output bytes in the empty code port.
It consumes no random bits and preserves the exact unused tape and width. -/

namespace EthInapproximability.CurrentPaper.RoundedCodeOutput

open Turing BitMachineEncoding BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorPositive Paper2.GeneratorStateSize
open Paper2.GeneratorSerialization CurrentAdditive.RoundedDraw
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

abbrev Stack := RoundedCodeLoop.Stack
def resultPort : Stack := RoundedCodeReset.code
def outputPort : Stack := RoundedCodeReset.output
def tapePort : Stack := RoundedCodeReset.tape
def widthPort : Stack := RoundedCodeReset.width

def reverseSlots : Fin 2 ↪ Stack :=
  ⟨![outputPort, resultPort], by decide⟩
def reverseProgram (l : Unit) := stackStmt reverseSlots (DimensionNatUnary.reverseProgram l)

abbrev Label := BitMachineRawSequence.Label RoundedCodeLoop.Label Unit
abbrev Control := RoundedCodeLoop.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (RoundedCodeStep.initial, none)
def program := BitMachineRawSequence.program RoundedCodeLoop.program reverseProgram ()
  RoundedCodeStep.initial none
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c
def start (c : Code) (tape : List Bool) (b : ℕ) : Config :=
  ⟨some (BitMachineRawSequence.leftLabel (.inl RoundedCodeLoop.entry)), initial,
    (RoundedCodeAdmin.start (Paper2.GeneratorCode.initial c) tape b).stk⟩

def finalBank (out tape : List Bool) (b : ℕ) : Stack → List Bool :=
  fun k => if k = resultPort then out else if k = tapePort then tape else
    if k = widthPort then List.replicate b true else []

private theorem reverse_initial (out tape : List Bool) (b : ℕ) :
    bank reverseSlots (RoundedCodeAdmin.start ⟨[], out⟩ tape b).stk
      (DimensionNatUnary.reverseCfg (some ()) none out.reverse []).stk =
      (RoundedCodeAdmin.start ⟨[], out⟩ tape b).stk := by
  apply bank_eq_self
  intro i
  rw [RoundedCodeCanonical.start_bank]
  fin_cases i <;> simp [reverseSlots, DimensionNatUnary.reverseCfg,
    RoundedCodeCanonical.bank, resultPort, outputPort, RoundedCodeReset.code,
    RoundedCodeReset.output, Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.output,
    Paper2.CodeAdminNormalization.todoWord]

private theorem reverse_final (out tape : List Bool) (b : ℕ) :
    bank reverseSlots (RoundedCodeAdmin.start ⟨[], out⟩ tape b).stk
      (DimensionNatUnary.reverseCfg none none [] out).stk = finalBank out tape b := by
  funext k
  by_cases hr : k = resultPort
  · subst k
    change bank reverseSlots _ _ (reverseSlots 1) = _
    rw [bank_at]
    simp [finalBank, DimensionNatUnary.reverseCfg]
  · by_cases ho : k = outputPort
    · subst k
      change bank reverseSlots _ _ (reverseSlots 0) = _
      rw [bank_at]
      simp [finalBank, DimensionNatUnary.reverseCfg, hr, resultPort, outputPort, tapePort, widthPort,
        RoundedCodeReset.code, RoundedCodeReset.output, RoundedCodeReset.tape, RoundedCodeReset.width,
        RoundedCodeDraw.oldTape, RoundedCodeDraw.oldWidth,
        Paper2.CodeHeaderDraw.output, Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d]
    · rw [bank_outside]
      · rw [RoundedCodeCanonical.start_bank]
        change k ≠ RoundedCodeReset.code at hr
        change k ≠ RoundedCodeReset.output at ho
        simp [RoundedCodeCanonical.bank, finalBank, hr, ho, resultPort, outputPort,
          tapePort, widthPort] <;> rfl
      · rintro ⟨i, hi⟩
        fin_cases i
        · exact ho hi.symm
        · exact hr hi.symm

theorem physical_reverse (out tape : List Bool) (b : ℕ) :
    ((advance reverseProgram)^[out.length + 1])
      (⟨some (), none, (RoundedCodeAdmin.start ⟨[], out⟩ tape b).stk⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Unit (Option Bool)) =
      ⟨none, none, finalBank out tape b⟩ := by
  have h := BitMachineStackRun.run reverseSlots
    (RoundedCodeAdmin.start ⟨[], out⟩ tape b).stk DimensionNatUnary.reverseProgram
    (DimensionNatUnary.reverseCfg (some ()) none out.reverse []) (out.length + 1)
  have hrev := DimensionNatUnary.reverse_run out.reverse [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hrev
  rw [hrev] at h
  change ((advance reverseProgram)^[out.length + 1])
    ⟨some (), none, bank reverseSlots _ _⟩ = ⟨none, none, bank reverseSlots _ _⟩ at h
  rw [reverse_initial, reverse_final] at h
  exact h

theorem execute_trace (root : Code) (b N : ℕ) (s : State) (ht : Trace root s)
    (bits : BitBlocks b N) : Trace root (RoundedCodeLoop.execute b N s bits).1 := by
  induction N generalizing s with
  | zero => exact trace_normalize root s ht
  | succ N ih =>
      by_cases hd : (Paper2.GeneratorCode.normalize s).todo = []
      · simpa only [RoundedCodeLoop.execute, hd, ↓reduceIte] using trace_normalize root s ht
      · simpa only [RoundedCodeLoop.execute, hd, ↓reduceIte] using
          ih (RoundedCodeLoop.roundedNext s b bits.1)
            (RoundedCodeLoop.roundedNext_trace root s ht b bits.1) bits.2

theorem physical_forward {A : ℕ} (c : Code) (hc : Positive c) (b N : ℕ)
    (hA : (meaning c).maxAlphabet ≤ A) (hN : (meaning c).maxDraws ≤ N)
    (bits : BitBlocks b N) (suffix : List Bool) :
    ∃ t ≤ RoundedCodeLoop.interpreterCoefficient * (N + 1) * (codeSize c + b + 3) ^ 2 +
        codeSize c + 2,
      run t (start c (RoundedCodeLoop.tapeWord b N bits ++ suffix) b) =
        ⟨none, initial, finalBank
          (CurrentAdditive.RoundedProgram.runProgram b N ⟨meaning c, hA⟩ hN bits)
          ((RoundedCodeLoop.execute b N (Paper2.GeneratorCode.initial c) bits).2 ++ suffix) b⟩ := by
  let out := CurrentAdditive.RoundedProgram.runProgram b N ⟨meaning c, hA⟩ hN bits
  let unused := (RoundedCodeLoop.execute b N (Paper2.GeneratorCode.initial c) bits).2 ++ suffix
  obtain ⟨u, hu, hur⟩ := RoundedCodeLoop.physical_initialProgram_polynomial c hc b N hA hN bits suffix
  have hr := physical_reverse out unused b
  have ha : (stateMeaning (Paper2.GeneratorCode.initial c)).maxAlphabet ≤ A := by
    simpa only [RoundedCodeLoop.initial_meaning] using hA
  have hn : (stateMeaning (Paper2.GeneratorCode.initial c)).maxDraws ≤ N := by
    simpa only [RoundedCodeLoop.initial_meaning] using hN
  have hout : out.length ≤ codeSize c := by
    have hl := trace_output_length_le c _
      (execute_trace c b N (Paper2.GeneratorCode.initial c) Trace.initial bits)
    have he := RoundedCodeLoop.execute_output_eq_runProgram b N
      (Paper2.GeneratorCode.initial c) (positive_initial c hc) ha hn bits
    simp only [RoundedCodeLoop.initial_meaning] at he
    simpa only [he] using hl
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs RoundedCodeLoop.program reverseProgram
    (.inl RoundedCodeLoop.entry) () RoundedCodeStep.initial (RoundedCodeStep.finalControl true)
    none none (RoundedCodeAdmin.start (Paper2.GeneratorCode.initial c)
      (RoundedCodeLoop.tapeWord b N bits ++ suffix) b).stk
    (RoundedCodeAdmin.start ⟨[], out⟩ unused b).stk (finalBank out unused b)
    u (out.length + 1) hur hr
  exact ⟨t, by omega, hrun⟩

#print axioms physical_reverse
#print axioms physical_forward

end
end EthInapproximability.CurrentPaper.RoundedCodeOutput
