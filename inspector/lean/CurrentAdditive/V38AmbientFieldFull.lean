import CurrentAdditive.V38AmbientFieldInstall

/-! Two literal preserving copies discharge the public producer input ABI.
The genuine width is read from width cell 5; padded width cell 3 is untouched.
The entire public-input/field-search/padding/install sequence is one program. -/

noncomputable section

namespace CurrentAdditive.V38AmbientFieldFull

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.SmallBias CurrentAdditive.V38Machine CurrentAdditive.V38Clock
open CurrentAdditive.FieldSearchCompletion
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
open CurrentAdditive.V38AmbientFieldInstall

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def degreePlace (t : ℕ) : Fin 3 ↪ Cell t 16 :=
  ⟨![.degree 3, .fieldInit 0, .copyScratch 0], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def genuinePlace (t : ℕ) : Fin 3 ↪ Cell t 16 :=
  ⟨![.width 5, .fieldInit 1, .copyScratch 0], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def inputProgram (t : ℕ) :=
  BitMachineRawSequence.program
    (MatrixStage4ScalarPreparationOps.copyProgram (degreePlace t))
    (MatrixStage4ScalarPreparationOps.copyProgram (genuinePlace t))
    .scan none none

def inputBank (t d n : ℕ) (S : Cell t 16 → List Bool) : Cell t 16 → List Bool :=
  Function.update (Function.update S (.fieldInit 0) (List.replicate d true))
    (.fieldInit 1) (List.replicate n true)

theorem physical_inputs (t d n : ℕ) (S : Cell t 16 → List Bool)
    (hd : S (.degree 3) = List.replicate d true)
    (hn : S (.width 5) = List.replicate n true)
    (h0 : S (.fieldInit 0) = []) (h1 : S (.fieldInit 1) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ∃ steps ≤ (2 * d + 2) + (2 * n + 2) + 1,
      ((advance (inputProgram t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, none), S⟩ : TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none, (none, none), inputBank t d n S⟩ := by
  let T := Function.update S (.fieldInit 0) (List.replicate d true)
  have hfirst : ((advance (MatrixStage4ScalarPreparationOps.copyProgram (degreePlace t)))^[2*d+2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ : TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
      ⟨none, none, T⟩ := by
    have hr := MatrixStage4ScalarPreparationOps.copy_run (degreePlace t) S
      (by simpa [degreePlace] using hscratch)
    simpa [degreePlace, hd, h0, T] using hr
  have hsecond : ((advance (MatrixStage4ScalarPreparationOps.copyProgram (genuinePlace t)))^[2*n+2])
      (⟨some BitMachineCopy.Label.scan, none, T⟩ : TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
      ⟨none, none, inputBank t d n S⟩ := by
    have hr := MatrixStage4ScalarPreparationOps.copy_run (genuinePlace t) T
      (by simp [genuinePlace, T, hscratch])
    simpa [genuinePlace, T, inputBank, hn, h1] using hr
  exact BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.copyProgram (degreePlace t))
    (MatrixStage4ScalarPreparationOps.copyProgram (genuinePlace t))
    .scan .scan none none none none S T (inputBank t d n S)
    (2*d+2) (2*n+2) hfirst hsecond

theorem inputBank_local (b t : ℕ) (S : Cell t 16 → List Bool)
    (hblank : ∀ i : V38FieldPad.Stack, S (producerEmbed t i) = [])
    (i : V38FieldPad.Stack) :
    inputBank t (v38FieldDegree b t) (v38PositionCount b t) S (producerEmbed t i) =
      (V38FieldPad.publicStart b t).stk i := by
  rcases i with i | i
  · rcases i with i | i
    · fin_cases i <;>
        simp_all [inputBank, producerEmbed, producerSlot, fieldCombinedEmbed,
          V38FieldPad.publicStart, V38FieldPad.initialConfig, V38FieldPad.initialStack,
          FieldUnaryUnifiedMachine.initialStack]
    · have hi := hblank (.inl (.inr i))
      simpa [inputBank, producerEmbed, producerSlot, fieldCombinedEmbed,
        V38FieldPad.publicStart, V38FieldPad.initialConfig, V38FieldPad.initialStack,
        FieldUnaryUnifiedMachine.initialStack] using hi
  · cases i with
    | false =>
      simpa [inputBank, producerEmbed, producerSlot, fieldCombinedEmbed,
        V38FieldPad.publicStart, V38FieldPad.initialConfig, V38FieldPad.initialStack,
        FieldUnaryUnifiedMachine.initialStack] using hblank (.inr false)
    | true =>
      simpa [inputBank, producerEmbed, producerSlot, fieldCombinedEmbed,
        V38FieldPad.publicStart, V38FieldPad.initialConfig, V38FieldPad.initialStack,
        FieldUnaryUnifiedMachine.initialStack] using hblank (.inr true)

def fullProgram (t : ℕ) :=
  BitMachineRawSequence.program (inputProgram t) (installProgram t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (FieldUnaryUnifiedMachine.Label.prep .scanD)))
    (none, none) (sourceControl, none)

def publicCopyClock (b t : ℕ) : ℕ :=
  (2 * v38FieldDegree b t + 2) + (2 * v38PositionCount b t + 2) + 1

def fullClock (b t : ℕ) : ℕ := publicCopyClock b t + 108 * (v38FieldTarget b t) ^ 5 + 1

theorem physical_full (b t : ℕ) (ht : 4 ≤ t) (S : Cell t 16 → List Bool)
    (hd : S (.degree 3) = List.replicate (v38FieldDegree b t) true)
    (hn : S (.width 5) = List.replicate (v38PositionCount b t) true)
    (hblank : ∀ i : V38FieldPad.Stack, S (producerEmbed t i) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ∃ modulus,
      FiniteFieldConstructor.TrialSearch.firstPassing (v38FieldDegree b t) = some modulus ∧
      ∃ producerSteps ≤ 100 * (v38FieldTarget b t) ^ 5,
      ∃ total ≤ fullClock b t,
        let T := inputBank t (v38FieldDegree b t) (v38PositionCount b t) S
        let produced := V38FieldPad.run (2 ^ t * 2 ^ t) (by positivity)
          producerSteps (V38FieldPad.publicStart b t)
        ((advance (fullProgram t))^[total])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
            ((none, none), (sourceControl, none)), S⟩ :
              TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
          ⟨none, ((none, none), (sourceControl, none)),
            Function.update (bank (producerEmbed t) T produced.stk)
              (fieldBankCell t) (paddedBits b t (v38FieldDegree b t) modulus)⟩ := by
  let T := inputBank t (v38FieldDegree b t) (v38PositionCount b t) S
  have h0 : S (.fieldInit 0) = [] := hblank (.inl (.inl 0))
  have h1 : S (.fieldInit 1) = [] := hblank (.inl (.inl 1))
  obtain ⟨ti, hti, hi⟩ := physical_inputs t _ _ S hd hn h0 h1 hscratch
  obtain ⟨modulus, hfirst, ps, hps, tf, htf, hf⟩ := physical_install b t ht T
    (inputBank_local b t S hblank)
    (by simp [T, inputBank, hscratch])
  let produced := V38FieldPad.run (2 ^ t * 2 ^ t) (by positivity) ps
    (V38FieldPad.publicStart b t)
  let U := Function.update (bank (producerEmbed t) T produced.stk)
    (fieldBankCell t) (paddedBits b t (v38FieldDegree b t) modulus)
  obtain ⟨total, htotal, hr⟩ := BitMachineRawSequence.runs (inputProgram t) (installProgram t)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (FieldUnaryUnifiedMachine.Label.prep .scanD)))
    (none, none) (none, none) (sourceControl, none) (sourceControl, none)
    S T U ti tf hi hf
  refine ⟨modulus, hfirst, ps, hps, total, ?_, hr⟩
  dsimp [fullClock, publicCopyClock]
  omega

#print axioms physical_inputs
#print axioms inputBank_local
#print axioms physical_full

end CurrentAdditive.V38AmbientFieldFull
