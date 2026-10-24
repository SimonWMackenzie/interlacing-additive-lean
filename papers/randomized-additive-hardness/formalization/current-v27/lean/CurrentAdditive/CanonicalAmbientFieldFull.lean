import CurrentAdditive.CanonicalAmbientFieldRun

/-! One literal ambient program copies unary d,n into the field initializer,
then prepares the search bank, finds the first-passing polynomial, and prints
the packed field list. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FieldSearchCompletion
open CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine
open CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff

def fieldInputBank (t d n : ℕ) (S : Cell t 16 → List Bool) :=
  Function.update (Function.update S (.fieldInit 0)
    (List.replicate d true)) (.fieldInit 1) (List.replicate n true)

def fieldFullProgram (t : ℕ) :=
  BitMachineRawSequence.program
    (fieldInputProgram t 16 (by decide)) (fieldStage t)
    (.prep .scanD) (none, none) (prepEmbed none)

theorem fieldInputBank_local (t d n : ℕ) (S : Cell t 16 → List Bool)
    (hblank : ∀ i : FieldUnaryUnifiedMachine.Stack,
      S (fieldCombinedEmbed t 16 i) = [])
    (i : FieldUnaryUnifiedMachine.Stack) :
    fieldInputBank t d n S (fieldCombinedEmbed t 16 i) =
      FieldUnaryUnifiedMachine.initialStack d n i := by
  rcases i with i | i
  · fin_cases i <;>
      simp_all [fieldInputBank, fieldCombinedEmbed,
        FieldUnaryUnifiedMachine.initialStack]
  · simpa [fieldInputBank, fieldCombinedEmbed,
      FieldUnaryUnifiedMachine.initialStack] using hblank (.inr i)

theorem physical_field_full (t d n : ℕ) (hdpos : 0 < d)
    (S : Cell t 16 → List Bool)
    (hd : S (.degree 3) = List.replicate d true)
    (hn : S (.width 3) = List.replicate n true)
    (hblank : ∀ i : FieldUnaryUnifiedMachine.Stack,
      S (fieldCombinedEmbed t 16 i) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ∃ c < 2^d,
      CurrentAdditive.FiniteFieldConstructor.TrialSearch.firstPassing d =
        some (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c) ∧
      ∃ u ≤ FieldUnaryUnifiedMachine.prepTime d n +
          55 * 2^d * 2^(d/2) * (d+1)^2 + 2 +
          CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.timeBound d c n,
        ∃ total ≤ (2*d+2)+(2*n+2)+1+u+1,
          ((advance (fieldFullProgram t))^[total])
            (⟨some (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
              ((none, none), prepEmbed none), S⟩ :
                TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
            ⟨none, ((none, none),
                (FieldUnaryUnifiedMachine.run u
                  (FieldUnaryUnifiedMachine.initialConfig d n)).var),
              bank (fieldCombinedEmbed t 16) (fieldInputBank t d n S)
                (FieldUnaryUnifiedMachine.run u
                  (FieldUnaryUnifiedMachine.initialConfig d n)).stk⟩ ∧
          (FieldUnaryUnifiedMachine.run u
            (FieldUnaryUnifiedMachine.initialConfig d n)).stk
            (FieldUnaryUnifiedMachine.fieldSlots
              (printerSlots
                CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
            CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.packedBits d c n := by
  let S1 := fieldInputBank t d n S
  obtain ⟨s, hs, hcopy⟩ := physical_field_inputs t 16 d n (by decide) S
    hd hn (hblank (.inl 0)) (hblank (.inl 1)) hscratch
  obtain ⟨c, hc, hfirst, u, hu, heq, hhalt, hout⟩ :=
    physical_ambient_field t d n hdpos S1
      (fieldInputBank_local t d n S hblank)
  let r := FieldUnaryUnifiedMachine.run u
    (FieldUnaryUnifiedMachine.initialConfig d n)
  have hrhalt : r.l = none := by
    rw [heq] at hhalt
    simpa [r, stackCfg] using hhalt
  have hsecond : ((advance (fieldStage t))^[u])
      (⟨some (.prep .scanD), prepEmbed none, S1⟩ :
        TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
      ⟨none, r.var,
        bank (fieldCombinedEmbed t 16) S1 r.stk⟩ := by
    simpa [r, stackCfg, hrhalt] using heq
  have hpackedLocal : r.stk
      (FieldUnaryUnifiedMachine.fieldSlots
        (printerSlots
          CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
      CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.packedBits d c n := by
    rw [heq] at hout
    change bank (fieldCombinedEmbed t 16) S1 r.stk
      (.field (printerSlots
        CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) = _ at hout
    have hslot : fieldCombinedEmbed t 16
        (FieldUnaryUnifiedMachine.fieldSlots
          (printerSlots
            CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
        (.field (printerSlots
          CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output) : Cell t 16) := rfl
    rw [← hslot, bank_at] at hout
    exact hout
  obtain ⟨total, htotal, hrun⟩ := BitMachineRawSequence.runs
    (fieldInputProgram t 16 (by decide)) (fieldStage t)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (.prep .scanD)
    (none, none) (none, none) (prepEmbed none) r.var
    S S1 _ s u (by simpa [S1, fieldInputBank] using hcopy) hsecond
  refine ⟨c, hc, hfirst, u, hu, total, by omega, ?_, ?_⟩
  · simpa [fieldFullProgram, S1, fieldInputBank, r] using hrun
  · exact hpackedLocal

#print axioms physical_field_full

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
