import Paper2.CodeRecursiveSeedLayout

/-! Physical seed construction followed by the fixed unary-fuel recursive
compiler. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeGeneratorComplete

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource
open Paper2.CodeRecursiveLoop
open Paper2.CodeRecursiveSeedPrep
open Paper2.CodeRecursiveSeedJoin
open Paper2.CodeRecursiveSeedLayout

abbrev SeedLabel := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label CodeAtomCountInput.Label
      BitMachineCopy.Label)
    CodeRecursiveSeedRow.Label)
  CodeRecursiveSeedJoin.ClearLabel

abbrev SeedControl :=
  ((CodeAtomCountInput.Control × Option Bool) × Option Bool) ×
    (Unit × Option Bool)

def seedStart : SeedLabel :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            CodeAtomCountInput.InitLabel.write))))

def seedControl : SeedControl :=
  ((((((),none),()),none),none),((),none))

def loopStart : CodeRecursiveLoop.Label := .inr ()
def loopControl : CodeRecursiveLoop.Control :=
  (CodeRecursiveLoop.roundControl,none)

noncomputable def program := BitMachineRawSequence.program
  CodeRecursiveSeedJoin.program CodeRecursiveLoop.program
  loopStart seedControl loopControl

noncomputable def clock (n p s q₁ q₂ w Q k : Nat) : Nat :=
  CodeRecursiveSeedJoin.clock p +
    CodeRecursiveLoop.totalClock n s q₁ q₂ w Q
      (copies p .bit) (.ticket p) k + 1

/-- A single fixed program physically builds the actual seed and then
executes k recursive syntax levels. Its only initial variable words are
the seven public raw count words and unary k fuel. -/
theorem run_seedRecursiveCodes (n p s q₁ q₂ w Q k : Nat)
    (hs : 3 ≤ s) :
    ∃ t ≤ clock n p s q₁ q₂ w Q k,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel seedStart),
          (seedControl,loopControl),
          publicBase n s q₁ q₂ w Q p (List.replicate k true)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (seedControl,loopControl),
          (finished n s q₁ q₂ w Q
            (seedRecursiveCodes n p s q₁ q₂ w Q k).1
            (seedRecursiveCodes n p s q₁ q₂ w Q k).2).stk⟩ := by
  obtain ⟨ta,hta,ha⟩ := CodeRecursiveSeedJoin.run_exact
    n s q₁ q₂ w Q p (List.replicate k true)
  have hbank := seed_clean_is_loop_bank n s q₁ q₂ w Q p
    (List.replicate k true)
  change seedClean n s q₁ q₂ w Q p (List.replicate k true) =
    (ready n s q₁ q₂ w Q (copies p .bit) (.ticket p)
      (List.replicate k true)).stk at hbank
  rw [hbank] at ha
  obtain ⟨tb,htb,hb⟩ := CodeRecursiveLoop.run_k
    n s q₁ q₂ w Q (copies p .bit) (.ticket p) k hs
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    CodeRecursiveSeedJoin.program CodeRecursiveLoop.program
    seedStart loopStart seedControl seedControl loopControl loopControl
    (publicBase n s q₁ q₂ w Q p (List.replicate k true))
    (ready n s q₁ q₂ w Q (copies p .bit) (.ticket p)
      (List.replicate k true)).stk
    (finished n s q₁ q₂ w Q
      (seedRecursiveCodes n p s q₁ q₂ w Q k).1
      (seedRecursiveCodes n p s q₁ q₂ w Q k).2).stk
    ta tb ha (by simpa only [seedRecursiveCodes] using hb)
  exact ⟨t, by dsimp [clock]; omega, by
    simpa only [finished] using hr⟩

theorem run_scheduledCodes (n m L Δ k : Nat) (γ : ℚ)
    (hs : 3 ≤ SourceProfileParameters.width L) :
    ∃ t ≤ clock n (LookupSeed.width L)
        (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2)
        (SourceProfileParameters.outerWidth L)
        (ParameterizedCanonicalSource.restorationWidth L)
        (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel seedStart),
          (seedControl,loopControl),
          publicBase n (SourceProfileParameters.width L)
            (SourceProfileParameters.width L - 2)
            (SourceProfileParameters.outerWidth L)
            (ParameterizedCanonicalSource.restorationWidth L)
            (ParameterizedCanonicalSource.coverWidth n m L Δ γ)
            (LookupSeed.width L) (List.replicate k true)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (seedControl,loopControl),
          (finished n (SourceProfileParameters.width L)
            (SourceProfileParameters.width L - 2)
            (SourceProfileParameters.outerWidth L)
            (ParameterizedCanonicalSource.restorationWidth L)
            (ParameterizedCanonicalSource.coverWidth n m L Δ γ)
            (scheduledCodes n m L Δ γ k).1
            (scheduledCodes n m L Δ γ k).2).stk⟩ := by
  simpa only [scheduledCodes] using
    run_seedRecursiveCodes n (LookupSeed.width L)
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k hs

#print axioms run_seedRecursiveCodes
#print axioms run_scheduledCodes

end Paper2.CodeGeneratorComplete
