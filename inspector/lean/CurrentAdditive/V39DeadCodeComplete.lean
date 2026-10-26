import CurrentAdditive.V39DeadCodeSeedLayout

/-! Physical seed construction followed by the fixed unary-fuel recursive
compiler. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace CurrentAdditive.V39DeadCodeComplete

open Paper2

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource
open CurrentAdditive.V39DeadCodeLoop
open Paper2.CodeRecursiveSeedPrep
open Paper2.CodeRecursiveSeedJoin
open CurrentAdditive.V39DeadCodeSeedLayout

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

def loopStart : V39DeadCodeLoop.Label := .inr ()
def loopControl : V39DeadCodeLoop.Control :=
  (V39DeadCodeLoop.roundControl,none)

noncomputable def program := BitMachineRawSequence.program
  CodeRecursiveSeedJoin.program V39DeadCodeLoop.program
  loopStart seedControl loopControl

def seedRecursiveCodes (n p s q₁ q₂ w Q k : Nat) : Code × Code :=
  CurrentAdditive.V39DeadGenericCode.recursiveCodes n s q₁ q₂ w Q (copies p .bit) (.ticket p) k

noncomputable def clock (n p s q₁ q₂ w Q k : Nat) : Nat :=
  CodeRecursiveSeedJoin.clock p +
    V39DeadCodeLoop.totalClock n s q₁ q₂ w Q
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
  obtain ⟨tb,htb,hb⟩ := V39DeadCodeLoop.run_k
    n s q₁ q₂ w Q (copies p .bit) (.ticket p) k hs
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    CodeRecursiveSeedJoin.program V39DeadCodeLoop.program
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


#print axioms run_seedRecursiveCodes

end CurrentAdditive.V39DeadCodeComplete
