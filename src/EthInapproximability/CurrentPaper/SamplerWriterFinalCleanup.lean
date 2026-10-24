import EthInapproximability.CurrentPaper.SamplerWriterPhysicalSequence
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-!
# Physical cleanup of the exact sampler's writer bank

The sampler uses writer scratch cells 32--50 and two extra input stacks.
This fixed machine pops every remaining bit in those cells, retaining the
three payload arrays and scalar inputs in the writer frame.
-/

namespace EthInapproximability.CurrentPaper.SamplerWriterFinalCleanup

open Turing BitMachineEncoding

abbrev Stack := SamplerWriterPhysicalSequence.Stack
abbrev Label := Fin 23
abbrev Control := Unit × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def clearing (i : Fin 21) : Stack :=
  if h : i.val < 19 then
    .inl (.inl (.inl (.inl ⟨32 + i.val, by omega⟩)))
  else .inr ⟨i.val - 19, by omega⟩

theorem clearing_injective : Function.Injective clearing := by decide

def labels (i : Fin 22) : Label := ⟨i.val, by omega⟩

def program (l : Label) : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  if h : l.val < 21 then
    BitMachineClearBank.clearStep (clearing ⟨l.val, h⟩) l
      ⟨l.val + 1, by omega⟩
  else if l.val = 21 then BitMachineClearBank.finishStep id 22
  else .halt

theorem run_clear (S : Stack → List Bool) :
    ((advance program)^[(∑ i : Fin 21, (S (clearing i)).length) + 22])
      (⟨some 0, ((), none), S⟩ : Config) =
    ⟨some 22, ((), none), BitMachineClearBank.cleared clearing S⟩ := by
  apply BitMachineClearBank.clear_bank_run program id 22 21 clearing
    clearing_injective labels
  · intro i
    simp [program, labels]
  · simp [program, labels]

theorem run_halt (S : Stack → List Bool) :
    ((advance program)^[(∑ i : Fin 21, (S (clearing i)).length) + 23])
      (⟨some 0, ((), none), S⟩ : Config) =
    ⟨none, ((), none), BitMachineClearBank.cleared clearing S⟩ := by
  rw [show (∑ i : Fin 21, (S (clearing i)).length) + 23 =
      1 + ((∑ i : Fin 21, (S (clearing i)).length) + 22) by omega,
    Function.iterate_add_apply, run_clear]
  rfl

def exactData (a t₁ t₂ d n : ℕ) (v : Fin n → Fin d → Bool) :
    MatrixMaterialization.ExactBitData :=
  MatrixMaterialization.storeBits
    (ExecutableSmallBiasSampler.exactFirstFamily a t₁ d)
    (ExecutableSmallBiasSampler.exactSecondFamily a t₂ d) v

def expected (a t₁ t₂ d N₁ N₂ n : ℕ) (v : Fin n → Fin d → Bool) :
    Stack → List Bool :=
  Sum.elim (MatrixScalarWriterFrame.rawInput a d N₁ N₂ n
    (exactData a t₁ t₂ d n v)) (fun _ => [])

set_option maxHeartbeats 400000 in
theorem afterReverse_cleared_exact (a t₁ t₂ d N₁ N₂ n : ℕ)
    (v : Fin n → Fin d → Bool) (source secondDegree : List Bool)
    (hsource : source = (exactData a t₁ t₂ d n v).source) :
    BitMachineClearBank.cleared clearing
      (SamplerWriterPhysicalSequence.afterReverse a t₁ t₂ d N₁ N₂ n
        (SmallBiasSampler.fieldExponent (ExactConstruction.prefixLength a + 3)
          (SmallBiasSampler.exactDenominator d * (2 ^ 1) ^ t₁))
        (ExactConstruction.prefixLength a + 3) source secondDegree v) =
      expected a t₁ t₂ d N₁ N₂ n v := by
  have hfirst := SamplerExactPayloadArrays.firstTrace_stored a t₁ t₂ d n v
  funext k
  fin_cases k <;>
    (simp only [BitMachineClearBank.cleared];
     first
       | (rw [if_pos (by decide)]; rfl)
       | (rw [if_neg (by decide)];
          first | rfl | (simpa [expected, exactData] using hfirst) |
            (simpa [expected, exactData] using hsource)))

end EthInapproximability.CurrentPaper.SamplerWriterFinalCleanup
