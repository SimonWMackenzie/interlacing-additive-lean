import Paper2.YaoEntryInputLoader
import EthInapproximability.CurrentPaper.ExactParameterBranchInstall

/-! Literal serialized randomness enters on one raw Boolean input stack.
A charged source-preserving copy loads the evaluator's flat-source stack 3;
neither a decoded table nor a pre-extracted slice is supplied. -/

namespace Paper2.YaoEntryControllerJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoEntryParameterJoin
open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization

abbrev InputStack (t lambda : ℕ) := RouteStack t lambda ⊕ Unit

def tapeSource (t lambda : ℕ) : InputStack t lambda := .inr ()
def tapeTarget (t lambda : ℕ) : InputStack t lambda := .inl (.inr (.inl 3))
def tapeScratch (t lambda : ℕ) : InputStack t lambda := .inl (.inr (.inr ()))

def tapeCopyEmbed (t lambda : ℕ) : Fin 3 ↪ InputStack t lambda where
  toFun := ![tapeSource t lambda,tapeTarget t lambda,tapeScratch t lambda]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [tapeSource,tapeTarget,tapeScratch]

noncomputable def tapeCopyProgram (t lambda : ℕ) :=
  ExactParameterBranchInstall.copyProgram (tapeCopyEmbed t lambda)

noncomputable def tapeRawBank {t lambda : ℕ} (S₀ : PayloadStack t lambda → List Bool)
    (source : List Bool) : InputStack t lambda → List Bool :=
  Sum.elim (Sum.elim S₀ (routedForeign [])) (fun _ => source)

noncomputable def tapeLoadedBank {t lambda : ℕ} (S₀ : PayloadStack t lambda → List Bool)
    (source : List Bool) : InputStack t lambda → List Bool :=
  Sum.elim (Sum.elim S₀ (routedForeign source)) (fun _ => source)

theorem tape_raw_source (t lambda : ℕ)
    (S₀ : PayloadStack t lambda → List Bool) (source : List Bool) :
    tapeRawBank S₀ source (tapeSource t lambda) = source := rfl

theorem tape_raw_target (t lambda : ℕ)
    (S₀ : PayloadStack t lambda → List Bool) (source : List Bool) :
    tapeRawBank S₀ source (tapeTarget t lambda) = [] := rfl

theorem tape_raw_scratch (t lambda : ℕ)
    (S₀ : PayloadStack t lambda → List Bool) (source : List Bool) :
    tapeRawBank S₀ source (tapeScratch t lambda) = [] := rfl

theorem tape_loaded_eq_update (t lambda : ℕ)
    (S₀ : PayloadStack t lambda → List Bool) (source : List Bool) :
    Function.update (tapeRawBank S₀ source) (tapeTarget t lambda) source =
      tapeLoadedBank S₀ source := by
  classical
  funext j
  rcases j with (x|u)
  · rcases x with (x|x)
    · simp [tapeRawBank,tapeLoadedBank,tapeTarget]
    · rcases x with (i|u)
      · fin_cases i <;>
          simp [tapeRawBank,tapeLoadedBank,tapeTarget,routedForeign]
      · simp [tapeRawBank,tapeLoadedBank,tapeTarget,routedForeign]
  · simp [tapeRawBank,tapeLoadedBank,tapeTarget]

theorem physical_load_serialized_tape (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (S₀ : PayloadStack t lambda → List Bool) :
    ∃ steps ≤ 2*tapeBitCount t b lambda+2,
      ((advance (tapeCopyProgram t lambda))^[steps])
        (⟨some .scan,none,tapeRawBank S₀ bits.val⟩ :
          TM2.Cfg (fun _ : InputStack t lambda => Bool)
            BitMachineCopy.Label (Option Bool)) =
        ⟨none,none,tapeLoadedBank S₀ bits.val⟩ ∧
      tapeLoadedBank S₀ bits.val (tapeSource t lambda) = bits.val ∧
      tapeLoadedBank S₀ bits.val (tapeTarget t lambda) = bits.val := by
  obtain ⟨steps,hsteps,hrun⟩ :=
    ExactParameterBranchInstall.copy_run (tapeCopyEmbed t lambda)
      (tapeRawBank S₀ bits.val) bits.val
      (tape_raw_source t lambda S₀ bits.val)
      (tape_raw_target t lambda S₀ bits.val)
      (tape_raw_scratch t lambda S₀ bits.val)
  refine ⟨steps,?_,?_,rfl,rfl⟩
  · simpa only [bits.property] using hsteps
  · have hrun' := hrun
    change ((advance (tapeCopyProgram t lambda))^[steps])
      (⟨some .scan,none,tapeRawBank S₀ bits.val⟩ :
        TM2.Cfg (fun _ : InputStack t lambda => Bool)
          BitMachineCopy.Label (Option Bool)) =
      ⟨none,none,Function.update (tapeRawBank S₀ bits.val)
        (tapeTarget t lambda) bits.val⟩ at hrun'
    rw [tape_loaded_eq_update] at hrun'
    exact hrun'

#print axioms physical_load_serialized_tape

end Paper2.YaoEntryControllerJoin
