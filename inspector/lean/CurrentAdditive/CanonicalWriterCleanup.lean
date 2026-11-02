import CurrentAdditive.CanonicalWriterCoordValue
import EthInapproximability.CurrentPaper.BitMachineClearBank

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineClearBank

/-- The six temporary coordinates used by the physical entry callback. -/
def canonicalCleanupSlots : Fin 6 → CanonicalCell :=
  ![.inl 7, .inl 8, .inl 9, .inl 10, .inl 11, .inl 12]

inductive CanonicalCleanupLabel where
  | c0 | c1 | c2 | c3 | c4 | c5 | finish | done
  deriving DecidableEq, Fintype

def canonicalCleanupLabels : Fin 7 → CanonicalCleanupLabel :=
  ![.c0, .c1, .c2, .c3, .c4, .c5, .finish]

def canonicalCleanupProgram : CanonicalCleanupLabel →
    TM2.Stmt (fun _ : CanonicalCell => Bool) CanonicalCleanupLabel
      (Unit × Option Bool)
  | .c0 => clearStep (.inl 7) .c0 .c1
  | .c1 => clearStep (.inl 8) .c1 .c2
  | .c2 => clearStep (.inl 9) .c2 .c3
  | .c3 => clearStep (.inl 10) .c3 .c4
  | .c4 => clearStep (.inl 11) .c4 .c5
  | .c5 => clearStep (.inl 12) .c5 .finish
  | .finish => finishStep id .done
  | .done => .halt

def canonicalCleanupTime (S : CanonicalCell → List Bool) : ℕ :=
  (∑ i : Fin 6, (S (canonicalCleanupSlots i)).length) + 8

/-- The literal fixed program pops every temporary coordinate and leaves
all other writer cells untouched, charging each popped symbol. -/
theorem canonical_cleanup_run (S : CanonicalCell → List Bool) :
    ((advance canonicalCleanupProgram)^[canonicalCleanupTime S])
      (⟨some .c0, ((), none), S⟩ :
        TM2.Cfg (fun _ : CanonicalCell => Bool) _ _) =
      ⟨none, ((), none), cleared canonicalCleanupSlots S⟩ := by
  have hinj : Function.Injective canonicalCleanupSlots := by decide
  have hsteps : ∀ i : Fin 6,
      canonicalCleanupProgram (canonicalCleanupLabels i.castSucc) =
        clearStep (canonicalCleanupSlots i)
          (canonicalCleanupLabels i.castSucc)
          (canonicalCleanupLabels i.succ) := by
    intro i
    fin_cases i <;> rfl
  have hfinish : canonicalCleanupProgram
      (canonicalCleanupLabels (Fin.last 6)) =
        finishStep id .done := rfl
  have hr := clear_bank_run canonicalCleanupProgram id
    CanonicalCleanupLabel.done 6 canonicalCleanupSlots hinj
    canonicalCleanupLabels hsteps hfinish () S
  have hr' :
      ((advance canonicalCleanupProgram)^[
          (∑ i : Fin 6, (S (canonicalCleanupSlots i)).length) + 7])
        (⟨some .c0, ((), none), S⟩ :
          TM2.Cfg (fun _ : CanonicalCell => Bool) _ _) =
        ⟨some .done, ((), none), cleared canonicalCleanupSlots S⟩ := by
    simpa only [show canonicalCleanupLabels 0 = CanonicalCleanupLabel.c0 from rfl,
      id_eq] using hr
  unfold canonicalCleanupTime
  rw [show (∑ i : Fin 6, (S (canonicalCleanupSlots i)).length) + 8 =
    ((∑ i : Fin 6, (S (canonicalCleanupSlots i)).length) + 7) + 1 by omega,
    Function.iterate_succ_apply', hr']
  rfl

#print axioms canonical_cleanup_run

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
