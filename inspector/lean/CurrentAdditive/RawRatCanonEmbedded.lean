import CurrentAdditive.RawRatNumeratorDivision
import EthInapproximability.CurrentPaper.BitMachineStackRun
import Mathlib.Tactic

/-! Embed the fixed padding-removal machine in any three ambient stacks. -/
namespace CurrentAdditive.RawRatCanonEmbedded

open Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding

variable {K : Type*} [DecidableEq K]

def program (ι : Fin 3 ↪ K) : BG34Canon.Label →
    TM2.Stmt (fun _ : K => Bool) BG34Canon.Label BG34Canon.Control :=
  fun l => BitMachineStackEmbedding.stackStmt ι (BG34Canon.program l)

noncomputable def result (ι : Fin 3 ↪ K) (S : K → List Bool) : K → List Bool :=
  BitMachineStackEmbedding.bank ι S
    (![[], [], BG34Canon.canon (S (ι 0))] : Fin 3 → List Bool)

def clock (ι : Fin 3 ↪ K) (S : K → List Bool) : Nat :=
  (S (ι 0)).length + 1 + BG34Canon.trimTime (S (ι 0)).reverse

theorem run (ι : Fin 3 ↪ K) (S : K → List Bool)
    (hwork : S (ι 1) = []) (hout : S (ι 2) = []) :
    ((advance (program ι))^[clock ι S])
      (⟨some BG34Canon.Label.rev, none, S⟩ :
        TM2.Cfg (fun _ : K => Bool) BG34Canon.Label BG34Canon.Control) =
      ⟨none, none, result ι S⟩ := by
  have hs := BitMachineStackRun.run ι S BG34Canon.program
    (BG34Canon.cfg (some .rev) none (S (ι 0)) [] []) (clock ι S)
  have hbank : BitMachineStackEmbedding.bank ι S
      (![S (ι 0), [], []] : Fin 3 → List Bool) = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    fin_cases i <;> simp [hwork, hout]
  change ((advance (program ι))^[clock ι S])
      ⟨some BG34Canon.Label.rev, none,
        BitMachineStackEmbedding.bank ι S
          (![S (ι 0), [], []] : Fin 3 → List Bool)⟩ =
      BitMachineStackEmbedding.stackCfg ι S
        (BG34Canon.run (clock ι S)
          (BG34Canon.cfg (some .rev) none (S (ι 0)) [] [])) at hs
  rw [hbank] at hs
  change ((advance (program ι))^[clock ι S])
      ⟨some BG34Canon.Label.rev, none, S⟩ =
      BitMachineStackEmbedding.stackCfg ι S
        (BG34Canon.run
          ((S (ι 0)).length + 1 + BG34Canon.trimTime (S (ι 0)).reverse)
          (BG34Canon.cfg (some .rev) none (S (ι 0)) [] [])) at hs
  rw [BG34Canon.canon_run] at hs
  simpa [result, BG34Canon.cfg] using hs

theorem result_output (ι : Fin 3 ↪ K) (S : K → List Bool) :
    result ι S (ι 2) = (EncodedCommunication.bitsValue (S (ι 0))).bits := by
  rw [result, BitMachineStackEmbedding.bank_at]
  simpa only [Matrix.cons_val_fin_one, Matrix.cons_val_zero] using
    RawRatQuotientCanonical.canon_exact (S (ι 0))

theorem result_foreign (ι : Fin 3 ↪ K) (S : K → List Bool)
    (k : K) (hk : ¬ ∃ j : Fin 3, ι j = k) :
    result ι S k = S k :=
  BitMachineStackEmbedding.bank_outside ι S _ k hk

theorem clock_linear (ι : Fin 3 ↪ K) (S : K → List Bool) :
    clock ι S ≤ 2 * (S (ι 0)).length + 2 :=
  RawRatQuotientCanonical.physical_clock _

end CurrentAdditive.RawRatCanonEmbedded
