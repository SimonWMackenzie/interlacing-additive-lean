import CurrentAdditive.QuarticSourceSizeNumeric
import Paper2.A4T24RuntimeComposed

/-! The charged source prefix is eventually linear in the effective source tape length. -/

namespace Paper2.CurrentAdditive.QuarticSourceRawFit

open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition

theorem formula_and_raw_fit
    (cs : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      (EncodedCNF.encode Φ.val).length ≤ Paper2.AEth.expLen Φ.val.variables ∧
      ∀ tape : List Bool,
        (tape.take (Paper2.AEth3.cutLen Φ.val)).length ≤
          5 * Paper2.AEth.expLen Φ.val.variables := by
  obtain ⟨N₁, hN₁⟩ := Paper2.AEth3.bits_fit 3 0
  refine ⟨max N₁ (28 * cs + 9), ?_⟩
  intro Φ hsparse hlarge
  let N := Φ.val.variables
  let U := Paper2.AEth.expLen N
  have h1 : N₁ ≤ N := (le_max_left _ _).trans hlarge
  have h2 : 28 * cs + 9 ≤ N := (le_max_right _ _).trans hlarge
  have hcube := Paper2.Unit4Shell.T24RuntimeComposed.encode_length_cube
    cs Φ hsparse h2
  have hbudget := hN₁ N h1 N (by simp)
  have hexp : 3 ≤ 3 * (kOf N + 1) := by omega
  have hcube' : (N + 2) ^ 3 ≤ (N + 2) ^ (3 * (kOf N + 1)) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hX : (EncodedCNF.encode Φ.val).length ≤ U := by
    dsimp [N, U] at *
    omega
  refine ⟨hX, ?_⟩
  intro tape
  have htake := List.length_take_le (Paper2.AEth3.cutLen Φ.val) tape
  have hcut := Paper2.AEth3.cutLen_eq Φ.val
  have hU : 1 ≤ U := Nat.one_le_two_pow
  dsimp only [U, N] at *
  omega

#print axioms formula_and_raw_fit

end Paper2.CurrentAdditive.QuarticSourceRawFit
