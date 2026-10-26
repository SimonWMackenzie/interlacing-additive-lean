import EthInapproximability.CurrentPaper.PrimeSamplerRuntime
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! Whole-bank raw endpoint for the actual chosen prime, not merely OutputsWithin. -/

namespace EthInapproximability.CurrentPaper.ChosenPrimeRaw

open Turing BitMachineEncoding

noncomputable section

abbrev Tester := PrimeSamplerPrimality.machine
abbrev Stack := PrimeSamplerSearch.Stack Tester
abbrev Label := PrimeSamplerSearch.Label Tester
abbrev Control := PrimeSamplerSearch.Control Tester
abbrev Config := PrimeSamplerSearch.Config Tester

def program := PrimeSamplerSearch.program Tester

def initial (X : ℕ) : Config :=
  PrimeSamplerSearch.adminCfg Tester .initialize (Tester.initial,none)
    (fun _ => []) (List.replicate X true) [] [] []

def bound (X : ℕ) : ℕ :=
  (2*X+2) + X * PrimeSamplerSearch.stepBound Tester (2*X)
    (40*(2*X+1)^3) + 2*X+1

/-- This is the production prime-search instruction table and its actual
whole-bank execution. The only input word is the unary threshold X; no
prime, size, or primality verdict is supplied. -/
theorem chosen_run (q t m : ℕ) :
    ∃ u ≤ bound (PrimeSampler.threshold q t m),
      ∃ v : Control, ∃ F : Stack → List Bool,
        ((advance program)^[u])
          (initial (PrimeSampler.threshold q t m)) = ⟨none,v,F⟩ ∧
        F (.inr 3) = List.replicate (PrimeSampler.prime q t m) true := by
  let X := PrimeSampler.threshold q t m
  let B := 40*(2*X+1)^3
  have htest : ∀ a ≤ 2*X,
      Tester.OutputsWithin (List.replicate a true)
        [PrimeSamplerTrial.trialPrime a] B := by
    intro a ha
    apply BitMachine.outputsWithin_mono Tester (PrimeSamplerPrimality.machine_outputs a)
    dsimp [B]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    omega
  obtain ⟨u,hu,hh,hout⟩ :=
    PrimeSamplerSearch.scan_run Tester X X (2*X) B (by omega) htest
  have hinit := PrimeSamplerSearch.initial_run Tester (List.replicate X true)
  have hrun : PrimeSamplerSearch.run Tester ((2*X+2)+u) (initial X) =
      PrimeSamplerSearch.run Tester u (PrimeSamplerSearch.ready Tester X X) := by
    have he : PrimeSamplerSearch.run Tester (2*X+2) (initial X) =
        PrimeSamplerSearch.ready Tester X X := by
      simpa only [initial, List.length_replicate] using hinit
    exact PrimeSamplerSearch.run_add Tester he u
  let c := PrimeSamplerSearch.run Tester u (PrimeSamplerSearch.ready Tester X X)
  have hc : c = (⟨none,c.var,c.stk⟩ : Config) := by
    change c.l = none at hh
    rcases c with ⟨l,v,stk⟩
    cases l with
    | none => rfl
    | some l => cases hh
  refine ⟨(2*X+2)+u, ?_, c.var, c.stk, ?_, ?_⟩
  · have hb := Nat.add_le_add_left hu (2*X+2)
    simpa only [bound, X, B, Nat.add_assoc] using hb
  · change PrimeSamplerSearch.run Tester ((2*X+2)+u) (initial X) = _
    rw [hrun]
    exact hc
  · change c.stk (.inr 3) = _
    simpa only [c, X, PrimeSamplerTrial.scan_primeSampler,
      Option.getD_some] using hout

#print axioms chosen_run

end
end EthInapproximability.CurrentPaper.ChosenPrimeRaw
