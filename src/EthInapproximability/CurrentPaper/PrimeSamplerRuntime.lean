import EthInapproximability.CurrentPaper.PrimeSamplerSearch
import EthInapproximability.CurrentPaper.PrimeSamplerPrimality

/-!
# Operational least-prime search for the explicit sampler

Source: frozen v8 `B-effectivity-details.tex`, the trial-division search in
`lem:paper-explicit-balanced-family`. This module instantiates the bounded
physical search with the proved actual unary primality machine. Thus no
primality oracle, local execution premise, or unit-cost arithmetic remains.
The interface uses unary thresholds and unary prime outputs. Its degree-five
runtime is polynomial in X, as required for the prime-search phase, and
singly exponential when X is bounded by an exponential naming scale.
Binary threshold preparation, compact output serialization, and polynomial
family entry evaluation are separate implementation obligations.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerRuntime

noncomputable abbrev tester := PrimeSamplerPrimality.machine

noncomputable def machine : BitMachine.Machine := PrimeSamplerSearch.machine tester

noncomputable def coefficient : ℕ := PrimeSamplerSearch.coefficient tester 40 * 2^5

theorem unary_outputs (input : List Bool) :
    machine.OutputsWithin input
      (List.replicate (PrimeSamplerTrial.firstPrime input.length) true)
      (coefficient*(input.length+1)^5) := by
  have h := PrimeSamplerSearch.outputs tester input (40*(2*input.length+1)^3) (by
    intro n hn
    apply BitMachine.outputsWithin_mono tester (PrimeSamplerPrimality.machine_outputs n)
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    omega)
  exact BitMachine.outputsWithin_mono _ h (PrimeSamplerSearch.polynomial_bound tester input.length 40 3)

theorem unary_polytime :
    BitMachine.Polytime (fun input => List.replicate (PrimeSamplerTrial.firstPrime input.length) true) :=
  ⟨machine,coefficient,5,unary_outputs⟩

/-- The concrete search returns exactly the prime used by the existing
balanced family, not an arbitrary prime from a nonempty window. -/
theorem sampler_prime_outputs (q t m : ℕ) :
    machine.OutputsWithin (List.replicate (PrimeSampler.threshold q t m) true)
      (List.replicate (PrimeSampler.prime q t m) true)
      (coefficient*(PrimeSampler.threshold q t m+1)^5) := by
  simpa only [List.length_replicate, PrimeSamplerTrial.firstPrime_eq_sampler] using
    unary_outputs (List.replicate (PrimeSampler.threshold q t m) true)

/-- Explicit singly exponential accounting for this search phase. -/
theorem sampler_prime_exponential (q t m p c : ℕ)
    (hX : PrimeSampler.threshold q t m ≤ 2^(c*p)) :
    machine.OutputsWithin (List.replicate (PrimeSampler.threshold q t m) true)
      (List.replicate (PrimeSampler.prime q t m) true)
      (coefficient*2^(5*(c*p+1))) := by
  apply BitMachine.outputsWithin_mono _ (sampler_prime_outputs q t m)
  apply Nat.mul_le_mul_left
  have hp : 1 ≤ 2^(c*p) := Nat.one_le_pow _ _ (by omega)
  calc
    (PrimeSampler.threshold q t m+1)^5 ≤ (2^(c*p+1))^5 := by
      apply Nat.pow_le_pow_left
      rw [pow_succ]
      omega
    _ = _ := by rw [← pow_mul]; congr 1; omega

end EthInapproximability.CurrentPaper.PrimeSamplerRuntime
