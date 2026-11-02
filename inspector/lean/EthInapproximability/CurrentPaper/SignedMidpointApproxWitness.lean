import EthInapproximability.CurrentPaper.SignedMidpointApproxCanonical

/-!
# Extracting the executable midpoint callback from the paper's approximation premise

The polynomial approximation premise already supplies a finite machine and
its polynomial running-time witness. This file exposes that same witness to
the ordinary-input callback; it assumes no new per-branch runtime claim.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointApproxWitness

open EncodedETHTail BitMachine

theorem approximation_supplies_callback (allowance : ℕ → ℕ)
    (happrox : PolynomialApproximation allowance) :
    ∃ (answer : List Bool → ℤ) (M : Machine) (c d : ℕ),
      M.ComputesWithin (fun table => encodeInteger (answer table))
        (fun n => c * (n + 1) ^ d) ∧
      (∀ b : Branch,
        |answer b.table - (b.cost : ℤ)| ≤ (allowance b.table.length : ℤ)) ∧
      (∀ b : Branch, ∀ k : ℕ,
        (SignedMidpointApproxPacket.decisionMachine M).OutputsWithin
          (SignedMidpointApproxCanonical.packet M b.table b.threshold k)
          [branchAccept answer k b]
          (SignedMidpointApproxPolynomial.decisionCoefficient M c *
            ((SignedMidpointApproxCanonical.packet M b.table b.threshold k).length + 1) ^
              (d + 2))) := by
  obtain ⟨answer, ⟨M, c, d, hM⟩, herror⟩ := happrox
  refine ⟨answer, M, c, d, hM, ?_, ?_⟩
  · intro b
    exact herror b.exponent b.table b.length_eq
  · intro b k
    simpa only [branchAccept] using
      SignedMidpointApproxCanonical.callback_fixed_polynomial M answer c d hM
        b.table b.threshold k

end EthInapproximability.CurrentPaper.SignedMidpointApproxWitness
