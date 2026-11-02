import CurrentAdditive.CanonicalEncodedHeader
import CurrentAdditive.FieldSearchPackedCompletion
import CurrentAdditive.SmallBiasPublicDegree

/-! The public-degree global field search and ordered list printer write the
exact packed word expected in canonical writer bank cell 5.  In particular,
the initial machine state contains no successful modulus or search tail. -/

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open CurrentAdditive.SmallBias
open CurrentAdditive.FieldSearchCompletion
open CurrentAdditive.FiniteFieldConstructor.TrialSearch
open Paper2.YaoLookup

theorem physical_canonical_field_bank_cell {v e : ℕ} (t : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    let b := paddedEdgeBits e
    let d := publicFieldDegree b t
    let n := 2 ^ b * (2 ^ t * 2 ^ t + 1)
    ∃ c < 2 ^ d,
      firstPassing d = some (monicBits d c) ∧
      ∃ steps ≤ 55 * 2 ^ d * 2 ^ (d / 2) * (d + 1) ^ 2 + 2 +
          CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.timeBound d c n,
        (Unified.run steps
          (concreteTailFreeStart d n
            (initialConfig d))).l =
          none ∧
        (Unified.run steps
          (concreteTailFreeStart d n
            (initialConfig d))).stk
          (CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff.printerSlots
            CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output) =
          canonicalWriterBank b t d ((firstPassing d).getD 0) edges 5 := by
  dsimp only
  let b := paddedEdgeBits e
  let d := publicFieldDegree b t
  let n := 2 ^ b * (2 ^ t * 2 ^ t + 1)
  obtain ⟨c, hc, hfirst, steps, hsteps, hhalt, hout⟩ :=
    physical_firstPassing_packed d n (public_degree_pos b t)
  refine ⟨c, hc, hfirst, steps, hsteps, hhalt, ?_⟩
  rw [hout, hfirst]
  rfl

#print axioms physical_canonical_field_bank_cell

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
