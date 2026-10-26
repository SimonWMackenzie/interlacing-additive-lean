import Paper2.SamplerParameterJoin
import Paper2.RecursiveSamplingMaterialization

/-!
# Public bit-count identity at the physical producer exit

The scheduled tape count is `N*(R*B)`. Here `N` and `R` are the actual
unary words left by `SamplerNRProducer.program` when run from its raw-count
start bank; `B` is the bit-width output of the joined public producer. This
is an exact same-object identity, not a machine that yet multiplies these
words or truncates an outer tape. It locates the remaining physical stage.
-/

namespace Paper2.FixedTape.PublicCount

open EthInapproximability.CurrentPaper

/-- The formal count in the selected scheduled law is exactly the product of
the three numbers produced by the public parameter machinery. -/
theorem bitCount_eq_producer_product (n p s q₁ q₂ w Q k mX mY : ℕ) :
    RecursiveSamplingMaterialization.inputBitCount (Fin n)
      s q₁ q₂ w Q p k mX mY =
      SamplerNRProducer.N s q₁ q₂ w Q p k mX mY *
        (SamplerNRProducer.R s q₁ q₂ w Q p k mX mY *
          SamplerParameterJoin.B n p s q₁ q₂ w Q) := by
  simp [RecursiveSamplingMaterialization.inputBitCount,
    RecursiveSamplingTape.bitCount, SamplerNRProducer.N, SamplerNRProducer.R,
    SamplerParameterJoin.B, SamplerParameterJoin.M]

/-- The actual finite controller reaches a bank with the two unary words
whose lengths are `N` and `R`. Their lengths, together with the public
bit-width `B`, give *the very same* `inputBitCount` as the scheduled law.
All six producing phases and their clock come from `SamplerNRProducer.run`. -/
theorem nr_run_bitCount (n p s q₁ q₂ w Q k mX mY : ℕ) :
    ∃ (t : ℕ) (F : SamplerNRProducer.Stack → List Bool),
      t ≤ SamplerNRProducer.clock s q₁ q₂ w Q p k mX mY ∧
      ((BitMachineEncoding.advance SamplerNRProducer.program)^[t])
        (⟨some SamplerNRProducer.startLabel, SamplerNRProducer.startControl,
          SamplerNRProducer.initialBank s q₁ q₂ w Q p k mX mY⟩ :
          Turing.TM2.Cfg (fun _ : SamplerNRProducer.Stack => Bool) _ _) =
        ⟨none, (SamplerNRProducer.c12345, none), F⟩ ∧
      F (.inl 22) = List.replicate (SamplerNRProducer.N s q₁ q₂ w Q p k mX mY) true ∧
      F (.inl 23) = List.replicate (SamplerNRProducer.R s q₁ q₂ w Q p k mX mY) true ∧
      RecursiveSamplingMaterialization.inputBitCount (Fin n)
        s q₁ q₂ w Q p k mX mY =
          (F (.inl 22)).length *
            ((F (.inl 23)).length * SamplerParameterJoin.B n p s q₁ q₂ w Q) := by
  obtain ⟨t, F, ht, hrun, hR, hN, _⟩ :=
    SamplerNRProducer.run s q₁ q₂ w Q p k mX mY
  refine ⟨t, F, ht, hrun, hN, hR, ?_⟩
  rw [hN, hR]
  simp only [List.length_replicate]
  exact bitCount_eq_producer_product n p s q₁ q₂ w Q k mX mY

end Paper2.FixedTape.PublicCount

#print axioms Paper2.FixedTape.PublicCount.nr_run_bitCount
