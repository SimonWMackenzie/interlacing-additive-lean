import CurrentAdditive.V40LawBankClock
import CurrentAdditive.RationalCanonicalCallback
import CurrentAdditive.CodeDTargetV2
import CurrentAdditive.V39GeneratedConstruction

set_option autoImplicit false
namespace CurrentAdditive.V40LawProductEntry
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open CodeDCodec
set_option maxHeartbeats 4000000

def input (index : ℕ) (x y : ℚ) : List Bool :=
  V40LawPacket.packet index.bits (CodeDPairProductTargetV2.pairBytes
    (CodeDCanonicalSource.rawOfRat x) (CodeDCanonicalSource.rawOfRat y))

def machine : BitMachine.Machine :=
  V40LawBankMap.liftMachine RationalCanonicalCallback.productMachine

/-- One fixed product/normalization program, preserving the exact binary
label field. Its polynomial coefficient precedes every label and rational. -/
theorem outputs : ∃ C : ℕ, ∀ (index : ℕ) (x y : ℚ),
    machine.OutputsWithin (input index x y) (CodeDTargetV2.alphabetEntry (index,x*y))
      (C*((input index x y).length+3)^97) := by
  obtain ⟨c,hc⟩:=RationalCanonicalCallback.product_outputs_all
  refine ⟨10*(c+1)*(RationalCanonicalCallback.productMachine.pushBound+1),?_⟩
  intro index x y
  have h:=hc (CodeDPairProductTargetV2.pairBytes
    (CodeDCanonicalSource.rawOfRat x) (CodeDCanonicalSource.rawOfRat y))
  rw [RationalCanonicalCallback.product_result_pair _ _
    (CodeDCanonicalSource.rawOfRat_valid x) (CodeDCanonicalSource.rawOfRat_valid y),
    CodeDCanonicalSource.rawOfRat_value,CodeDCanonicalSource.rawOfRat_value] at h
  exact V40LawBankMap.outputs_polynomial RationalCanonicalCallback.productMachine c 96
    index.bits _ _ h

/-- In particular this computes one actual inner-product input weight of
SourceData: the row-major Fin product label and the reduced product weight. -/
theorem inner_entry {q n : ℕ} [NeZero q] (μ : PositiveRationalLaw (Fin n)) :
    ∃ C : ℕ, ∀ j : Fin (q*n),
      let pair:=finProdFinEquiv.symm j
      machine.OutputsWithin (input j.val ((q:ℚ)⁻¹) (μ.weight pair.2))
        (CodeDTargetV2.alphabetEntry (j.val,
          (V39GeneratedConstruction.reindex finProdFinEquiv
            (V39GeneratedConstruction.product (V39GeneratedConstruction.uniform q) μ)).weight j))
        (C*((input j.val ((q:ℚ)⁻¹) (μ.weight pair.2)).length+3)^97) := by
  obtain ⟨C,hC⟩:=outputs
  exact ⟨C,fun j => hC j.val _ _⟩

#print axioms outputs
#print axioms inner_entry
end
end CurrentAdditive.V40LawProductEntry
