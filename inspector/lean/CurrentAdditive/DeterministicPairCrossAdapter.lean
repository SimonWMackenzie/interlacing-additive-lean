import CurrentAdditive.DeterministicPairProductLaw
import CurrentAdditive.ProductCross

/-! The exact iid pair-vector law discharges the product cross identities in
the long-suffix theorem, for actual retained pair images. -/

namespace CurrentAdditive.SuffixLong

open Paper2

variable {Z S : Type*} [Fintype Z] [Fintype S]

omit [Fintype S] in
theorem pairHit_product_cross (ν : FiniteLaw Z) {m q : ℕ}
    (decode : S → Fin q → Z) (e : Fin (2*m) → Fin q)
    (he : Function.Injective e) (K : Set S) :
    FourthMoment.PairCrossMoments (ν.iid q)
      (centeredPairAmbient ν decode e K) := by
  classical
  let ρ := ν.iid q
  let μ : Fin m → FiniteLaw Bool :=
    fun i => boolImageLaw ρ (pairHit decode e K i)
  have hprob (E : (Fin m → Bool) → Prop) :
      ρ.prob (fun c => E (fun i => pairHit decode e K i c)) =
        (FiniteLaw.pi μ).prob E := by
    exact pairHit_vector_product_law ν decode e he K E
  have hmass (i : Fin m) :
      (μ i).prob (fun b => b = true) =
        ρ.prob (fun c => pairHit decode e K i c) := by
    simp only [μ, boolImageLaw, FiniteLaw.prob_singleton]
  have hcenter :
      (fun i c => FourthMoment.boolCentered μ i (pairHit decode e K i c)) =
        centeredPairAmbient ν decode e K := by
    funext i c
    simp only [FourthMoment.boolCentered, centeredPairAmbient,
      FourthMoment.centeredPair, pairBaseMass, ρ] at *
    rw [hmass i]
  rw [← hcenter]
  exact FourthMoment.pairCrossMoments_of_indicator_law ρ
    (pairHit decode e K) μ hprob

#print axioms pairHit_product_cross

end CurrentAdditive.SuffixLong
