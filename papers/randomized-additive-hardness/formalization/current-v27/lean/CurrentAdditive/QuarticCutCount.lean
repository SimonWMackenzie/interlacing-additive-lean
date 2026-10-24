import CurrentAdditive.QuarticConstructor
import Paper2.PublicBitCountIdentity
import Paper2.SamplerParameterJoin

/-! The fixed physical B/R/N multiplication at literal quartic numeric values
equals the current scheduled constructor's exact random-tape length. -/

namespace Paper2.CurrentAdditive.QuarticCutCount

open EthInapproximability.CurrentPaper
open CurrentAdditive.RandomizedSchedule
open Paper2.CurrentAdditive.QuarticConstructor

def count27 (n m L Δ : ℕ) (γ : ℚ) (k : ℕ) : ℕ :=
  let p := LookupSeed.width L
  let s := SourceProfileParameters.width L
  let q₁ := s - 2
  let q₂ := SourceProfileParameters.outerWidth L
  let w := width27 L
  let Q := Q27 (V := Fin n) (E := Fin m) L γ Δ
  let mX := rows27 n m L Δ γ k
  let mY := cols27 n m L Δ γ k
  let B := SamplerParameterJoin.B n p s q₁ q₂ w Q
  let R := SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY
  let N := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
  N * (R * B)

theorem count27_eq_inputBitCount (n m L Δ : ℕ) (γ : ℚ) (k : ℕ) :
    count27 n m L Δ γ k =
      RecursiveSamplingMaterialization.inputBitCount
        (Fin n) (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2)
        (SourceProfileParameters.outerWidth L)
        (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
        (LookupSeed.width L) k (rows27 n m L Δ γ k)
        (cols27 n m L Δ γ k) := by
  unfold count27
  exact (Paper2.FixedTape.PublicCount.bitCount_eq_producer_product
    n (LookupSeed.width L) (SourceProfileParameters.width L)
    (SourceProfileParameters.width L - 2)
    (SourceProfileParameters.outerWidth L)
    (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
    k (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)).symm

theorem count27_eq_select27_inputBits {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) :
    count27 n m (Nat.clog 2 n) Δ γ k =
      (select27 hn edge Δ γ k).inputBits := by
  rw [select27_good hn edge Δ γ k hc]
  exact count27_eq_inputBitCount n m (Nat.clog 2 n) Δ γ k

#print axioms count27_eq_inputBitCount
#print axioms count27_eq_select27_inputBits

end Paper2.CurrentAdditive.QuarticCutCount
