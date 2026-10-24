import CurrentAdditive.QuarticSquareEncodedSize

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.AEth4
open EthInapproximability.CurrentPaper

theorem squareHeaderClock_bound27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (Φ : EncodedCNF.Formula) :
    let k := Paper2.Unit4Shell.Asymptotics.kOf Φ.variables
    let L := squareEncodedLength27 hn edge Δ γ k
    squareHeaderClock27 hn edge Δ γ Φ ≤
      (2 * (EncodedCNF.encode Φ).length +
        Paper2.Unit4Shell.KofFront.BK * (Φ.variables + 1) ^ 2 +
        2 * k + 6) +
        2 * (2 * k + 1 + L) + 2 +
        4 * (2 * k + 1 + L + 1) ^ 2 := by
  intro k L
  let o := select27 hn edge Δ γ k
  let q := SquarePadding.side o.rows o.cols
  let i : EncodedCommunication.Instance :=
    ⟨q, q, o.budget, List.replicate (q * q) false⟩
  have hgc := GrowHeader.clock_le k i
  have hlen : (EncodedCommunication.encodeInstance i).length = L := by
    rw [EncodedCommunication.encodeInstance_length]
    simp only [i, L, squareEncodedLength27,
      List.length_replicate]
    rfl
  rw [EncodedComplexity.pair_length, List.length_replicate, hlen] at hgc
  change GrowHeader.clock k q q o.budget ≤
    4 * (2 * k + 1 + L + 1) ^ 2 at hgc
  change (2 * (EncodedCNF.encode Φ).length +
      Paper2.Unit4Shell.KofFront.BK * (Φ.variables + 1) ^ 2 +
      2 * k + 6) + 2 * (2 * k + 1 + L) + 2 +
      GrowHeader.clock k q q o.budget ≤ _
  omega

#print axioms squareHeaderClock_bound27

end Paper2.CurrentAdditive.QuarticClassEndpoint
