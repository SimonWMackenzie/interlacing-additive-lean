import CurrentAdditive.CanonicalPhysicalIndex

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing Paper2.YaoIndexDecoder
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.SmallBias

variable {J : Type*} [DecidableEq J]

/-- A second physical unary division splits a canonical pair-seed label
into its two `Fin(2^d)` labels. The dividend cell is consumed; callers
must copy it first when they need to preserve the original label. -/
theorem physical_seed_pair_split (d : ℕ)
    (ι : Fin 6 ↪ J) (S : J → List Bool)
    (ℓ : Fin ((2 ^ d) ^ 2))
    (hlabel : S (ι 0) = List.replicate ℓ.val true)
    (hR : S (ι 1) = List.replicate (2 ^ d) true)
    (h2 : S (ι 2) = []) (h3 : S (ι 3) = [])
    (h4 : S (ι 4) = []) (h5 : S (ι 5) = []) :
    ∃ steps ≤ 8 * ℓ.val + 3 * (2 ^ d) + 4,
      ((advance (divProgram ι))^[steps])
        (⟨some .start, false, S⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
      ⟨none, false,
        Function.update (Function.update (Function.update S (ι 0) [])
          (ι 3) (List.replicate (((printerPairLabel d).symm ℓ).2.val) true))
          (ι 4) (List.replicate (((printerPairLabel d).symm ℓ).1.val) true)⟩ := by
  obtain ⟨steps, hsteps, hrun⟩ := div_run ι S ℓ.val (2 ^ d)
    hlabel hR h2 h3 h4 h5
  refine ⟨steps, hsteps, ?_⟩
  rw [hrun]
  obtain ⟨hx, hy⟩ := seed_pair_decode_numeric d ℓ
  simp only [hx, hy]

#print axioms physical_seed_pair_split

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
