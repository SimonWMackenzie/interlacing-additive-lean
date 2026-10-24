import CurrentAdditive.CanonicalNumericEntry
import Paper2.YaoIdxDecode

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing
open Paper2.YaoIndexDecoder
open EthInapproximability.CurrentPaper.BitMachineEncoding

variable {J : Type*} [DecidableEq J]

/-- The existing fixed physical index-decoder, supplied with canonical row
and column divisors, writes exactly the five canonical coordinates. It
does not yet compute the selector digit, edge position, or field bit. -/
theorem physical_canonical_index_decode {v : ℕ} (b t d : ℕ)
    (ι : Fin 14 ↪ J) (S : J → List Bool)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d))
    (hx : S (ι 0) = List.replicate i.val true)
    (hy : S (ι 1) = List.replicate j.val true)
    (hsel : S (ι 2) = List.replicate ((2 ^ b) ^ (2 ^ (t - 1))) true)
    (hpay : S (ι 3) = List.replicate ((2 ^ d) ^ 2) true)
    (hpow : S (ι 4) = List.replicate (2 ^ b) true)
    (hempty : ∀ k : Fin 14, 5 ≤ k.val → S (ι k) = []) :
    ∃ total ≤ (2 * i.val + 2) +
        (8 * i.val + 3 * ((2 ^ b) ^ (2 ^ (t - 1))) + 4) +
        (2 * j.val + 2) + (8 * j.val + 3 * ((2 ^ d) ^ 2) + 4) +
        (8 * (j.val / ((2 ^ d) ^ 2)) + 3 * (2 ^ b) + 4) + 4,
      ((advance (program ι))^[total])
        (⟨some startLabel, startControl, S⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
      ⟨none, startControl,
        Function.update (Function.update (Function.update (Function.update
          (Function.update S (ι 8)
            (List.replicate (((rowIndex v b t).symm i).1.val) true))
          (ι 9) (List.replicate (((rowIndex v b t).symm i).2.val) true))
          (ι 10) (List.replicate (((columnIndex b t d).symm j).1.val) true))
          (ι 11) (List.replicate (((columnIndex b t d).symm j).2.1.val) true))
          (ι 12) (List.replicate (((columnIndex b t d).symm j).2.2.val) true)⟩ := by
  obtain ⟨total, htime, hrun⟩ := physical_index_decode ι S i.val j.val
    ((2 ^ b) ^ (2 ^ (t - 1))) ((2 ^ d) ^ 2) (2 ^ b)
    hx hy hsel hpay hpow
    (hempty 5 (by omega)) (hempty 6 (by omega))
    (hempty 7 (by omega)) (hempty 8 (by omega))
    (hempty 9 (by omega)) (hempty 10 (by omega))
    (hempty 11 (by omega)) (hempty 12 (by omega))
    (hempty 13 (by omega))
  refine ⟨total, htime, ?_⟩
  rw [hrun]
  obtain ⟨hrv, hrz⟩ := row_decode_numeric v b t i
  obtain ⟨hcg, hca, hcl⟩ := column_decode_numeric b t d j
  simp only [outBank, hrv, hrz, hcg, hca, hcl]

#print axioms physical_canonical_index_decode

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
