import EthInapproximability.CurrentPaper.MatrixWeightedPower

/-!
# Charged arithmetic stages for the actual joint-tail diagonal address

The target is the literal `Construction.diagonal` address in raw `B`.
These are separately executable fixed-stack stages with exposed unary input
and output words.  A controller transferring the intermediate words among
the stages and into a protected-table cell reader remains to be built.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedDiagonalStages

open Construction MatrixStage4Codes MatrixStage4Digits MatrixWeightedDiagonal

variable {a s q cy : ℕ}

def tailCode (d : SecondRows a s q (Fin cy)) : ℕ :=
  (firstWordCode a s cy d.2).val % cy ^ (s + 1)

def wordCode (d : SecondRows a s q (Fin cy)) : ℕ :=
  (secondRowCode a s q cy d).val

def geomCode (a s q cy : ℕ) : ℕ :=
  ((binBase a s q cy) ^ s - 1) / (binBase a s q cy - 1)

def rawAddress (d : SecondRows a s q (Fin cy)) : ℕ :=
  tailCode d * (binBase a s q cy) ^ s + wordCode d * geomCode a s q cy

theorem rawAddress_eq (hcy : 0 < cy) (hb : 2 ≤ binBase a s q cy)
    (d : SecondRows a s q (Fin cy)) :
    rawAddress d = (rawColumnCode a s q cy (diagonal d)).val := by
  simpa [rawAddress, tailCode, wordCode, geomCode] using
    (diagonal_ordinal_arithmetic hcy hb d).symm

/-- Variable power for the bin-word base is physically computed. -/
theorem power_stage :
    ∃ t ≤ MatrixWeightedPower.powerBound (binBase a s q cy) s,
      MatrixWeightedPower.run t
        (MatrixWeightedPower.cfg (some (.inr .test)) (false,false)
          (List.replicate 1 true)
          (List.replicate (binBase a s q cy) true) []
          (List.replicate s true)) =
      MatrixWeightedPower.cfg none (false,false)
        (List.replicate ((binBase a s q cy) ^ s) true)
        (List.replicate (binBase a s q cy) true) [] [] :=
  MatrixWeightedPower.power_run _ _

/-- The tail modulus is another variable unary power, not a free scalar. -/
theorem tail_power_stage :
    ∃ t ≤ MatrixWeightedPower.powerBound cy (s + 1),
      MatrixWeightedPower.run t
        (MatrixWeightedPower.cfg (some (.inr .test)) (false,false)
          (List.replicate 1 true) (List.replicate cy true) []
          (List.replicate (s + 1) true)) =
      MatrixWeightedPower.cfg none (false,false)
        (List.replicate (cy ^ (s + 1)) true)
        (List.replicate cy true) [] [] :=
  MatrixWeightedPower.power_run _ _

/-- Unary predecessor of the bin power is charged by the fixed cut machine. -/
theorem power_predecessor_stage (hb : 2 ≤ binBase a s q cy) :
    ∃ t ≤ 3 * min ((binBase a s q cy) ^ s) 1 + 4,
      MatrixUnaryCut.run t
        (MatrixUnaryCut.cfg (some .scan) (false,true)
          (List.replicate ((binBase a s q cy) ^ s) true)
          (List.replicate 1 true) [] []) =
      MatrixUnaryCut.cfg none
        (decide (1 ≤ (binBase a s q cy) ^ s), false)
        (List.replicate (((binBase a s q cy) ^ s) - 1) true)
        (List.replicate 1 true) [] [] := by
  have hp : 1 ≤ (binBase a s q cy) ^ s := by
    exact pow_pos (by omega : 0 < binBase a s q cy) s
  simpa [show ¬(binBase a s q cy) ^ s < 1 by omega] using
    MatrixUnaryCut.cut_run ((binBase a s q cy) ^ s) 1

/-- Unary predecessor of the bin base is charged by the same fixed machine. -/
theorem base_predecessor_stage (hb : 1 ≤ binBase a s q cy) :
    ∃ t ≤ 3 * min (binBase a s q cy) 1 + 4,
      MatrixUnaryCut.run t
        (MatrixUnaryCut.cfg (some .scan) (false,true)
          (List.replicate (binBase a s q cy) true)
          (List.replicate 1 true) [] []) =
      MatrixUnaryCut.cfg none (true,false)
        (List.replicate (binBase a s q cy - 1) true)
        (List.replicate 1 true) [] [] := by
  simpa [hb, show ¬binBase a s q cy < 1 by omega] using
    MatrixUnaryCut.cut_run (binBase a s q cy) 1

/-- The tail suffix is a charged quotient/remainder result, assuming the
unary `cy^(s+1)` divisor has already been produced. -/
theorem tail_stage (d : SecondRows a s q (Fin cy)) :
    ∃ t ≤ 10 * (firstWordCode a s cy d.2).val +
      3 * cy ^ (s + 1) + 6,
      MatrixIndexQuotient.run t
        (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.start)
          MatrixIndexQuotient.initial
          (List.replicate (firstWordCode a s cy d.2).val true)
          (List.replicate (cy ^ (s + 1)) true) [] [] [] [] [] []) =
        MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear)
          MatrixIndexQuotient.initial
          (List.replicate (firstWordCode a s cy d.2).val true)
          (List.replicate (cy ^ (s + 1)) true) [] [] []
          (List.replicate (tailCode d) true)
          (List.replicate ((firstWordCode a s cy d.2).val / cy ^ (s + 1)) true) [] := by
  simpa [tailCode] using
    MatrixIndexSplit.split_run (firstWordCode a s cy d.2).val (cy ^ (s + 1))

/-- The geometric multiplier is physically divided after its numerator
and denominator have been prepared; both preparation steps are still
separate charged work, not host instructions. -/
theorem geometric_stage :
    ∃ t ≤ 10 * ((binBase a s q cy) ^ s - 1) +
      3 * (binBase a s q cy - 1) + 6,
      MatrixIndexQuotient.run t
        (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.start)
          MatrixIndexQuotient.initial
          (List.replicate ((binBase a s q cy) ^ s - 1) true)
          (List.replicate (binBase a s q cy - 1) true) [] [] [] [] [] []) =
        MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear)
          MatrixIndexQuotient.initial
          (List.replicate ((binBase a s q cy) ^ s - 1) true)
          (List.replicate (binBase a s q cy - 1) true) [] [] []
          (List.replicate (((binBase a s q cy) ^ s - 1) %
            (binBase a s q cy - 1)) true)
          (List.replicate (geomCode a s q cy) true) [] := by
  simpa [geomCode] using
    MatrixIndexSplit.split_run ((binBase a s q cy) ^ s - 1)
      (binBase a s q cy - 1)

/-- First multiply-add stage computes the repeated-bin contribution. -/
theorem word_product_stage (d : SecondRows a s q (Fin cy)) :
    MatrixAddressMachine.run
      (MatrixAddressMachine.exactTime (wordCode d) (geomCode a s q cy) 0)
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate (wordCode d) true)
        (List.replicate (geomCode a s q cy) true) [] [] [] []) =
      MatrixAddressMachine.cfg none false
        (List.replicate (wordCode d) true)
        (List.replicate (geomCode a s q cy) true) [] [] []
        (List.replicate (wordCode d * geomCode a s q cy) true) := by
  simpa using MatrixAddressMachine.address_run
    (wordCode d) (geomCode a s q cy) 0 false []

/-- Second multiply-add stage computes exactly the diagonal's raw address. -/
theorem final_address_stage (d : SecondRows a s q (Fin cy)) :
    MatrixAddressMachine.run
      (MatrixAddressMachine.exactTime (tailCode d)
        ((binBase a s q cy) ^ s) (wordCode d * geomCode a s q cy))
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate (tailCode d) true)
        (List.replicate ((binBase a s q cy) ^ s) true)
        (List.replicate (wordCode d * geomCode a s q cy) true) [] [] []) =
      MatrixAddressMachine.cfg none false
        (List.replicate (tailCode d) true)
        (List.replicate ((binBase a s q cy) ^ s) true)
        (List.replicate (wordCode d * geomCode a s q cy) true) [] []
        (List.replicate (rawAddress d) true) := by
  simpa [rawAddress] using MatrixAddressMachine.address_run
    (tailCode d) ((binBase a s q cy) ^ s)
    (wordCode d * geomCode a s q cy) false []

end EthInapproximability.CurrentPaper.MatrixWeightedDiagonalStages
