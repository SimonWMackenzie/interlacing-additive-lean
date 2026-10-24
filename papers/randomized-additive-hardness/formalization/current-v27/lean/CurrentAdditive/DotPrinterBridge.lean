import CurrentAdditive.DotMachine
import CurrentAdditive.PackedDotMachine
import CurrentAdditive.BitPrinter

/-!
Literal connection from the physical five-stack dot program to the frozen
constructor agent's Nat-bit `BitPrinter.dot` convention.
-/

namespace CurrentAdditive.FiniteFieldMachine.DotPrinterBridge

open CurrentAdditive.FiniteFieldMachine.DotMachine
open CurrentAdditive.FiniteFieldConstructor.BitPrinter

theorem run_bitPrinter_dot (d x z : ℕ) (out : List Bool) :
    run (2 * d + 3) (cfg (some .scan) initial (natBits d x) (natBits d z) [] [] out) =
      cfg none (dot d x z, none, none) (natBits d x) (natBits d z)
        [] [] (dot d x z :: out) := by
  simpa only [dot] using run_natBits_dot d x z out

theorem packedMachine_outputs_bitPrinter_dot (d x z : ℕ) :
    PackedDotMachine.machine.OutputsWithin
      (PackedDotMachine.pack (natBits d x) (natBits d z))
      [dot d x z] (d + 1) := by
  have h := PackedDotMachine.machine_outputs (natBits d x) (natBits d z)
    (by simp [natBits])
  have heq : DotMachine.dotAux false (natBits d x) (natBits d z) =
      dot d x z := by
    exact DotMachine.dotAux_natBits false (List.range d) x z
  rw [heq] at h
  simpa only [natBits, List.length_map, List.length_range] using h

#print axioms run_bitPrinter_dot
#print axioms packedMachine_outputs_bitPrinter_dot

end CurrentAdditive.FiniteFieldMachine.DotPrinterBridge
