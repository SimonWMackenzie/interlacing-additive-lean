import CurrentAdditive.YaoSuffixPower
import EthInapproximability.CurrentPaper.SourceClauseFixedUnary

/-! Append the physical unary words Q, b and the fixed-t constant to the
retained unary cut index. The resulting bank 3 is the exact degree word. -/

namespace CurrentAdditive.SmallBias.YaoDegreePrinter

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding MatrixStage4ScalarPreparationOps

def copyQ : Fin 3 ↪ Fin 16 := ⟨![5, 3, 7], by decide⟩
def copyB : Fin 3 ↪ Fin 16 := ⟨![0, 3, 7], by decide⟩
def fixedPart (t : ℕ) : ℕ := 3 * t + 3

def afterQ (t : ℕ) :=
  BitMachineRawSequence.program (copyProgram copyB)
    (SourceClauseFixedUnary.program (3 : Fin 16) (fixedPart t))
    (0 : SourceClauseFixedUnary.Label (fixedPart t)) none ()

def program (t : ℕ) :=
  BitMachineRawSequence.program (copyProgram copyQ) (afterQ t)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none (none, ())

theorem run (S : Fin 16 → List Bool) (b i Q t : ℕ)
    (h0 : S 0 = List.replicate b true)
    (h3 : S 3 = List.replicate i true)
    (h5 : S 5 = List.replicate Q true)
    (h7 : S 7 = []) :
    ∃ u ≤ (2 * Q + 2) + (2 * b + 2) + (fixedPart t + 1) + 2,
      ((advance (program t))^[u])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, (none, ())), S⟩ : TM2.Cfg (fun _ : Fin 16 => Bool) _ _) =
      ⟨none, (none, (none, ())),
        Function.update S 3
          (List.replicate (Q + b + i + fixedPart t) true)⟩ := by
  let S1 := Function.update S (3 : Fin 16)
    (List.replicate Q true ++ List.replicate i true)
  have hq : ((advance (copyProgram copyQ))^[2 * Q + 2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : Fin 16 => Bool)
        BitMachineCopy.Label (Option Bool)) = ⟨none, none, S1⟩ := by
    have hr := copy_run copyQ S h7
    simpa [copyQ, S1, h5, h3] using hr
  let S2 := Function.update S1 (3 : Fin 16)
    (List.replicate b true ++ S1 3)
  have hb : ((advance (copyProgram copyB))^[2 * b + 2])
      (⟨some .scan, none, S1⟩ : TM2.Cfg (fun _ : Fin 16 => Bool)
        BitMachineCopy.Label (Option Bool)) = ⟨none, none, S2⟩ := by
    have h7' : S1 (copyB 2) = [] := by simp [S1, copyB, h7]
    have hr := copy_run copyB S1 h7'
    simpa [copyB, S2, S1, h0] using hr
  have h3S2 : S2 3 = List.replicate (b + Q + i) true := by
    simp [S2, S1, Nat.add_assoc]
  have hstart : SourceClauseFixedUnary.state (3 : Fin 16) S2
      (0 : SourceClauseFixedUnary.Label (fixedPart t))
      (List.replicate (b + Q + i) true) =
      (⟨some 0, (), S2⟩ : TM2.Cfg (fun _ : Fin 16 => Bool)
        (SourceClauseFixedUnary.Label (fixedPart t)) Unit) := by
    simp [SourceClauseFixedUnary.state, h3S2]
  have hp := SourceClauseFixedUnary.run_from (3 : Fin 16) S2
    (0 : SourceClauseFixedUnary.Label (fixedPart t)) (fixedPart t)
    (by simp) (List.replicate (b + Q + i) true)
  rw [hstart] at hp
  have hfinal : Function.update S2 3
      (List.replicate (fixedPart t) true ++
        List.replicate (b + Q + i) true) =
      Function.update S 3
        (List.replicate (Q + b + i + fixedPart t) true) := by
    simp only [← List.replicate_add]
    have he : fixedPart t + (b + Q + i) = Q + b + i + fixedPart t := by omega
    rw [he]
    simp [S2, S1, Function.update_idem]
  rw [hfinal] at hp
  obtain ⟨u2, hu2, hr2⟩ := BitMachineRawSequence.runs
    (copyProgram copyB)
    (SourceClauseFixedUnary.program (3 : Fin 16) (fixedPart t))
    BitMachineCopy.Label.scan (0 : SourceClauseFixedUnary.Label (fixedPart t))
    none none () () S1 S2 _ (2 * b + 2) (fixedPart t + 1) hb hp
  obtain ⟨u, hu, hr⟩ := BitMachineRawSequence.runs
    (copyProgram copyQ) (afterQ t)
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, ()) (none, ()) S S1 _ (2 * Q + 2) u2 hq hr2
  exact ⟨u, by omega, by simpa [program, afterQ] using hr⟩

#print axioms run

end CurrentAdditive.SmallBias.YaoDegreePrinter
