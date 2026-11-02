import CurrentAdditive.YaoSuffixCut
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

/-! The checked subtraction controller followed by the checked unary power
controller leaves the cut index in bank 3, the suffix depth in bank 4, and
its power of two in bank 5. -/

namespace CurrentAdditive.SmallBias.YaoSuffixPower

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding MatrixStage4ScalarPreparationOps

def powerEmbed : MatrixUnaryPower.Stack ↪ Fin 16 :=
  ⟨fun k => match k with
    | .inl 0 => 5
    | .inl 1 => 7
    | .inl 2 => 8
    | .inr 0 => 4,
    by decide⟩

def program := BitMachineRawSequence.program YaoSuffixCut.program
  (unaryPowerProgram powerEmbed) (.inr false : MatrixUnaryPower.Label)
  ((false, true) : MatrixUnaryCut.Control)
  (((false, false), none) : MatrixUnaryPower.Control)

theorem run (S : Fin 16 → List Bool) (a i : ℕ) (hi : i ≤ a)
    (h4 : S 4 = List.replicate a true)
    (h3 : S 3 = List.replicate i true)
    (h5 : S 5 = []) (h7 : S 7 = []) (h8 : S 8 = []) :
    ∃ u ≤ (3 * i + 4) + (4 * 2 ^ (a - i) + 5 * (a - i) + 7) + 1,
      ((advance program)^[u])
        (⟨some (BitMachineRawSequence.leftLabel MatrixUnaryCut.Label.scan),
          ((false, true), ((false, false), none)), S⟩ :
          TM2.Cfg (fun _ : Fin 16 => Bool) _ _) =
      ⟨none, ((false, true), ((false, false), none)),
        Function.update
          (Function.update S 4 (List.replicate (a - i) true))
          5 (List.replicate (2 ^ (a - i)) true)⟩ := by
  let S1 := Function.update S (4 : Fin 16) (List.replicate (a - i) true)
  obtain ⟨u1, hu1, hr1⟩ := YaoSuffixCut.run S a i hi h4 h3 h7 h8
  have hpow4 : S1 (powerEmbed (.inr ())) = List.replicate (a - i) true := by
    simp [S1, powerEmbed]
  have hpow5 : S1 (powerEmbed (.inl 0)) = [] := by
    simp [S1, powerEmbed, h5]
  have hpow7 : S1 (powerEmbed (.inl 1)) = [] := by
    simp [S1, powerEmbed, h7]
  have hpow8 : S1 (powerEmbed (.inl 2)) = [] := by
    simp [S1, powerEmbed, h8]
  obtain ⟨u2, hu2, hr2⟩ := unary_power_run powerEmbed S1 (a - i)
    hpow4 hpow5 hpow7 hpow8
  have hfinal : Function.update S1 (powerEmbed (.inl 0))
      (List.replicate (2 ^ (a - i)) true) =
      Function.update S1 5 (List.replicate (2 ^ (a - i)) true) := by
    simp [powerEmbed]
  rw [hfinal] at hr2
  obtain ⟨u, hu, hr⟩ := BitMachineRawSequence.runs
    YaoSuffixCut.program (unaryPowerProgram powerEmbed)
    MatrixUnaryCut.Label.scan (.inr false : MatrixUnaryPower.Label)
    ((false, true) : MatrixUnaryCut.Control) (true, false)
    (((false, false), none) : MatrixUnaryPower.Control)
    (((false, false), none) : MatrixUnaryPower.Control)
    S S1 _ u1 u2 hr1 hr2
  exact ⟨u, by omega, by simpa [program, S1] using hr⟩

#print axioms run

end CurrentAdditive.SmallBias.YaoSuffixPower
