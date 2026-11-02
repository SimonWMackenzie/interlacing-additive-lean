import CurrentAdditive.YaoThresholdAffine

/-! Physically construct the cut threshold from the graph prelude's unary
`H = 2^b`, preserving H and every unrelated bank. -/

namespace CurrentAdditive.SmallBias.YaoThreshold

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding
open MatrixStage4ScalarPreparationOps
open YaoThresholdAffine

def copyEmbed : Fin 3 ↪ Fin 16 :=
  ⟨![1, 8, 7], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all⟩

def affineEmbed : Fin 3 ↪ Fin 16 :=
  ⟨![8, 9, 6], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all⟩

def coefficient (t : ℕ) : Nat × Nat := (2 ^ (t - 3) - 1, 0)

theorem coefficient_value (t : ℕ) :
    SourceAffineUnary.vertexCoefficient (coefficient t) = 2 ^ (t - 3) := by
  unfold SourceAffineUnary.vertexCoefficient coefficient
  have hp : 0 < 2 ^ (t - 3) := pow_pos (by decide : 0 < (2 : ℕ)) _
  omega

def program (t : ℕ) :=
  BitMachineRawSequence.program (copyProgram copyEmbed)
    (affineProgram (coefficient t) affineEmbed)
    SourceAffineUnary.Label.vertexScan none none

def affineTime (t H : ℕ) : ℕ :=
  ((SourceAffineUnary.vertexCoefficient (coefficient t) + 1) * H + 1) +
  ((SourceAffineUnary.rowCoefficient (coefficient t) + 1) * 0 + 1)

theorem threshold_value (b t : ℕ) (ht : 3 ≤ t) :
    2 ^ (t - 3) * 2 ^ b = 2 ^ (t + b - 3) := by
  have he : t + b - 3 = (t - 3) + b := by omega
  rw [he, pow_add]

theorem run (S : Fin 16 → List Bool) (b t : ℕ)
    (ht : 3 ≤ t)
    (hH : S 1 = List.replicate (2 ^ b) true)
    (h6 : S 6 = []) (h7 : S 7 = [])
    (h8 : S 8 = []) (h9 : S 9 = []) :
    ∃ u ≤ (2 * 2 ^ b + 2) + affineTime t (2 ^ b) + 1,
      ((advance (program t))^[u])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, none), S⟩ : TM2.Cfg (fun _ : Fin 16 => Bool) _ _) =
      ⟨none, (none, none),
        Function.update S 6 (List.replicate (2 ^ (t + b - 3)) true)⟩ := by
  let S1 := Function.update S (8 : Fin 16) (List.replicate (2 ^ b) true)
  have hcopy : ((advance (copyProgram copyEmbed))^[2 * 2 ^ b + 2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : Fin 16 => Bool)
        BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, S1⟩ := by
    have hr := copy_run copyEmbed S h7
    simpa [copyEmbed, S1, hH, h8] using hr
  have h8' : S1 (affineEmbed 0) = List.replicate (2 ^ b) true := by
    simp [S1, affineEmbed]
  have h9' : S1 (affineEmbed 1) = [] := by
    simp [S1, affineEmbed, h9]
  have h6' : S1 (affineEmbed 2) = [] := by
    simp [S1, affineEmbed, h6]
  have haffine := affine_run (coefficient t) affineEmbed S1 (2 ^ b) h8' h9' h6'
  have hfinal : Function.update (Function.update S1 (affineEmbed 0) [])
      (affineEmbed 2)
        (List.replicate (SourceAffineUnary.vertexCoefficient (coefficient t) * 2 ^ b) true) =
      Function.update S 6 (List.replicate (2 ^ (t + b - 3)) true) := by
    rw [coefficient_value, threshold_value b t ht]
    funext z
    fin_cases z <;> simp [S1, affineEmbed, h8]
  rw [hfinal] at haffine
  obtain ⟨u, hu, hr⟩ := BitMachineRawSequence.runs
    (copyProgram copyEmbed) (affineProgram (coefficient t) affineEmbed)
    BitMachineCopy.Label.scan SourceAffineUnary.Label.vertexScan
    none none none none S S1 _ (2 * 2 ^ b + 2)
    (affineTime t (2 ^ b)) hcopy haffine
  exact ⟨u, by simpa [affineTime] using hu, hr⟩

#print axioms run

end CurrentAdditive.SmallBias.YaoThreshold
