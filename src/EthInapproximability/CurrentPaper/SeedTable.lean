import EthInapproximability.CurrentPaper.SeedLoop
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
# The level-0 matrix word: the charged producer (generic cells)

Lane owner:b-stage4-entry-program-6 (Paper B, unit 2, map item 3).

ONE fixed program `program W C T O` on an arbitrary bank, four distinct cells:
(1) the admitted charged copy `copyProgram ![W, C, T]` (unary `w` from `W` onto the
blank counter `C`, `W` restored, `T` blank again), i.e. `C = bitsLE w (2^w - 1)`;
(2) the counting loop `SeedLoop.program C T O`. One charged handoff
(`BitMachineRawSequence.runs`). Exit bank EXACT: `O` gets `rows w (2^w - 1)`, every
other cell (including `W`, `C`, `T`) equal to the start bank (`seed_table_run`).
The row identity with the actual level-0 matrix is in `P6SeedSpec`.
-/

namespace EthInapproximability.CurrentPaper.SeedTable

open Turing BitMachineEncoding SeedLoop

variable {K : Type*} [DecidableEq K]

theorem bitsLE_all_ones (w : ℕ) : bitsLE w (2 ^ w - 1) = List.replicate w true := by
  induction w with
  | zero => rfl
  | succ w ih =>
      have h1 : (2 ^ (w + 1) - 1) % 2 = 1 := by
        have : 1 ≤ 2 ^ w := Nat.one_le_two_pow
        rw [pow_succ]; omega
      have h2 : (2 ^ (w + 1) - 1) / 2 = 2 ^ w - 1 := by
        have : 1 ≤ 2 ^ w := Nat.one_le_two_pow
        rw [pow_succ]; omega
      simp [bitsLE, h1, h2, ih, List.replicate_succ]

/-- The copy slots: source `W`, destination `C`, temporary `T`. -/
def slots (W C T : K) (h : Function.Injective ![W, C, T]) : Fin 3 ↪ K := ⟨![W, C, T], h⟩

/-- ONE fixed program: charged copy, then the counting loop. -/
def program (W C T O : K) (h : Function.Injective ![W, C, T]) :=
  BitMachineRawSequence.program (MatrixStage4ScalarPreparationOps.copyProgram (slots W C T h))
    (SeedLoop.program C T O) Lab.emit (none : Option Bool) (none : Option Bool)

def startLabel : BitMachineRawSequence.Label BitMachineCopy.Label Lab :=
  BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan

def bound (w : ℕ) : ℕ := (2 * w + 2) + (2 ^ w - 1 + 1) * (4 * w + 4) + 1

theorem seed_table_run (W C T O : K) (h : Function.Injective ![W, C, T])
    (hCO : C ≠ O) (hTO : T ≠ O) (S : K → List Bool) (w : ℕ)
    (hW : S W = List.replicate w true) (hC : S C = []) (hT : S T = []) (hO : S O = []) :
    ∃ t ≤ bound w,
      ((advance (program W C T O h))^[t])
          (⟨some startLabel, ((none : Option Bool), (none : Option Bool)), S⟩ :
            TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, ((none : Option Bool), (none : Option Bool)),
          Function.update S O (rows w (2 ^ w - 1))⟩ := by
  have hCT : C ≠ T := fun e => by
    have := h (show ![W, C, T] 1 = ![W, C, T] 2 from e); exact absurd this (by decide)
  have hc := MatrixStage4ScalarPreparationOps.copy_run (slots W C T h) S hT
  change ((advance (MatrixStage4ScalarPreparationOps.copyProgram (slots W C T h)))^[2 * (S W).length + 2])
      ⟨some .scan, none, S⟩ = ⟨none, none, Function.update S C (S W ++ S C)⟩ at hc
  rw [hW, hC, List.append_nil, List.length_replicate] at hc
  have hmid : Function.update S C (List.replicate w true) =
      upd3 C T O S (bitsLE w (2 ^ w - 1)) [] [] := by
    rw [bitsLE_all_ones]
    funext k
    simp only [upd3, Function.update_apply]
    by_cases h1 : k = O
    · subst h1; simp [hO, Ne.symm hCO]
    · by_cases h2 : k = T
      · subst h2; simp [hT, Ne.symm hCT, h1]
      · simp [h1, h2]
  have hend : upd3 C T O S [] [] (rows w (2 ^ w - 1) ++ []) =
      Function.update S O (rows w (2 ^ w - 1)) := by
    funext k
    simp only [upd3, Function.update_apply, List.append_nil]
    by_cases h1 : k = O
    · simp [h1]
    · by_cases h2 : k = T
      · subst h2; simp [hT, h1]
      · by_cases h3 : k = C
        · subst h3; simp [hC, h1, h2]
        · simp [h1, h2, h3]
  obtain ⟨tl, htl, hl⟩ := loop_run hCT hCO hTO w (2 ^ w - 1) (by
    have : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    omega) S none []
  rw [← hmid, hend] at hl
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.copyProgram (slots W C T h)) (SeedLoop.program C T O)
    BitMachineCopy.Label.scan Lab.emit none none none none S
    (Function.update S C (List.replicate w true)) (Function.update S O (rows w (2 ^ w - 1)))
    (2 * w + 2) tl hc hl
  exact ⟨t, by unfold bound; omega, hr⟩

#print axioms SeedLoop.loop_run
#print axioms bitsLE_all_ones
#print axioms seed_table_run

end EthInapproximability.CurrentPaper.SeedTable
