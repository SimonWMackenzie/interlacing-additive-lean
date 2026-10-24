import CurrentAdditive.IndexedRationalProgramBridge

/-! The indexed program has exactly the input law prescribed by positive
integer masses, and therefore by rational laws after denominator clearing. -/

namespace Paper2.IndexedRationalLawBridge

open scoped BigOperators
open Paper2.RecursiveSamplingProgram Paper2.RecursiveSamplingLaws
open Paper2.RecursiveLabelCodecScratch
open Paper2.IndexedRationalProgramBridge Paper2.IndexedRationalFinCode

def decodeIndex {n : ℕ} (hn : 0 < n) (bits : List Bool) : Fin n :=
  match (finCodec n).decode bits with
  | some (i, _) => i
  | none => ⟨0, hn⟩

theorem decodeIndex_encode {n : ℕ} (hn : 0 < n) (i : Fin n) :
    decodeIndex hn ((finCodec n).encode i) = i := by
  have h := (finCodec n).roundtrip i []
  simp only [List.append_nil] at h
  simp [decodeIndex, h]

theorem program_expect {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (f : Fin n → ℝ) :
    Program.expect (program hn (indices n w)) f =
      (∑ i, (w i : ℝ) * f i) / (∑ i, w i) := by
  have hcode := code_exact hn w hw
  have h := congrArg
    (fun p : Program (List Bool) =>
      Program.expect p (fun bits => f (decodeIndex hn bits))) hcode
  change Program.expect (GeneratorCode.meaning (code n w))
      (fun bits => f (decodeIndex hn bits)) =
    Program.expect (Program.map (finCodec n).encode (program hn (indices n w)))
      (fun bits => f (decodeIndex hn bits)) at h
  rw [code_expect hn w hw, Program.expect_map] at h
  simpa only [decodeIndex_encode] using h.symm

/-- Any positive integer weight table defines an exact rational law on
positions. Duplicate decoded labels remain different positions. -/
noncomputable def law {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) :
    PositiveRationalLaw (Fin n) where
  weight i := (w i : ℚ) / (∑ j, w j)
  positive i := by
    have ht : 0 < ∑ j, w j := by
      exact Finset.sum_pos (fun j _ => hw j)
        ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    exact div_pos (by exact_mod_cast hw i) (by exact_mod_cast ht)
  total := by
    have ht : ((∑ j, w j) : ℚ) ≠ 0 := by
      have hp : 0 < ∑ j, w j := by
        exact Finset.sum_pos (fun j _ => hw j)
          ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      exact_mod_cast hp.ne'
    calc
      (∑ i, (w i : ℚ) / (∑ j, w j)) =
          (∑ i, (w i : ℚ)) / (∑ j, w j) := by rw [Finset.sum_div]
      _ = 1 := by simpa only [Nat.cast_sum] using (div_self ht)

theorem program_generates {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) :
    Generates (program hn (indices n w))
      (law hn w hw).toFiniteLaw := by
  intro f
  rw [program_expect hn w hw]
  simp only [PositiveRationalLaw.toFiniteLaw, law]
  simp only [Rat.cast_div, Rat.cast_natCast]
  rw [Finset.sum_div]
  congr 1
  funext i
  ring

#print axioms program_expect
#print axioms program_generates

end Paper2.IndexedRationalLawBridge
