import CurrentAdditive.GenericBitvectorColumnLength
import EthInapproximability.CurrentPaper.MatrixTableLookup

/-! A literal row-major lookup on a seed-shaped carrier. The input row
label has already been converted to unary in cell 1; cell 8 contains the
length of the encoded column word, hence a padded column address. -/

namespace Paper2.GenericBitvectorPaddedLookup

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

def ι : MatrixTableLookup.Stack ↪ Fin 14 :=
  ⟨![1, 6, 8, 10, 12, 13, 7, 11, 4, 3], by decide⟩

def program := fun l => stackStmt ι (MatrixTableLookup.program l)

theorem lookup_run (S : Fin 14 → List Bool) (row width col : ℕ)
    (bits : List Bool)
    (h1 : S 1 = List.replicate row true)
    (h6 : S 6 = List.replicate width true)
    (h8 : S 8 = List.replicate col true)
    (h7 : S 7 = bits)
    (h11 : S 11 = [])
    (h10 : S 10 = []) (h12 : S 12 = []) (h13 : S 13 = [])
    (h4 : S 4 = []) (h3 : S 3 = []) :
    ∃ t ≤ 32 * (row + width + col + bits.length + 1) ^ 2,
      ((advance program)^[t])
        (⟨some MatrixTableLookup.start, MatrixTableLookup.initial, S⟩ :
          TM2.Cfg (fun _ : Fin 14 => Bool) _ _) =
      ⟨none, MatrixTableLookup.initial,
        Function.update S 11 [bits[row * width + col]?.getD false]⟩ := by
  let B := MatrixTableLookup.cfg (some MatrixTableLookup.start)
    MatrixTableLookup.initial (List.replicate row true)
    (List.replicate width true) (List.replicate col true) [] bits []
  have hB : ∀ k, B.stk k = S (ι k) := by
    intro k
    fin_cases k <;>
      simp [B, MatrixTableLookup.cfg, ι, h1, h6, h8, h7, h11,
        h10, h12, h13, h4, h3]
  obtain ⟨t, ht, hr⟩ := MatrixTableLookup.lookup_run row width col bits []
  have hs := BitMachineStackRun.run ι S MatrixTableLookup.program B t
  change ((advance MatrixTableLookup.program)^[t]) B = _ at hr
  rw [hr] at hs
  have hstart : stackCfg ι S B =
      (⟨some MatrixTableLookup.start, MatrixTableLookup.initial, S⟩ :
        TM2.Cfg (fun _ : Fin 14 => Bool) _ _) := by
    simp only [stackCfg, B]
    congr 1
    exact bank_eq_self ι S _ hB
  rw [hstart] at hs
  have hend : stackCfg ι S
      (MatrixTableLookup.cfg none MatrixTableLookup.initial
        (List.replicate row true) (List.replicate width true)
        (List.replicate col true) [] bits
        [bits[row * width + col]?.getD false]) =
      (⟨none, MatrixTableLookup.initial,
        Function.update S 11 [bits[row * width + col]?.getD false]⟩ :
          TM2.Cfg (fun _ : Fin 14 => Bool) _ _) := by
    simp only [stackCfg]
    congr 1
    have hloc : (MatrixTableLookup.cfg none MatrixTableLookup.initial
        (List.replicate row true) (List.replicate width true)
        (List.replicate col true) [] bits
        [bits[row * width + col]?.getD false]).stk =
        Function.update B.stk 7
          [bits[row * width + col]?.getD false] := by
      funext k
      fin_cases k <;> simp [B, MatrixTableLookup.cfg]
    rw [hloc, bank_update, bank_eq_self ι S B.stk hB]
    rfl
  exact ⟨t, ht, by simpa only [program, hend] using hs⟩

#print axioms lookup_run

end Paper2.GenericBitvectorPaddedLookup
