import CurrentAdditive.YaoCutPhysical
import EthInapproximability.CurrentPaper.MatrixUnaryCut
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Physically subtract the cut index from the pair depth, preserving the
cut word and all other ambient Fin16 banks. -/

namespace CurrentAdditive.SmallBias.YaoSuffixCut

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding

def embed : Fin 4 ↪ Fin 16 :=
  ⟨![4, 3, 7, 8], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all⟩

def program := fun l => stackStmt embed (MatrixUnaryCut.program l)

theorem run (S : Fin 16 → List Bool) (a i : ℕ) (hi : i ≤ a)
    (h4 : S 4 = List.replicate a true)
    (h3 : S 3 = List.replicate i true)
    (h7 : S 7 = []) (h8 : S 8 = []) :
    ∃ u ≤ 3 * i + 4,
      ((advance program)^[u])
        (⟨some .scan, (false, true), S⟩ : TM2.Cfg (fun _ : Fin 16 => Bool)
          MatrixUnaryCut.Label MatrixUnaryCut.Control) =
      ⟨none, (true, false),
        Function.update S 4 (List.replicate (a - i) true)⟩ := by
  let c := MatrixUnaryCut.cfg (some .scan) (false, true)
    (List.replicate a true) (List.replicate i true) [] []
  have hstart : stackCfg embed S c =
      (⟨some .scan, (false, true), S⟩ : TM2.Cfg (fun _ : Fin 16 => Bool)
        MatrixUnaryCut.Label MatrixUnaryCut.Control) := by
    dsimp [stackCfg, c, MatrixUnaryCut.cfg]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [embed, h4, h3, h7, h8]
  obtain ⟨u, hu, hr⟩ := MatrixUnaryCut.cut_run a i
  have he := BitMachineStackRun.run embed S MatrixUnaryCut.program c u
  rw [hstart] at he
  change _ = stackCfg embed S (MatrixUnaryCut.run u c) at he
  rw [show c = MatrixUnaryCut.cfg (some .scan) (false, true)
      (List.replicate a true) (List.replicate i true) [] [] from rfl,
    hr] at he
  have hfin : stackCfg embed S
      (MatrixUnaryCut.cfg none (decide (i ≤ a), false)
        (List.replicate (if a < i then a else a - i) true)
        (List.replicate i true) [] []) =
      (⟨none, (true, false),
        Function.update S 4 (List.replicate (a - i) true)⟩ :
        TM2.Cfg (fun _ : Fin 16 => Bool)
          MatrixUnaryCut.Label MatrixUnaryCut.Control) := by
    simp only [hi, if_neg (by omega : ¬ a < i)]
    dsimp [stackCfg, MatrixUnaryCut.cfg]
    congr 1
    have hloc : (![List.replicate (a - i) true, List.replicate i true,
        ([] : List Bool), []] : Fin 4 → List Bool) =
        Function.update (fun k : Fin 4 => S (embed k)) 0
          (List.replicate (a - i) true) := by
      funext k
      fin_cases k <;> simp [embed, h3, h7, h8]
    rw [hloc, bank_update, bank_restrict]
    simp [embed]
  exact ⟨u, by simpa [Nat.min_eq_right hi] using hu, he.trans hfin⟩

#print axioms run

end CurrentAdditive.SmallBias.YaoSuffixCut
