import CurrentAdditive.GenericBitvectorRowAddress
import CurrentAdditive.GenericWordLengthCopy

/-! Place the literal Boolean-word length copier on the column label cell
and an empty unary-index cell, preserving the original encoded column. -/

namespace Paper2.GenericBitvectorColumnLength

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

def ι : Fin 3 ↪ Fin 14 := ⟨![5, 8, 9], by decide⟩
def program := fun l => stackStmt ι (GenericWordLengthCopy.program l)

theorem length_run (S : Fin 14 → List Bool) (q : List Bool)
    (h5 : S 5 = q) (h8 : S 8 = []) (h9 : S 9 = []) :
    ((advance program)^[2 * q.length + 2])
      (⟨some .scan, (none : Option Bool), S⟩ :
        TM2.Cfg (fun _ : Fin 14 => Bool) _ _) =
      ⟨none, (none : Option Bool),
        Function.update S 8 (List.replicate q.length true)⟩ := by
  let B := (![q, [], []] : Fin 3 → List Bool)
  have hB : ∀ k, B k = S (ι k) := by
    intro k
    fin_cases k <;> simp [B, ι, h5, h8, h9]
  have hb := GenericWordLengthCopy.length_copy q
  unfold GenericWordLengthCopy.run at hb
  have hs := BitMachineStackRun.run ι S GenericWordLengthCopy.program
    (GenericWordLengthCopy.cfg (some .scan) none q [] []) (2 * q.length + 2)
  rw [hb] at hs
  have hstart : stackCfg ι S (GenericWordLengthCopy.cfg (some .scan) none q [] []) =
      (⟨some .scan, (none : Option Bool), S⟩ : TM2.Cfg (fun _ : Fin 14 => Bool) _ _) := by
    simp only [stackCfg, GenericWordLengthCopy.cfg]
    congr 1
    exact bank_eq_self ι S B hB
  rw [hstart] at hs
  have hend : stackCfg ι S
      (GenericWordLengthCopy.cfg none none q (List.replicate q.length true) []) =
      (⟨none, (none : Option Bool), Function.update S 8
        (List.replicate q.length true)⟩ : TM2.Cfg (fun _ : Fin 14 => Bool) _ _) := by
    simp only [stackCfg, GenericWordLengthCopy.cfg]
    congr 1
    have hloc : (![q, List.replicate q.length true, []] : Fin 3 → List Bool) =
        Function.update B 1 (List.replicate q.length true) := by
      funext k
      fin_cases k <;> simp [B]
    rw [hloc, bank_update, bank_eq_self ι S B hB]
    rfl
  simpa only [program, hend] using hs

#print axioms length_run

end Paper2.GenericBitvectorColumnLength
