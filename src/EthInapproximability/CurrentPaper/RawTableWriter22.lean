import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

/-! Final physical transfer of the generated raw table word to writer cell 22.
This operation accepts only the word reached by an upstream table writer;
it does not compute or assume its semantic identity. -/

namespace EthInapproximability.CurrentPaper.RawTableWriter22

open Turing BitMachineEncoding MatrixStage4ScalarPreparationOps

abbrev Stack := Fin 64 ⊕ Fin 3

def slots : Fin 3 ↪ Stack :=
  ⟨![Sum.inr 0, Sum.inl 22, Sum.inr 1], by decide⟩

def program := copyProgram slots

def initialBank (W : Fin 64 → List Bool) (word : List Bool) :
    Stack → List Bool :=
  Sum.elim W (![word, [], []] : Fin 3 → List Bool)

def finalBank (W : Fin 64 → List Bool) (word : List Bool) :
    Stack → List Bool :=
  Sum.elim (Function.update W 22 word)
    (![word, [], []] : Fin 3 → List Bool)

theorem run (W : Fin 64 → List Bool) (word : List Bool)
    (hblank : W 22 = []) :
    ((advance program)^[2 * word.length + 2])
      (⟨some .scan, none, initialBank W word⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, finalBank W word⟩ := by
  have hs : (initialBank W word) (slots 2) = [] := rfl
  have hr := copy_run slots (initialBank W word) hs
  change ((advance program)^[2 * word.length + 2])
      (⟨some .scan, none, initialBank W word⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, Function.update (initialBank W word) (Sum.inl 22)
        (word ++ W 22)⟩ at hr
  rw [hblank, List.append_nil] at hr
  convert hr using 1
  congr 1
  funext k
  cases k with
  | inl j =>
      by_cases hj : j = 22
      · subst j
        simp [finalBank, initialBank]
      · simp [finalBank, initialBank, hj]
  | inr j =>
      fin_cases j <;> simp [finalBank, initialBank]

theorem writer22 (W : Fin 64 → List Bool) (word : List Bool) :
    finalBank W word (.inl 22) = word := by
  simp [finalBank]

theorem preserve_writer (W : Fin 64 → List Bool) (word : List Bool)
    (k : Fin 64) (hk : k ≠ 22) :
    finalBank W word (.inl k) = W k := by
  simp [finalBank, hk]

theorem preserve_source (W : Fin 64 → List Bool) (word : List Bool) :
    finalBank W word (.inr 0) = word := by
  rfl

#print axioms run
#print axioms preserve_writer

end EthInapproximability.CurrentPaper.RawTableWriter22
