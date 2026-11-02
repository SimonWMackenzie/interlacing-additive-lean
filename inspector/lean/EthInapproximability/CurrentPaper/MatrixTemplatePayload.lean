import EthInapproximability.CurrentPaper.MatrixDuplicateRow
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# The template-row rule from two literal sampled words

Source: locked v8 `eq:exact-H-template` and `eq:exact-duplicate-labels`.
One actual controller duplicates the two original first-family coordinates,
decodes the sampled second-family binary word, and reads the requested bit.
Neither a decoded label nor the final answer is supplied to the controller.
The caller still has to gather these words from the flat sampled arrays.
-/

namespace EthInapproximability.CurrentPaper.MatrixTemplatePayload

open Turing BitMachineEncoding BitMachineComposition BitMachineSubroutine
open BitMachineSubroutineRenaming

abbrev Label := MatrixDuplicateRow.Label ⊕ MatrixTemplateMachine.Label
abbrev Control := MatrixDuplicateRow.Control × MatrixTemplateMachine.Control
abbrev Config := TM2.Cfg (fun _ : Fin 6 => Bool) Label Control

def duplicateBank : Fin 2 ⊕ Fin 4 ≃ Fin 6 := finSumFinEquiv

private def queryPerm : Fin 6 ≃ Fin 6 where
  toFun i := ![2, 4, 5, 0, 3, 1] i
  invFun i := ![3, 5, 0, 4, 1, 2] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def queryBank : MatrixTemplateMachine.Stack ⊕ Fin 1 ≃ Fin 6 :=
  ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 1))).trans finSumFinEquiv).trans queryPerm

def program : Label → TM2.Stmt (fun _ : Fin 6 => Bool) Label Control
  | .inl l => renameStmt duplicateBank (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixBinaryAddress.Label.readBit)) (MatrixDuplicateRow.program l))
  | .inr l => renameStmt queryBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftStmt none (MatrixTemplateMachine.program l))

def cfg (l : Option Label) (prefixBits bits out : List Bool) : Config :=
  ⟨l, ((false, false, none), (false, false), (false, false)),
    ![prefixBits, [], bits, out, [], []]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem duplicate_input (prefixBits bits out : List Bool) :
    renameCfg duplicateBank (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some (.inl MatrixBinaryAddress.Label.readBit)) ((false, false), (false, false))
        (![bits, out, [], []] : Fin 4 → List Bool)
        (MatrixDuplicateRow.cfg (some .first) (false, false, none) prefixBits [])) =
      cfg (some (.inl .first)) prefixBits bits out := by
  apply congrArg (fun S => (⟨some (.inl .first),
    ((false, false, none), (false, false), (false, false)), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem duplicate_output (prefixBits bits out : List Bool) :
    renameCfg duplicateBank (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some (.inl MatrixBinaryAddress.Label.readBit)) ((false, false), (false, false))
        (![bits, out, [], []] : Fin 4 → List Bool)
        (MatrixDuplicateRow.cfg none (false, false, none) prefixBits [])) =
      cfg (some (.inr (.inl .readBit))) prefixBits bits out := by
  apply congrArg (fun S => (⟨some (.inr (.inl .readBit)),
    ((false, false, none), (false, false), (false, false)), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem query_input (prefixBits bits out : List Bool) :
    renameCfg queryBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftCfg none (false, false, none) (fun _ : Fin 1 => [])
        (MatrixTemplateMachine.initial bits prefixBits out)) =
      cfg (some (.inr (.inl .readBit))) prefixBits bits out := by
  apply congrArg (fun S => (⟨some (.inr (.inl .readBit)),
    ((false, false, none), (false, false), (false, false)), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem query_output (out : List Bool) :
    renameCfg queryBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftCfg none (false, false, none) (fun _ : Fin 1 => [])
        (MatrixTemplateMachine.cfg none ((false, false), (false, false)) [] [] out)) =
      cfg none [] [] out := by
  apply congrArg (fun S => (⟨none,
    ((false, false, none), (false, false), (false, false)), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

/-- The two supplied sampled words are processed by one physical program.
The two duplicate labels, binary decoding, and lookup are all charged. -/
theorem template_run {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (p : Fin 4) (z : Fin N₂) (c : ExactConstruction.Columns d N₁) (out : List Bool) :
    ∃ t ≤ 8 * 2 ^ a + 3 * a + 10,
      run t (cfg (some (.inl .first))
        (MatrixDuplicateRow.prefixWord C₁ (c.2 p).2)
        (List.ofFn ((MatrixMaterialization.wordCode a).symm (C₂ z (c.2 p).1))) out) =
        cfg none [] [] (ExactConstruction.matrix ha C₁ C₂ v cap (.inl (p, z)) c :: out) := by
  let bits := List.ofFn ((MatrixMaterialization.wordCode a).symm (C₂ z (c.2 p).1))
  let prefixBits := MatrixDuplicateRow.prefixWord C₁ (c.2 p).2
  let row := MatrixTemplateMachine.duplicatedRow ha C₁ (c.2 p).2
  have hd := MatrixDuplicateRow.sampled_prefix_run ha C₁ (c.2 p).2
  have hdh : (((advance MatrixDuplicateRow.program)^[2 * ExactConstruction.prefixLength a + 4])
      (MatrixDuplicateRow.cfg (some .first) (false, false, none) prefixBits [])).l = none := by
    change (MatrixDuplicateRow.run _ _).l = none
    rw [hd]
    rfl
  obtain ⟨td, htd, hrunD⟩ := lift_outputs_renamed duplicateBank (Equiv.refl _) (Equiv.refl _)
    MatrixDuplicateRow.program program (some (.inl MatrixBinaryAddress.Label.readBit))
    (fun _ => rfl) ((false, false), (false, false)) (![bits, out, [], []] : Fin 4 → List Bool)
    (MatrixDuplicateRow.cfg (some .first) (false, false, none) prefixBits [])
    (2 * ExactConstruction.prefixLength a + 4) hdh
  change (((advance MatrixDuplicateRow.program)^[_]) _) = _ at hd
  rw [hd, duplicate_input, duplicate_output] at hrunD
  obtain ⟨k, hk, hr⟩ := MatrixTemplateMachine.template_matrix_run ha C₁ C₂ v cap p z c out
  have hqh : (((advance MatrixTemplateMachine.program)^[k])
      (MatrixTemplateMachine.initial bits row out)).l = none := by
    change (MatrixTemplateMachine.run k _).l = none
    rw [hr]
    rfl
  obtain ⟨tq, htq, hrunQ⟩ := lift_outputs_renamed queryBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
    MatrixTemplateMachine.program program none (fun _ => rfl) (false, false, none)
    (fun _ : Fin 1 => []) (MatrixTemplateMachine.initial bits row out) k hqh
  change (((advance MatrixTemplateMachine.program)^[k]) _) = _ at hr
  rw [hr, query_input, query_output] at hrunQ
  refine ⟨td + tq, ?_, ?_⟩
  · have hprefix := Construction.qOne_add_two a (by omega : 1 ≤ a)
    change ExactConstruction.prefixLength a + 2 = 2 ^ a at hprefix
    omega
  · exact (run_add hrunD tq).trans hrunQ

end EthInapproximability.CurrentPaper.MatrixTemplatePayload
