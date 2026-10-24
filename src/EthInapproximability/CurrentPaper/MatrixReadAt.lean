import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.MatrixTemplateMachine
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Nondestructive indexed reads for the matrix controller

Two actual copy subroutines retain the source array and its unary index.
The lookup subroutine consumes only the copies. All workspace is cleared,
and the answer is prepended to the output accumulator. The original array,
index, and old output are arbitrary literal Boolean stacks, not oracles.
-/

namespace EthInapproximability.CurrentPaper.MatrixReadAt

open Turing BitMachineEncoding BitMachineComposition BitMachineSubroutineRenaming

abbrev Label := BitMachineCopy.Label ⊕ (BitMachineCopy.Label ⊕ MatrixTemplateMachine.Label)
abbrev Control := Option Bool × (Option Bool × MatrixTemplateMachine.Control)
abbrev Config := TM2.Cfg (fun _ : Fin 7 => Bool) Label Control

def indexBank : Fin 3 ⊕ Fin 4 ≃ Fin 7 := finSumFinEquiv
def sourceBank : Fin 3 ⊕ Fin 4 ≃ Fin 7 :=
  indexBank.trans ((Equiv.swap 0 3).trans (Equiv.swap 1 4))

def copyLabelSwap : Label ≃ Label where
  toFun := Sum.elim (fun l => .inr (.inl l))
    (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  invFun := Sum.elim (fun l => .inr (.inl l))
    (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def copyControlSwap : Control ≃ Control where
  toFun s := (s.2.1, s.1, s.2.2)
  invFun s := (s.2.1, s.1, s.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

private def lookupPerm : Fin 7 ≃ Fin 7 where
  toFun i := ![1, 2, 6, 4, 5, 0, 3] i
  invFun i := ![5, 0, 1, 6, 3, 4, 2] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def lookupBank : MatrixTemplateMachine.Stack ⊕ Fin 2 ≃ Fin 7 :=
  ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 2))).trans finSumFinEquiv).trans lookupPerm

def lookupLabels : MatrixTemplateMachine.Label ⊕ (BitMachineCopy.Label ⊕ BitMachineCopy.Label) ≃ Label where
  toFun := Sum.elim (fun l => .inr (.inr l)) (Sum.elim Sum.inl (fun l => .inr (.inl l)))
  invFun := Sum.elim (fun l => .inr (.inl l))
    (Sum.elim (fun l => .inr (.inr l)) Sum.inl)
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def lookupControls : (MatrixTemplateMachine.Control × (Option Bool × Option Bool)) ≃ Control where
  toFun s := (s.2.1, s.2.2, s.1)
  invFun s := (s.2.2, s.1, s.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def program : Label → TM2.Stmt (fun _ : Fin 7 => Bool) Label Control
  | .inl l => renameStmt indexBank (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl BitMachineCopy.Label.scan)) (BitMachineCopy.program l))
  | .inr (.inl l) => renameStmt sourceBank copyLabelSwap copyControlSwap
      (liftStmt (some (.inr (.inr MatrixTemplateMachine.LookupLabel.skip))) (BitMachineCopy.program l))
  | .inr (.inr l) => renameStmt lookupBank lookupLabels lookupControls
      (liftStmt none (MatrixTemplateMachine.program l))

def cfg (l : Option Label) (s : Control) (index indexWork source sourceWork out : List Bool) : Config :=
  ⟨l, s, ![index, indexWork, [], source, sourceWork, out, []]⟩

def initial (index source out : List Bool) : Config :=
  cfg (some (.inl .scan)) (none, none, (false, false), (false, false)) index [] source [] out

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem index_input (index source out : List Bool) :
    renameCfg indexBank (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some (.inl BitMachineCopy.Label.scan))
        (none, (false, false), (false, false)) (![source, [], out, []] : Fin 4 → List Bool)
        (BitMachineCopy.cfg (some .scan) none index [] [])) = initial index source out := by
  apply congrArg (fun S => (⟨some (.inl .scan), (none, none, (false, false), (false, false)), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem index_output (index source out : List Bool) :
    renameCfg indexBank (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some (.inl BitMachineCopy.Label.scan))
        (none, (false, false), (false, false)) (![source, [], out, []] : Fin 4 → List Bool)
        (BitMachineCopy.cfg none none index index [])) =
      cfg (some (.inr (.inl .scan))) (none, none, (false, false), (false, false))
        index index source [] out := by
  apply congrArg (fun S => (⟨some (.inr (.inl .scan)), (none, none, (false, false), (false, false)), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem source_input (index source out : List Bool) :
    renameCfg sourceBank copyLabelSwap copyControlSwap
      (liftCfg (some (.inr (.inr MatrixTemplateMachine.LookupLabel.skip)))
        (none, (false, false), (false, false)) (![index, index, out, []] : Fin 4 → List Bool)
        (BitMachineCopy.cfg (some .scan) none source [] [])) =
      cfg (some (.inr (.inl .scan))) (none, none, (false, false), (false, false))
        index index source [] out := by
  apply congrArg (fun S => (⟨some (.inr (.inl .scan)), (none, none, (false, false), (false, false)), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem source_output (index source out : List Bool) :
    renameCfg sourceBank copyLabelSwap copyControlSwap
      (liftCfg (some (.inr (.inr MatrixTemplateMachine.LookupLabel.skip)))
        (none, (false, false), (false, false)) (![index, index, out, []] : Fin 4 → List Bool)
        (BitMachineCopy.cfg none none source source [])) =
      cfg (some (.inr (.inr (.inr .skip)))) (none, none, (false, false), (false, false))
        index index source source out := by
  apply congrArg (fun S => (⟨some (.inr (.inr (.inr .skip))), (none, none, (false, false), (false, false)), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem lookup_input (index source out : List Bool) :
    renameCfg lookupBank lookupLabels lookupControls
      (liftCfg none (none, none) (![index, source] : Fin 2 → List Bool)
        (MatrixTemplateMachine.cfg (some (.inr .skip)) ((false, false), (false, false)) index source out)) =
      cfg (some (.inr (.inr (.inr .skip)))) (none, none, (false, false), (false, false))
        index index source source out := by
  apply congrArg (fun S => (⟨some (.inr (.inr (.inr .skip))), (none, none, (false, false), (false, false)), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem lookup_output (index source out : List Bool) :
    renameCfg lookupBank lookupLabels lookupControls
      (liftCfg none (none, none) (![index, source] : Fin 2 → List Bool)
        (MatrixTemplateMachine.cfg none ((false, false), (false, false)) [] [] out)) =
      cfg none (none, none, (false, false), (false, false)) index [] source [] out := by
  apply congrArg (fun S => (⟨none, (none, none, (false, false), (false, false)), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

/-- Read the literal indexed source bit, preserving both input registers
and clearing every work register. The original output suffix is retained. -/
theorem readAt_run (i : ℕ) (source out : List Bool) :
    ∃ t ≤ 3 * i + 3 * source.length + 8,
      run t (initial (List.replicate i true) source out) =
        cfg none (none, none, (false, false), (false, false))
          (List.replicate i true) [] source [] (source[i]?.getD false :: out) := by
  let idx := List.replicate i true
  have hi := BitMachineCopy.run_correct none idx []
  simp only [BitMachineCopy.run, List.append_nil] at hi
  have hihalt : (((advance BitMachineCopy.program)^[2 * idx.length + 2])
      (BitMachineCopy.cfg (some .scan) none idx [] [])).l = none := by rw [hi]; rfl
  obtain ⟨ki, hki, hri⟩ := lift_outputs_renamed indexBank (Equiv.refl _) (Equiv.refl _)
    BitMachineCopy.program program (some (.inl BitMachineCopy.Label.scan)) (fun _ => rfl)
    (none, (false, false), (false, false)) (![source, [], out, []] : Fin 4 → List Bool)
    (BitMachineCopy.cfg (some .scan) none idx [] []) (2 * idx.length + 2) hihalt
  rw [hi, index_input, index_output] at hri
  have hs := BitMachineCopy.run_correct none source []
  simp only [BitMachineCopy.run, List.append_nil] at hs
  have hshalt : (((advance BitMachineCopy.program)^[2 * source.length + 2])
      (BitMachineCopy.cfg (some .scan) none source [] [])).l = none := by rw [hs]; rfl
  obtain ⟨ks, hks, hrs⟩ := lift_outputs_renamed sourceBank copyLabelSwap copyControlSwap
    BitMachineCopy.program program (some (.inr (.inr MatrixTemplateMachine.LookupLabel.skip)))
    (fun _ => rfl) (none, (false, false), (false, false)) (![idx, idx, out, []] : Fin 4 → List Bool)
    (BitMachineCopy.cfg (some .scan) none source [] []) (2 * source.length + 2) hshalt
  rw [hs, source_input, source_output] at hrs
  have hl := MatrixTemplateMachine.lookup_correct i ((false, false), (false, false)) source out
  simp only [MatrixTemplateMachine.run] at hl
  have hlhalt : (((advance MatrixTemplateMachine.program)^[i + 4 + (source.drop i).tail.length])
      (MatrixTemplateMachine.cfg (some (.inr .skip)) ((false, false), (false, false)) idx source out)).l = none := by
    rw [hl]
    rfl
  obtain ⟨kl, hkl, hrl⟩ := lift_outputs_renamed lookupBank lookupLabels lookupControls
    MatrixTemplateMachine.program program none (fun _ => rfl) (none, none)
    (![idx, source] : Fin 2 → List Bool)
    (MatrixTemplateMachine.cfg (some (.inr .skip)) ((false, false), (false, false)) idx source out)
    (i + 4 + (source.drop i).tail.length) hlhalt
  rw [hl, lookup_input, lookup_output] at hrl
  refine ⟨ki + ks + kl, ?_, ?_⟩
  · have hlen : (source.drop i).tail.length ≤ source.length := by
      simp only [List.length_tail, List.length_drop]
      omega
    simp only [idx, List.length_replicate] at hki
    omega
  · exact (run_add ((run_add hri ks).trans hrs) kl).trans hrl

end EthInapproximability.CurrentPaper.MatrixReadAt
