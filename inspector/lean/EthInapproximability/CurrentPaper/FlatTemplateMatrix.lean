import EthInapproximability.CurrentPaper.MatrixWordGather
import EthInapproximability.CurrentPaper.MatrixTemplatePayload

/-!
# Template entries from the two flat sampled arrays

Source: locked v8 `eq:exact-H-template`, `eq:exact-duplicate-labels`, and
Appendix B `thm:paper-materialization`. This physical controller gathers the
first-family prefix, gathers the second-family binary label, duplicates the
two required coordinates, and performs the indexed read. Its only preloaded
unbounded query data are unary addresses and word lengths, not sampled words,
decoded labels, or answers. Address computation and selector decoding remain
separate controllers.
-/

namespace EthInapproximability.CurrentPaper.FlatTemplateMatrix

open Turing BitMachineEncoding BitMachineComposition BitMachineSubroutine
open BitMachineSubroutineRenaming

abbrev FLabel := MatrixWordGather.Forward.Label
abbrev FControl := MatrixWordGather.Forward.Control
abbrev PLabel := MatrixTemplatePayload.Label
abbrev PControl := MatrixTemplatePayload.Control
abbrev Label := FLabel ⊕ (FLabel ⊕ PLabel)
abbrev Control := FControl × (FControl × PControl)
abbrev Config := TM2.Cfg (fun _ : Fin 14 => Bool) Label Control

def baseF : FControl := (MatrixWordGather.baseControl, none)
def baseP : PControl := ((false, false, none), (false, false), (false, false))

def firstBank : MatrixWordGather.Forward.Stack ⊕ Fin 5 ≃ Fin 14 :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 5))).trans finSumFinEquiv

private def secondPerm : Fin 14 ≃ Fin 14 where
  toFun i := ![9, 1, 2, 10, 4, 5, 6, 11, 12, 0, 3, 7, 8, 13] i
  invFun i := ![9, 1, 2, 10, 4, 5, 6, 11, 12, 0, 3, 7, 8, 13] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def secondBank : MatrixWordGather.Forward.Stack ⊕ Fin 5 ≃ Fin 14 :=
  firstBank.trans secondPerm

def swapLabels : Label ≃ Label where
  toFun := Sum.elim (fun l => .inr (.inl l)) (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  invFun := Sum.elim (fun l => .inr (.inl l)) (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def swapControls : Control ≃ Control where
  toFun s := (s.2.1, s.1, s.2.2)
  invFun s := (s.2.1, s.1, s.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

private def payloadPerm : Fin 14 ≃ Fin 14 where
  toFun i := ![8, 1, 12, 13, 2, 4, 0, 3, 5, 6, 7, 9, 10, 11] i
  invFun i := ![6, 1, 4, 7, 5, 8, 9, 10, 0, 11, 12, 13, 2, 3] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def payloadBank : Fin 6 ⊕ Fin 8 ≃ Fin 14 := finSumFinEquiv.trans payloadPerm

def payloadLabels : PLabel ⊕ (FLabel ⊕ FLabel) ≃ Label where
  toFun := Sum.elim (fun l => .inr (.inr l)) (Sum.elim Sum.inl (fun l => .inr (.inl l)))
  invFun := Sum.elim (fun l => .inr (.inl l)) (Sum.elim (fun l => .inr (.inr l)) Sum.inl)
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def payloadControls : PControl × (FControl × FControl) ≃ Control where
  toFun s := (s.2.1, s.2.2, s.1)
  invFun s := (s.2.2, s.1, s.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def program : Label → TM2.Stmt (fun _ : Fin 14 => Bool) Label Control
  | .inl l => renameStmt firstBank (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl (.inr MatrixWordGather.Forward.Admin.test)))
        (MatrixWordGather.Forward.program l))
  | .inr (.inl l) => renameStmt secondBank swapLabels swapControls
      (liftStmt (some (.inr (.inl MatrixDuplicateRow.Label.first)))
        (MatrixWordGather.Forward.program l))
  | .inr (.inr l) => renameStmt payloadBank payloadLabels payloadControls
      (liftStmt none (MatrixTemplatePayload.program l))

def cfg (l : Option Label)
    (addr₁ source₁ prefWord count₁ addr₂ source₂ bits count₂ out : List Bool) : Config :=
  ⟨l, (baseF, baseF, baseP),
    ![addr₁, [], [], source₁, [], [], [], count₁, prefWord, addr₂, source₂, count₂, bits, out]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem first_cfg (l : Option FLabel)
    (addr₁ source₁ prefWord count₁ addr₂ source₂ bits count₂ out : List Bool) :
    renameCfg firstBank (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some (.inl (.inr MatrixWordGather.Forward.Admin.test))) (baseF, baseP)
        (![addr₂, source₂, count₂, bits, out] : Fin 5 → List Bool)
        (MatrixWordGather.Forward.cfg l none addr₁ source₁ [] count₁ prefWord)) =
      cfg (l.elim (some (.inr (.inl (.inr .test)))) (fun l => some (.inl l)))
        addr₁ source₁ prefWord count₁ addr₂ source₂ bits count₂ out := by
  cases l <;> apply congrArg (fun S => (⟨_, (baseF, baseF, baseP), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem second_cfg (l : Option FLabel)
    (addr₁ source₁ prefWord count₁ addr₂ source₂ bits count₂ out : List Bool) :
    renameCfg secondBank swapLabels swapControls
      (liftCfg (some (.inr (.inl MatrixDuplicateRow.Label.first))) (baseF, baseP)
        (![addr₁, source₁, count₁, prefWord, out] : Fin 5 → List Bool)
        (MatrixWordGather.Forward.cfg l none addr₂ source₂ [] count₂ bits)) =
      cfg (l.elim (some (.inr (.inr (.inl .first)))) (fun l => some (.inr (.inl l))))
        addr₁ source₁ prefWord count₁ addr₂ source₂ bits count₂ out := by
  cases l <;> apply congrArg (fun S => (⟨_, (baseF, baseF, baseP), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem payload_cfg (l : Option PLabel)
    (addr₁ source₁ prefWord count₁ addr₂ source₂ bits count₂ out : List Bool) :
    renameCfg payloadBank payloadLabels payloadControls
      (liftCfg none (baseF, baseF)
        (![addr₁, source₁, [], [], count₁, addr₂, source₂, count₂] : Fin 8 → List Bool)
        (MatrixTemplatePayload.cfg l prefWord bits out)) =
      cfg (l.map fun l => .inr (.inr l))
        addr₁ source₁ prefWord count₁ addr₂ source₂ bits count₂ out := by
  cases l <;> apply congrArg (fun S => (⟨_, (baseF, baseF, baseP), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

def readBound (width start size : ℕ) : ℕ := width * (3 * (start + width) + 3 * size + 11) + 2

/-- All three phases execute in one finite controller. The source arrays are
preserved and the sampled-word work registers are empty upon termination. -/
theorem template_run {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (p : Fin 4) (z : Fin N₂) (c : ExactConstruction.Columns d N₁) (out : List Bool) :
    let q := ExactConstruction.prefixLength a
    let s₁ := (c.2 p).2.val * (q + 3)
    let s₂ := (z.val * d + (c.2 p).1.val) * a
    let data := MatrixMaterialization.storeBits C₁ C₂ v
    ∃ t ≤ readBound q s₁ data.first.length + readBound a s₂ data.second.length +
        (8 * 2 ^ a + 3 * a + 10),
      run t (cfg (some (.inl (.inr .test)))
        (List.replicate s₁ true) data.first [] (List.replicate q true)
        (List.replicate s₂ true) data.second [] (List.replicate a true) out) =
        cfg none (List.replicate (s₁ + q) true) data.first [] []
          (List.replicate (s₂ + a) true) data.second [] []
          (ExactConstruction.matrix ha C₁ C₂ v cap (.inl (p, z)) c :: out) := by
  dsimp only
  let q := ExactConstruction.prefixLength a
  let s₁ := (c.2 p).2.val * (q + 3)
  let s₂ := (z.val * d + (c.2 p).1.val) * a
  let data := MatrixMaterialization.storeBits C₁ C₂ v
  let prefWord := MatrixDuplicateRow.prefixWord C₁ (c.2 p).2
  let bits := List.ofFn ((MatrixMaterialization.wordCode a).symm (C₂ z (c.2 p).1))
  obtain ⟨k₁, hk₁, hr₁⟩ := MatrixWordGather.Forward.stored_prefix_run C₁ C₂ v (c.2 p).2 []
  simp only [List.append_nil] at hr₁
  have hh₁ : (((advance MatrixWordGather.Forward.program)^[k₁])
      (MatrixWordGather.Forward.cfg (some (.inr .test)) none (List.replicate s₁ true)
        data.first [] (List.replicate q true) [])).l = none := by
    change (MatrixWordGather.Forward.run k₁ _).l = none
    rw [hr₁]
    rfl
  obtain ⟨t₁, ht₁, hrun₁⟩ := lift_outputs_renamed firstBank (Equiv.refl _) (Equiv.refl _)
    MatrixWordGather.Forward.program program
    (some (.inl (.inr MatrixWordGather.Forward.Admin.test)))
    (fun _ => rfl) (baseF, baseP)
    (![List.replicate s₂ true, data.second, List.replicate a true, [], out] : Fin 5 → List Bool)
    (MatrixWordGather.Forward.cfg (some (.inr .test)) none (List.replicate s₁ true)
      data.first [] (List.replicate q true) []) k₁ hh₁
  change (((advance MatrixWordGather.Forward.program)^[k₁]) _) = _ at hr₁
  rw [hr₁, first_cfg, first_cfg] at hrun₁
  obtain ⟨k₂, hk₂, hr₂⟩ := MatrixWordGather.Forward.stored_word_run C₁ C₂ v z (c.2 p).1 []
  simp only [List.append_nil] at hr₂
  have hh₂ : (((advance MatrixWordGather.Forward.program)^[k₂])
      (MatrixWordGather.Forward.cfg (some (.inr .test)) none (List.replicate s₂ true)
        data.second [] (List.replicate a true) [])).l = none := by
    change (MatrixWordGather.Forward.run k₂ _).l = none
    rw [hr₂]
    rfl
  obtain ⟨t₂, ht₂, hrun₂⟩ := lift_outputs_renamed secondBank swapLabels swapControls
    MatrixWordGather.Forward.program program (some (.inr (.inl MatrixDuplicateRow.Label.first)))
    (fun _ => rfl) (baseF, baseP)
    (![List.replicate (s₁ + q) true, data.first, [], prefWord, out] : Fin 5 → List Bool)
    (MatrixWordGather.Forward.cfg (some (.inr .test)) none (List.replicate s₂ true)
      data.second [] (List.replicate a true) []) k₂ hh₂
  change (((advance MatrixWordGather.Forward.program)^[k₂]) _) = _ at hr₂
  rw [hr₂, second_cfg, second_cfg] at hrun₂
  obtain ⟨kp, hkp, hrp⟩ := MatrixTemplatePayload.template_run ha C₁ C₂ v cap p z c out
  have hhp : (((advance MatrixTemplatePayload.program)^[kp])
      (MatrixTemplatePayload.cfg (some (.inl .first)) prefWord bits out)).l = none := by
    change (MatrixTemplatePayload.run kp _).l = none
    rw [hrp]
    rfl
  obtain ⟨tp, htp, hrunp⟩ := lift_outputs_renamed payloadBank payloadLabels payloadControls
    MatrixTemplatePayload.program program none (fun _ => rfl) (baseF, baseF)
    (![List.replicate (s₁ + q) true, data.first, [], [], [], List.replicate (s₂ + a) true,
      data.second, []] : Fin 8 → List Bool)
    (MatrixTemplatePayload.cfg (some (.inl .first)) prefWord bits out) kp hhp
  change (((advance MatrixTemplatePayload.program)^[kp]) _) = _ at hrp
  rw [hrp, payload_cfg, payload_cfg] at hrunp
  refine ⟨t₁ + t₂ + tp, ?_, ?_⟩
  · change t₁ + t₂ + tp ≤ readBound q s₁ data.first.length +
      readBound a s₂ data.second.length + (8 * 2 ^ a + 3 * a + 10)
    exact Nat.add_le_add (Nat.add_le_add (ht₁.trans hk₁) (ht₂.trans hk₂)) (htp.trans hkp)
  · exact (run_add ((run_add hrun₁ t₂).trans hrun₂) tp).trans hrunp

end EthInapproximability.CurrentPaper.FlatTemplateMatrix
