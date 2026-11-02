import CurrentAdditive.CodeDPairCallbackRun

/-! Relocate the unchanged callback computation into the twelve banks it uses,
so the scheduler's source, index, and fuel banks can carry arbitrary words. -/

namespace CurrentAdditive.CodeDPairCallbackForeign

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDPairCallbackProgram
open CurrentAdditive.CodeDPairCallbackRun
open CurrentAdditive.CodeDSourceCodecV2
open CurrentAdditive.CodeDCanonicalSourceV2
open Turing BitMachineEncoding

abbrev Stack := Fin 15
abbrev Used := { j : Stack // j ≠ 8 ∧ j ≠ 10 ∧ j ≠ 13 }

def locate : Used ↪ Stack where
  toFun := Subtype.val
  inj' := Subtype.val_injective

def project (j : Stack) : Used :=
  if h : j ≠ 8 ∧ j ≠ 10 ∧ j ≠ 13 then ⟨j, h⟩
  else ⟨0, by decide⟩

theorem locate_project (j : Stack)
    (h : j ≠ 8 ∧ j ≠ 10 ∧ j ≠ 13) :
    locate (project j) = j := by simp [project, h, locate]

def smallStmt {L V : Type} :
    TM2.Stmt (fun _ : Stack => Bool) L V →
      TM2.Stmt (fun _ : Used => Bool) L V
  | .push j f q => .push (project j) f (smallStmt q)
  | .peek j f q => .peek (project j) f (smallStmt q)
  | .pop j f q => .pop (project j) f (smallStmt q)
  | .load f q => .load f (smallStmt q)
  | .branch f q r => .branch f (smallStmt q) (smallStmt r)
  | .goto f => .goto f
  | .halt => .halt

def usesOnly {L V : Type} :
    TM2.Stmt (fun _ : Stack => Bool) L V → Prop
  | .push j _ q =>
      (j ≠ 8 ∧ j ≠ 10 ∧ j ≠ 13) ∧ usesOnly q
  | .peek j _ q =>
      (j ≠ 8 ∧ j ≠ 10 ∧ j ≠ 13) ∧ usesOnly q
  | .pop j _ q =>
      (j ≠ 8 ∧ j ≠ 10 ∧ j ≠ 13) ∧ usesOnly q
  | .load _ q => usesOnly q
  | .branch _ q r => usesOnly q ∧ usesOnly r
  | .goto _ => True
  | .halt => True

instance usesOnlyDecidable {L V : Type} :
    (q : TM2.Stmt (fun _ : Stack => Bool) L V) →
      Decidable (usesOnly q)
  | .push j _ q => by
      letI := usesOnlyDecidable q
      simpa only [usesOnly] using
        (inferInstance : Decidable ((j ≠ 8 ∧ j ≠ 10 ∧ j ≠ 13) ∧ usesOnly q))
  | .peek j _ q => by
      letI := usesOnlyDecidable q
      simpa only [usesOnly] using
        (inferInstance : Decidable ((j ≠ 8 ∧ j ≠ 10 ∧ j ≠ 13) ∧ usesOnly q))
  | .pop j _ q => by
      letI := usesOnlyDecidable q
      simpa only [usesOnly] using
        (inferInstance : Decidable ((j ≠ 8 ∧ j ≠ 10 ∧ j ≠ 13) ∧ usesOnly q))
  | .load _ q => by
      simpa only [usesOnly] using usesOnlyDecidable q
  | .branch _ q r => by
      letI := usesOnlyDecidable q
      letI := usesOnlyDecidable r
      simpa only [usesOnly] using
        (inferInstance : Decidable (usesOnly q ∧ usesOnly r))
  | .goto _ => isTrue trivial
  | .halt => isTrue trivial

theorem stmt_recover {L V : Type}
    (q : TM2.Stmt (fun _ : Stack => Bool) L V)
    (h : usesOnly q) :
    BitMachineStackEmbedding.stackStmt locate (smallStmt q) = q := by
  induction q with
  | push j f q ih =>
      obtain ⟨hj, hq⟩ := h
      simp only [smallStmt, BitMachineStackEmbedding.stackStmt,
        locate_project j hj, ih hq]
  | peek j f q ih =>
      obtain ⟨hj, hq⟩ := h
      simp only [smallStmt, BitMachineStackEmbedding.stackStmt,
        locate_project j hj, ih hq]
  | pop j f q ih =>
      obtain ⟨hj, hq⟩ := h
      simp only [smallStmt, BitMachineStackEmbedding.stackStmt,
        locate_project j hj, ih hq]
  | load f q ih =>
      simp only [smallStmt, BitMachineStackEmbedding.stackStmt, ih h]
  | branch f q r ihq ihr =>
      exact congrArg₂ (TM2.Stmt.branch f) (ihq h.1) (ihr h.2)
  | goto f => rfl
  | halt => rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem program_usesOnly :
    ∀ l : CodeDPairCallbackProgram.Label,
      usesOnly (CodeDPairCallbackProgram.program l) := by
  intro l
  fin_cases l <;> decide

def smallProgram (l : CodeDPairCallbackProgram.Label) :
    TM2.Stmt (fun _ : Used => Bool)
      CodeDPairCallbackProgram.Label CodeDPairCallbackProgram.Control :=
  smallStmt (CodeDPairCallbackProgram.program l)

theorem program_recover (l : CodeDPairCallbackProgram.Label) :
    BitMachineStackEmbedding.stackStmt locate (smallProgram l) =
      CodeDPairCallbackProgram.program l :=
  stmt_recover _ (program_usesOnly l)

theorem advance_frame (foreign : Stack → List Bool)
    (c : TM2.Cfg (fun _ : Used => Bool)
      CodeDPairCallbackProgram.Label CodeDPairCallbackProgram.Control) :
    advance CodeDPairCallbackProgram.program
      (BitMachineStackEmbedding.stackCfg locate foreign c) =
    BitMachineStackEmbedding.stackCfg locate foreign
      (advance smallProgram c) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => rfl
  | some l =>
      change TM2.stepAux (CodeDPairCallbackProgram.program l) v
          (BitMachineStackEmbedding.bank locate foreign S) =
        BitMachineStackEmbedding.stackCfg locate foreign
          (TM2.stepAux (smallProgram l) v S)
      rw [← program_recover l]
      exact BitMachineStackEmbedding.stack_stepAux locate foreign
        (smallProgram l) v S

theorem run_frame (foreign : Stack → List Bool)
    (c : TM2.Cfg (fun _ : Used => Bool)
      CodeDPairCallbackProgram.Label CodeDPairCallbackProgram.Control)
    (t : Nat) :
    ((advance CodeDPairCallbackProgram.program)^[t])
      (BitMachineStackEmbedding.stackCfg locate foreign c) =
    BitMachineStackEmbedding.stackCfg locate foreign
      (((advance smallProgram)^[t]) c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, advance_frame,
        Function.iterate_succ_apply']

theorem stackCfg_injective (foreign : Stack → List Bool) :
    Function.Injective
      (BitMachineStackEmbedding.stackCfg locate foreign :
        TM2.Cfg (fun _ : Used => Bool)
          CodeDPairCallbackProgram.Label CodeDPairCallbackProgram.Control →
        TM2.Cfg (fun _ : Stack => Bool)
          CodeDPairCallbackProgram.Label CodeDPairCallbackProgram.Control) := by
  intro c d h
  rcases c with ⟨lc, vc, Sc⟩
  rcases d with ⟨ld, vd, Sd⟩
  have hl : lc = ld := congrArg TM2.Cfg.l h
  have hv : vc = vd := congrArg TM2.Cfg.var h
  have hs : Sc = Sd := by
    funext j
    have hj := congrFun (congrArg TM2.Cfg.stk h) (locate j)
    simpa only [BitMachineStackEmbedding.stackCfg,
      BitMachineStackEmbedding.bank_at] using hj
  cases hl
  cases hv
  cases hs
  rfl

theorem transport_run
    (foreign₀ foreign₁ : Stack → List Bool)
    (c d : TM2.Cfg (fun _ : Used => Bool)
      CodeDPairCallbackProgram.Label CodeDPairCallbackProgram.Control)
    (t : Nat)
    (h : CodeDPairCallbackProgram.run t
      (BitMachineStackEmbedding.stackCfg locate foreign₀ c) =
      BitMachineStackEmbedding.stackCfg locate foreign₀ d) :
    CodeDPairCallbackProgram.run t
      (BitMachineStackEmbedding.stackCfg locate foreign₁ c) =
      BitMachineStackEmbedding.stackCfg locate foreign₁ d := by
  have hsmall : ((advance smallProgram)^[t]) c = d := by
    apply stackCfg_injective foreign₀
    exact (run_frame foreign₀ c t).symm.trans h
  exact (run_frame foreign₁ c t).trans (congrArg _ hsmall)

noncomputable def initialWithForeign (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (foreign : Stack → List Bool) :
    CodeDPairCallbackProgram.Config :=
  ⟨some (.copy (.inl .scan)), none,
    BitMachineStackEmbedding.bank locate foreign
      (fun j => CodeDPairCallbackRun.initialBank x y output (locate j))⟩

theorem initialWithForeign_self (x : Entry)
    (y : Nat × ℚ) (output : List Bool) :
    initialWithForeign x y output
      (CodeDPairCallbackRun.initialBank x y output) =
      CodeDPairCallbackRun.initial x y output := by
  simp only [initialWithForeign, CodeDPairCallbackRun.initial]
  congr 1
  exact BitMachineStackEmbedding.bank_restrict locate
    (CodeDPairCallbackRun.initialBank x y output)

theorem one_pair_foreign (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (foreign : Stack → List Bool) :
    ∃ t ≤ CodeDPairCallbackRun.fixedBudget x y output,
      ∃ S : Stack → List Bool,
        CodeDPairCallbackProgram.run t
          (initialWithForeign x y output foreign) =
          ⟨none, none, S⟩ ∧
        S 9 = output ++ EncodedCommunication.field
          (CodeDPairProductTargetV2.pairBytes x.weight
          (rawOfRat y.2)) ∧
        S 12 = encodeEntry x ∧
        S 8 = foreign 8 ∧ S 10 = foreign 10 ∧
        S 13 = foreign 13 := by
  obtain ⟨T', t, ht, hr⟩ := CodeDPairCallbackRun.one_pair_run_fixed x y output
  let c₀ : TM2.Cfg (fun _ : Used => Bool)
      CodeDPairCallbackProgram.Label CodeDPairCallbackProgram.Control :=
    ⟨some (.copy (.inl .scan)), none,
      fun j => CodeDPairCallbackRun.initialBank x y output (locate j)⟩
  let d := ((advance smallProgram)^[t]) c₀
  have hstart₀ : BitMachineStackEmbedding.stackCfg locate
      (CodeDPairCallbackRun.initialBank x y output) c₀ =
      CodeDPairCallbackRun.initial x y output := by
    exact initialWithForeign_self x y output
  have hbase : BitMachineStackEmbedding.stackCfg locate
      (CodeDPairCallbackRun.initialBank x y output) d =
      ⟨none, none,
        CodeDPairCallbackRun.afterAppend x y output
          (CodeDPairCallbackRun.clearedPairBank x y) T'⟩ := by
    rw [← run_frame (CodeDPairCallbackRun.initialBank x y output) c₀ t,
      hstart₀]
    exact hr
  have hl : d.l = none := congrArg TM2.Cfg.l hbase
  have hv : d.var = none := congrArg TM2.Cfg.var hbase
  have h9 : d.stk ⟨9, by decide⟩ =
      output ++ EncodedCommunication.field
        (CodeDPairProductTargetV2.pairBytes x.weight
          (rawOfRat y.2)) := by
    have h := congrFun (congrArg TM2.Cfg.stk hbase) 9
    change BitMachineStackEmbedding.bank locate
      (CodeDPairCallbackRun.initialBank x y output) d.stk
        (locate ⟨9, by decide⟩) = _ at h
    rw [BitMachineStackEmbedding.bank_at] at h
    exact h.trans (CodeDPairCallbackRun.afterAppend_at9 x y output
      (CodeDPairCallbackRun.clearedPairBank x y) T')
  have h12 : d.stk ⟨12, by decide⟩ = encodeEntry x := by
    have h := congrFun (congrArg TM2.Cfg.stk hbase) 12
    change BitMachineStackEmbedding.bank locate
      (CodeDPairCallbackRun.initialBank x y output) d.stk
        (locate ⟨12, by decide⟩) = _ at h
    rw [BitMachineStackEmbedding.bank_at] at h
    exact h.trans (CodeDPairCallbackRun.afterAppend_at12 x y output
      (CodeDPairCallbackRun.clearedPairBank x y) T')
  let S := BitMachineStackEmbedding.bank locate foreign d.stk
  refine ⟨t, ht, S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change CodeDPairCallbackProgram.run t
      (BitMachineStackEmbedding.stackCfg locate foreign c₀) =
      ⟨none, none, S⟩
    change ((advance CodeDPairCallbackProgram.program)^[t])
      (BitMachineStackEmbedding.stackCfg locate foreign c₀) =
      ⟨none, none, S⟩
    rw [run_frame foreign c₀ t]
    simp [S, d, BitMachineStackEmbedding.stackCfg, hl, hv]
  · change BitMachineStackEmbedding.bank locate foreign d.stk
      (locate ⟨9, by decide⟩) = _
    rw [BitMachineStackEmbedding.bank_at]
    exact h9
  · change BitMachineStackEmbedding.bank locate foreign d.stk
      (locate ⟨12, by decide⟩) = _
    rw [BitMachineStackEmbedding.bank_at]
    exact h12
  · apply BitMachineStackEmbedding.bank_outside
    rintro ⟨j, hj⟩
    exact j.property.1 hj
  · apply BitMachineStackEmbedding.bank_outside
    rintro ⟨j, hj⟩
    exact j.property.2.1 hj
  · apply BitMachineStackEmbedding.bank_outside
    rintro ⟨j, hj⟩
    exact j.property.2.2 hj

#print axioms one_pair_foreign

end CurrentAdditive.CodeDPairCallbackForeign
