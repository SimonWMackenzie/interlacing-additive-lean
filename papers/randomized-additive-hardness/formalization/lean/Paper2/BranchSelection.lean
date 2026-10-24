import Paper2.ChildSelect

/-! Actual unary choice composed with the physical three-child transport. -/

namespace Paper2.BranchSelection

open Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

abbrev Stack := ChildSelect.Stack ⊕ Fin 5

inductive Label where
  | unary (l : UnaryChoice.Label)
  | handoff
  | child (c : UnaryChoice.Choice) (l : ChildSelect.Label)
  deriving DecidableEq, Fintype

abbrev Control := UnaryChoice.Control × ChildSelect.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def contents (code : ChildSelect.Stack → List Bool)
    (unary : Fin 5 → List Bool) : Stack → List Bool := Sum.elim code unary

def unaryEmbedding : Fin 5 ↪ Stack :=
  ⟨Sum.inr, by intro i j h; exact Sum.inr.inj h⟩
def childEmbedding : ChildSelect.Stack ↪ Stack :=
  ⟨Sum.inl, by intro i j h; exact Sum.inl.inj h⟩

def unaryProgram (l : UnaryChoice.Label) :=
  stackStmt unaryEmbedding (UnaryChoice.program l)
def childProgram (l : ChildSelect.Label) :=
  stackStmt childEmbedding (ChildSelect.program l)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .unary l =>
      BitMachineInline.stmt Label.unary
        (fun v => (v, ChildSelect.idle .first)) Prod.fst
        (some .handoff) (unaryProgram l)
  | .handoff =>
      .load (fun v => (v.1, ChildSelect.idle v.1.1))
        (.goto (fun v => .child v.1.1 .dispatch))
  | .child c l =>
      BitMachineInline.stmt (.child c)
        (fun v => ((c, none), v)) Prod.snd none (childProgram l)

def inputWord (f s t : Code) (rest : List Bool) : List Bool :=
  encodeCode f ++ encodeCode s ++ encodeCode t ++ rest

def selectedCode (c : UnaryChoice.Choice) (f s t : Code) : Code :=
  match c with
  | .first => f
  | .second => s
  | .third => t

def initial (i a b : Nat) (f s t : Code) (rest : List Bool) : Config :=
  ⟨some (.unary .copyScan), ((.first, none), ChildSelect.idle .first),
    contents (CodeExtract.contents (inputWord f s t rest) [] [] [])
      (UnaryChoice.contents (List.replicate i true)
        (List.replicate a true) (List.replicate b true) [] [])⟩

def output (choice : UnaryChoice.Choice) (selected rest : List Bool) : Config :=
  ⟨none, ((choice, none), ChildSelect.idle choice),
    contents (CodeExtract.contents selected rest [] [])
      (UnaryChoice.contents [] [] [] [] [])⟩

private theorem unary_bank (X : ChildSelect.Stack → List Bool)
    (U V : Fin 5 → List Bool) :
    bank unaryEmbedding (contents X U) V = contents X V := by
  funext k
  rcases k with k | k
  · rw [bank_outside]
    · rfl
    · intro ⟨j, hj⟩; cases hj
  · change bank unaryEmbedding _ _ (unaryEmbedding k) = _
    rw [bank_at]
    rfl

private theorem child_bank (X Y : ChildSelect.Stack → List Bool)
    (U : Fin 5 → List Bool) :
    bank childEmbedding (contents X U) Y = contents Y U := by
  funext k
  rcases k with k | k
  · change bank childEmbedding _ _ (childEmbedding k) = _
    rw [bank_at]
    rfl
  · rw [bank_outside]
    · rfl
    · intro ⟨j, hj⟩; cases hj

theorem unary_stage (i a b : Nat) (word : List Bool) :
    ∃ tu ≤ 20 * (i + a + b + 1),
      ((advance unaryProgram)^[tu])
        (⟨some .copyScan, (.first, none),
          contents (CodeExtract.contents word [] [] [])
            (UnaryChoice.contents (List.replicate i true)
              (List.replicate a true) (List.replicate b true) [] [])⟩ :
          TM2.Cfg (fun _ : Stack => Bool) UnaryChoice.Label UnaryChoice.Control) =
        ⟨none, (UnaryChoice.choiceOf i a b, none),
          contents (CodeExtract.contents word [] [] [])
            (UnaryChoice.contents [] [] [] [] [])⟩ := by
  obtain ⟨tu, htu, hr⟩ := UnaryChoice.choose i a b
  have hs := BitMachineStackRun.run unaryEmbedding
    (contents (CodeExtract.contents word [] [] [])
      (UnaryChoice.contents [] [] [] [] []))
    UnaryChoice.program (UnaryChoice.initial i a b) tu
  rw [hr] at hs
  simp only [stackCfg, UnaryChoice.initial, UnaryChoice.output,
    UnaryChoice.cfg, unary_bank] at hs
  exact ⟨tu, htu, hs⟩

theorem child_stage (c : UnaryChoice.Choice)
    (f s t : Code) (rest : List Bool) :
    ∃ tc ≤ 25 * (inputWord f s t rest).length + 30,
      ((advance childProgram)^[tc])
        (⟨some .dispatch, ChildSelect.idle c,
          contents (CodeExtract.contents (inputWord f s t rest) [] [] [])
            (UnaryChoice.contents [] [] [] [] [])⟩ :
          TM2.Cfg (fun _ : Stack => Bool) ChildSelect.Label ChildSelect.Control) =
        ⟨none, ChildSelect.idle c,
          contents (CodeExtract.contents
            (encodeCode (selectedCode c f s t)) rest [] [])
            (UnaryChoice.contents [] [] [] [] [])⟩ := by
  obtain ⟨tc, htc, hr⟩ := ChildSelect.select_choice c f s t rest
  have hr' : ((advance ChildSelect.program)^[tc])
      (ChildSelect.initial c (inputWord f s t rest)) =
      ChildSelect.output c
        (encodeCode (selectedCode c f s t)) rest := by
    cases c <;> simpa [inputWord, selectedCode] using hr
  have hs := BitMachineStackRun.run childEmbedding
    (contents (CodeExtract.contents (inputWord f s t rest) [] [] [])
      (UnaryChoice.contents [] [] [] [] []))
    ChildSelect.program
    (ChildSelect.initial c (inputWord f s t rest)) tc
  rw [hr'] at hs
  simp only [stackCfg, ChildSelect.initial, ChildSelect.output,
    child_bank] at hs
  exact ⟨tc, by simpa only [inputWord] using htc, hs⟩

theorem unary_inlined (i a b : Nat) (f s t : Code) (rest : List Bool) :
    ∃ tu ≤ 20 * (i + a + b + 1),
      ((advance program)^[tu]) (initial i a b f s t rest) =
        ⟨some .handoff,
          ((UnaryChoice.choiceOf i a b, none), ChildSelect.idle .first),
          contents (CodeExtract.contents (inputWord f s t rest) [] [] [])
            (UnaryChoice.contents [] [] [] [] [])⟩ := by
  obtain ⟨tu, htu, hr⟩ := unary_stage i a b (inputWord f s t rest)
  have hhalt : (((advance unaryProgram)^[tu])
      (⟨some .copyScan, (.first, none),
        contents (CodeExtract.contents (inputWord f s t rest) [] [] [])
          (UnaryChoice.contents (List.replicate i true)
            (List.replicate a true) (List.replicate b true) [] [])⟩ :
        TM2.Cfg (fun _ : Stack => Bool) UnaryChoice.Label UnaryChoice.Control)).l = none := by
    rw [hr]
  obtain ⟨u, hu, he⟩ := BitMachineInline.outputs Label.unary
    (fun v : UnaryChoice.Control => (v, ChildSelect.idle .first)) Prod.fst
    (by intro v; rfl) (some .handoff) unaryProgram program
    (by intro l; rfl)
    (⟨some .copyScan, (.first, none),
      contents (CodeExtract.contents (inputWord f s t rest) [] [] [])
        (UnaryChoice.contents (List.replicate i true)
          (List.replicate a true) (List.replicate b true) [] [])⟩ :
      TM2.Cfg (fun _ : Stack => Bool) UnaryChoice.Label UnaryChoice.Control)
    tu hhalt
  rw [hr] at he
  exact ⟨u, by omega, he⟩

theorem handoff_step (c : UnaryChoice.Choice)
    (word : List Bool) :
    advance program
      (⟨some .handoff, ((c, none), ChildSelect.idle .first),
        contents (CodeExtract.contents word [] [] [])
          (UnaryChoice.contents [] [] [] [] [])⟩ : Config) =
      ⟨some (.child c .dispatch), ((c, none), ChildSelect.idle c),
        contents (CodeExtract.contents word [] [] [])
          (UnaryChoice.contents [] [] [] [] [])⟩ := rfl

theorem child_inlined (c : UnaryChoice.Choice)
    (f s t : Code) (rest : List Bool) :
    ∃ tc ≤ 25 * (inputWord f s t rest).length + 30,
      ((advance program)^[tc])
        (⟨some (.child c .dispatch), ((c, none), ChildSelect.idle c),
          contents (CodeExtract.contents (inputWord f s t rest) [] [] [])
            (UnaryChoice.contents [] [] [] [] [])⟩ : Config) =
        output c (encodeCode (selectedCode c f s t)) rest := by
  obtain ⟨tc, htc, hr⟩ := child_stage c f s t rest
  have hhalt : (((advance childProgram)^[tc])
      (⟨some .dispatch, ChildSelect.idle c,
        contents (CodeExtract.contents (inputWord f s t rest) [] [] [])
          (UnaryChoice.contents [] [] [] [] [])⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ChildSelect.Label ChildSelect.Control)).l = none := by
    rw [hr]
  obtain ⟨u, hu, he⟩ := BitMachineInline.outputs (.child c)
    (fun v : ChildSelect.Control => ((c, none), v)) Prod.snd
    (by intro v; rfl) none childProgram program
    (by intro l; rfl)
    (⟨some .dispatch, ChildSelect.idle c,
      contents (CodeExtract.contents (inputWord f s t rest) [] [] [])
        (UnaryChoice.contents [] [] [] [] [])⟩ :
      TM2.Cfg (fun _ : Stack => Bool) ChildSelect.Label ChildSelect.Control)
    tc hhalt
  rw [hr] at he
  exact ⟨u, by omega, he⟩

/-- One fixed machine decides nested unary thresholds and physically selects
exactly one of three serialized child codes, preserving any suffix. -/
theorem branch3_select (i a b : Nat) (f s t : Code) (rest : List Bool) :
    ∃ n ≤ 60 * (i + a + b + (inputWord f s t rest).length + 1),
      ((advance program)^[n]) (initial i a b f s t rest) =
        output (UnaryChoice.choiceOf i a b)
          (encodeCode (if i < a then f else if i < b then s else t)) rest := by
  let c := UnaryChoice.choiceOf i a b
  obtain ⟨tu, htu, hu⟩ := unary_inlined i a b f s t rest
  obtain ⟨tc, htc, hc⟩ := child_inlined c f s t rest
  have hh := handoff_step c (inputWord f s t rest)
  have hselected : selectedCode c f s t =
      (if i < a then f else if i < b then s else t) := by
    simp only [c, UnaryChoice.choiceOf]
    split_ifs <;> rfl
  refine ⟨tu + 1 + tc, ?_, ?_⟩
  · omega
  · have hfirst : ((advance program)^[tu + 1]) (initial i a b f s t rest) =
        ⟨some (.child c .dispatch), ((c, none), ChildSelect.idle c),
          contents (CodeExtract.contents (inputWord f s t rest) [] [] [])
            (UnaryChoice.contents [] [] [] [] [])⟩ := by
      rw [show tu + 1 = 1 + tu by omega, Function.iterate_add_apply,
        hu, Function.iterate_one]
      exact hh
    rw [show tu + 1 + tc = tc + (tu + 1) by omega,
      Function.iterate_add_apply, hfirst, hc, hselected]

#print axioms branch3_select

end Paper2.BranchSelection
