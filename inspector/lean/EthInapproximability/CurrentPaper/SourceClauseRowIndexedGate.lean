import EthInapproximability.CurrentPaper.SourceClauseRowSlotAddress

/-!
# Transfer the physically computed row slot to a row-derived OR gate

This is the inter-stage bridge. It does not supply an oracle clause ordinal:
the unary slot is produced by `SourceClauseRowSlotAddress` and copied into the
row gate's slot input. A later finite-control tuple iterator must provide the
unary tuple counter and the remaining literal position.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowIndexedGate

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack (q : ℕ) := SourceClauseRowSlotAddress.Stack ⊕
  (SourceClauseRowGate.Stack q ⊕ Fin 1)

def slotEmbedding {q : ℕ} : SourceClauseRowSlotAddress.Stack ↪ Stack q :=
  Function.Embedding.inl
def gateEmbedding {q : ℕ} : SourceClauseRowGate.Stack q ↪ Stack q where
  toFun x := .inr (.inl x)
  inj' := by intro x y h; exact Sum.inl.inj (Sum.inr.inj h)

def source {q : ℕ} : Stack q := .inl (.inr (.inl 5))
def temp {q : ℕ} : Stack q := .inr (.inr 0)
def gateSlot {q : ℕ} : SourceClauseRowGate.Stack q :=
  .inr (.inl (.inr (.inl (.inl 0))))
def target {q : ℕ} : Stack q := .inr (.inl gateSlot)
def targets {q : ℕ} : List (Stack q) := [target]

inductive CopyLabel where
  | scan | restore | finish
  deriving DecidableEq, Fintype

def copyProgram {q : ℕ} : CopyLabel →
    TM2.Stmt (fun _ : Stack q => Bool) CopyLabel (Unit × Option Bool)
  | .scan => BitMachineBroadcast.scanStep source temp .scan .restore
  | .restore => BitMachineBroadcast.restoreStep temp targets .restore .finish
  | .finish => .halt

noncomputable def initial {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    Stack q → List Bool :=
  Sum.elim (SourceClauseRowSlotAddress.initial n r a q k)
    (Sum.elim (SourceClauseRowGate.initial row
      (row (.inl (j, 1))).length a s n t 0 w saved output count)
      (fun _ => []))

noncomputable def slotted {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    Stack q → List Bool :=
  Sum.elim (SourceClauseRowSlotAddress.finalBank n r a q k)
    (Sum.elim (SourceClauseRowGate.initial row
      (row (.inl (j, 1))).length a s n t 0 w saved output count)
      (fun _ => []))

noncomputable def copied {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    Stack q → List Bool :=
  BitMachineBroadcast.copied source temp targets
    (List.replicate (SourceClauseRowSlotAddress.slot n r a q k) true)
    (slotted j row n r a k s t w saved output count)

def slotProgram {q : ℕ} (l : BitMachineRawSequence.Label
    (BitMachineRawSequence.Label MatrixAddressMachine.Label
      SourceClauseRowSlotAddress.CopyLabel) MatrixAddressMachine.Label) :=
  stackStmt (slotEmbedding (q := q)) (SourceClauseRowSlotAddress.program l)

theorem slot_initial {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    bank slotEmbedding (initial j row n r a k s t w saved output count)
      (SourceClauseRowSlotAddress.initial n r a q k) =
      initial j row n r a k s t w saved output count := by
  apply bank_eq_self
  intro i
  rfl

theorem slot_final {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    bank slotEmbedding (initial j row n r a k s t w saved output count)
      (SourceClauseRowSlotAddress.finalBank n r a q k) =
      slotted j row n r a k s t w saved output count := by
  funext i
  cases i with
  | inl i => exact bank_at slotEmbedding _ _ i
  | inr i =>
      rw [bank_outside]
      · rfl
      · intro ⟨u, h⟩; cases h

theorem slot_run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    ∃ ts ≤ SourceClauseRowSlotAddress.cost n r a q k,
      ((advance slotProgram)^[ts])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)),
          ((false, ((), none)), false),
          initial j row n r a k s t w saved output count⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label MatrixAddressMachine.Label
                SourceClauseRowSlotAddress.CopyLabel) MatrixAddressMachine.Label)
            ((Bool × (Unit × Option Bool)) × Bool)) =
        ⟨none, ((false, ((), none)), false),
          slotted j row n r a k s t w saved output count⟩ := by
  obtain ⟨ts, hts, hs⟩ := SourceClauseRowSlotAddress.run n r a q k
  have he := BitMachineStackRun.run slotEmbedding
    (initial j row n r a k s t w saved output count)
    SourceClauseRowSlotAddress.program
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)),
      ((false, ((), none)), false),
      SourceClauseRowSlotAddress.initial n r a q k⟩ :
      TM2.Cfg (fun _ : SourceClauseRowSlotAddress.Stack => Bool)
        (BitMachineRawSequence.Label
          (BitMachineRawSequence.Label MatrixAddressMachine.Label
            SourceClauseRowSlotAddress.CopyLabel) MatrixAddressMachine.Label)
        ((Bool × (Unit × Option Bool)) × Bool)) ts
  rw [hs] at he
  simp only [stackCfg, slot_initial, slot_final] at he
  exact ⟨ts, hts, he⟩

theorem copied_slot {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    copied j row n r a k s t w saved output count target =
      List.replicate (SourceClauseRowSlotAddress.slot n r a q k) true := by
  simp [copied, BitMachineBroadcast.copied, source, temp, target,
    targets, slotted, gateSlot, SourceClauseRowGate.initial,
    SourceClauseGateSlotAddress.initial,
    SourceClauseGateAffineAddress.initial,
    SourceLabelAddressMachine.inputs, SourceLabelAddressMachine.ambient]

theorem copy_run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    ((advance (copyProgram (q := q)))^[2 * SourceClauseRowSlotAddress.slot n r a q k + 3])
      (⟨some .scan, ((), none),
        slotted j row n r a k s t w saved output count⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) CopyLabel (Unit × Option Bool)) =
      ⟨none, ((), none), copied j row n r a k s t w saved output count⟩ := by
  have h := BitMachineBroadcast.broadcast_run copyProgram source temp
    (by simp [source, temp]) targets (by simp [targets])
    (by simp [source, targets, target])
    (by simp [temp, targets, target])
    .scan .restore .finish rfl rfl () none
    (List.replicate (SourceClauseRowSlotAddress.slot n r a q k) true)
    (slotted j row n r a k s t w saved output count)
    (SourceClauseRowSlotAddress.final_slot n r a q k) rfl
  rw [show 2 * SourceClauseRowSlotAddress.slot n r a q k + 3 =
    (2 * (List.replicate (SourceClauseRowSlotAddress.slot n r a q k) true).length + 2) + 1
    by simp, Function.iterate_succ_apply']
  change advance copyProgram
    (BitMachineBroadcast.run copyProgram
      (2 * (List.replicate (SourceClauseRowSlotAddress.slot n r a q k) true).length + 2)
      (⟨some .scan, ((), none),
        slotted j row n r a k s t w saved output count⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) CopyLabel (Unit × Option Bool))) = _
  rw [h]
  simp [advance, TM2.step, copyProgram, copied]

theorem gate_input {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (x : SourceClauseRowGate.Stack q) :
    copied j row n r a k s t w saved output count (gateEmbedding x) =
      SourceClauseRowGate.initial row
        (row (.inl (j, 1))).length a s n t
        (SourceClauseRowSlotAddress.slot n r a q k) w
        saved output count x := by
  by_cases hx : x = gateSlot
  · subst x
    simp [copied, BitMachineBroadcast.copied, source, temp,
      target, targets, gateEmbedding, slotted, gateSlot,
      SourceClauseRowGate.initial, SourceClauseGateSlotAddress.initial,
      SourceClauseGateAffineAddress.initial,
      SourceLabelAddressMachine.inputs, SourceLabelAddressMachine.ambient]
  · simp [copied, BitMachineBroadcast.copied, source, temp,
      target, targets, gateEmbedding, slotted, gateSlot,
      SourceClauseRowGate.initial, SourceClauseGateSlotAddress.initial,
      SourceClauseGateAffineAddress.initial,
      SourceLabelAddressMachine.inputs, SourceLabelAddressMachine.ambient] at *
    rcases x with x | (x | x)
    · rfl
    · rcases x with x | x
      · rfl
      · rcases x with x | x
        · rcases x with x | x
          · fin_cases x <;> simp_all
          · simp_all
        · simp_all
    · rfl

theorem gate_ready {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    bank gateEmbedding (copied j row n r a k s t w saved output count)
      (SourceClauseRowGate.initial row
        (row (.inl (j, 1))).length a s n t
        (SourceClauseRowSlotAddress.slot n r a q k) w
        saved output count) =
      copied j row n r a k s t w saved output count := by
  apply bank_eq_self
  intro x
  exact (gate_input j row n r a k s t w saved output count x).symm

noncomputable def gateProgram {q : ℕ} (j : Fin q) (sign : Bool) :=
  fun l => stackStmt (gateEmbedding (q := q))
    (SourceClauseRowGate.program j sign l)

def slotControl : (Bool × (Unit × Option Bool)) × Bool :=
  ((false, ((), none)), false)

abbrev GateControl :=
  (SourceLabelAddressMachine.Control × (Unit × Option Bool)) ×
    ((Bool × (Unit × Option Bool)) ×
      ((SourceLabelAddressMachine.Control × (Unit × Option Bool)) ×
        (((Unit × Option Bool) × Option Bool) ×
          (SourceClauseGateMachine.PrepareControl ×
            SourceClauseGateMachine.EmitControl))))

noncomputable def gateControl : GateControl :=
  (((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none)),
    ((false, ((), none)),
      (((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none)),
        ((((), none), none), SourceClauseGateMachine.control))))

noncomputable def program {q : ℕ} (j : Fin q) (sign : Bool) :=
  BitMachineRawSequence.program
    (BitMachineRawSequence.program slotProgram copyProgram CopyLabel.scan
      slotControl ((), none))
    (gateProgram j sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))
    (slotControl, ((), none)) gateControl

noncomputable def finalBank {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool) : Stack q → List Bool :=
  bank gateEmbedding (copied j row n r a k s t w saved output count)
    (SourceClauseRowGate.finalBank j row
      (row (.inl (j, 1))).length a s n t
      (SourceClauseRowSlotAddress.slot n r a q k) w sign
      saved output count)

theorem gate_run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (h : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ tg ≤ SourceClauseRowGate.cost
        (row (.inl (j, 1))).length a s n t
        (SourceClauseRowSlotAddress.slot n r a q k) w sign,
      ((advance (gateProgram j sign))^[tg])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))),
          gateControl, copied j row n r a k s t w saved output count⟩) =
        ⟨none, gateControl,
          finalBank j row n r a k s t w sign saved output count⟩ := by
  let v := (row (.inl (j, 1))).length
  obtain ⟨tg, htg, hg⟩ := SourceClauseRowGate.run j row v a s n t
    (SourceClauseRowSlotAddress.slot n r a q k) w sign
    saved output count h
  have he := BitMachineStackRun.run gateEmbedding
    (copied j row n r a k s t w saved output count)
    (SourceClauseRowGate.program j sign)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))),
      gateControl,
      SourceClauseRowGate.initial row v a s n t
        (SourceClauseRowSlotAddress.slot n r a q k) w
        saved output count⟩) tg
  dsimp only [gateControl] at he
  rw [hg] at he
  simp only [stackCfg] at he
  dsimp only [v] at he
  rw [gate_ready j row n r a k s t w saved output count] at he
  exact ⟨tg, htg, he⟩

noncomputable def cost (q n r a k v s t w : ℕ) (sign : Bool) : ℕ :=
  SourceClauseRowSlotAddress.cost n r a q k +
  (2 * SourceClauseRowSlotAddress.slot n r a q k + 3) +
  SourceClauseRowGate.cost v a s n t
    (SourceClauseRowSlotAddress.slot n r a q k) w sign + 2

theorem run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (h : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ T ≤ cost q n r a k (row (.inl (j, 1))).length s t w sign,
      ((advance (program j sign))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))),
          ((slotControl, ((), none)), gateControl),
          initial j row n r a k s t w saved output count⟩) =
        ⟨none, ((slotControl, ((), none)), gateControl),
          finalBank j row n r a k s t w sign saved output count⟩ := by
  obtain ⟨ts, hts, hs⟩ := slot_run j row n r a k s t w saved output count
  have hc := copy_run j row n r a k s t w saved output count
  obtain ⟨tsc, htsc, hsc⟩ := BitMachineRawSequence.runs
    slotProgram copyProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))
    CopyLabel.scan slotControl slotControl ((), none) ((), none)
    (initial j row n r a k s t w saved output count)
    (slotted j row n r a k s t w saved output count)
    (copied j row n r a k s t w saved output count)
    ts (2 * SourceClauseRowSlotAddress.slot n r a q k + 3) hs hc
  obtain ⟨tg, htg, hg⟩ := gate_run j row n r a k s t w sign
    saved output count h
  obtain ⟨T, hT, hrun⟩ := BitMachineRawSequence.runs
    (BitMachineRawSequence.program slotProgram copyProgram CopyLabel.scan
      slotControl ((), none))
    (gateProgram j sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))
    (slotControl, ((), none)) (slotControl, ((), none))
    gateControl gateControl
    (initial j row n r a k s t w saved output count)
    (copied j row n r a k s t w saved output count)
    (finalBank j row n r a k s t w sign saved output count)
    tsc tg hsc hg
  exact ⟨T, by dsimp [cost] at *; omega, hrun⟩

theorem final_row {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (h : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true)
    (x : SourceCSPRowQueryFrame.Stack q) :
    finalBank j row n r a k s t w sign saved output count
      (gateEmbedding (.inl (.inl x))) = row x := by
  rw [finalBank, bank_at]
  exact SourceClauseRowGate.final_row j row
    (row (.inl (j, 1))).length a s n t
    (SourceClauseRowSlotAddress.slot n r a q k) w sign
    saved output count h x

theorem final_count {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    finalBank j row n r a k s t w sign saved output count
      (gateEmbedding
        (SourceClauseRowGate.gateEmbedding
          (SourceClauseGateSlotAddress.gateEmbedding
            (SourceClauseGateAffineAddress.gateEmbedding
              (SourceClauseGateTwoAddress.embedding
                (SourceClauseGateMachine.embedding (.inr (.inr ())))))))) =
      true :: true :: true :: count := by
  simp only [finalBank, bank_at, SourceClauseRowGate.final_count]

theorem final_saved {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    let p := SourceClauseRowSlotAddress.slot n r a q k * w + (n * a + t)
    finalBank j row n r a k s t w sign saved output count
      (gateEmbedding
        (SourceClauseRowGate.gateEmbedding
          (SourceClauseGateSlotAddress.gateEmbedding
            (SourceClauseGateAffineAddress.gateEmbedding
              (SourceClauseGateTwoAddress.embedding
                (SourceClauseGateMachine.embedding (.inr (.inl 0)))))))) =
      (EncodedCNF.encodeClause
        (SourceClauseGatePrepare.thirdClause p
          ⟨(row (.inl (j, 1))).length * a + s, sign⟩)).reverse ++
      (EncodedCNF.encodeClause (SourceClauseGatePrepare.secondClause p)).reverse ++
      (EncodedCNF.encodeClause
        (SourceClauseGatePrepare.firstClause p
          ⟨(row (.inl (j, 1))).length * a + s, sign⟩)).reverse ++ saved := by
  simp only [finalBank, bank_at, SourceClauseRowGate.final_saved]

end EthInapproximability.CurrentPaper.SourceClauseRowIndexedGate
