import EthInapproximability.CurrentPaper.SourceClauseRowLiteralAddress
import EthInapproximability.CurrentPaper.SourceClauseGateSlotAddress

/-!
# An ordered OR gate whose literal address comes from a checked row query

The first stage physically computes `query(j)*a+s` from the row bank. The
second transfers that binary word to the gate writer. The last stage is the
existing physical prefix-slot address and three-clause OR-gate writer. The
row bank is not used as a preloaded binary-address oracle.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowGate

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack (q : ℕ) := SourceClauseRowLiteralAddress.Stack q ⊕
  (SourceClauseGateSlotAddress.Stack ⊕ Fin 1)

def addressEmbedding {q : ℕ} : SourceClauseRowLiteralAddress.Stack q ↪ Stack q :=
  Function.Embedding.inl
def gateEmbedding {q : ℕ} : SourceClauseGateSlotAddress.Stack ↪ Stack q where
  toFun k := .inr (.inl k)
  inj' := by intro x y h; exact Sum.inl.inj (Sum.inr.inj h)

noncomputable def source {q : ℕ} : Stack q :=
  .inl (.inr (.inr (.inl SourceLabelAddressMachine.counter.input)))
def temp {q : ℕ} : Stack q := .inr (.inr 0)
def literal {q : ℕ} : Stack q :=
  .inr (.inl (.inr (.inr SourceClauseGateSuccessor.literal)))
def targets {q : ℕ} : List (Stack q) := [literal]

inductive CopyLabel where
  | scan | restore | finish
  deriving DecidableEq, Fintype

noncomputable def copyProgram {q : ℕ} : CopyLabel →
    TM2.Stmt (fun _ : Stack q => Bool) CopyLabel (Unit × Option Bool)
  | .scan => BitMachineBroadcast.scanStep source temp .scan .restore
  | .restore => BitMachineBroadcast.restoreStep temp targets .restore .finish
  | .finish => .halt

noncomputable def initial {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (saved output count : List Bool) :
    Stack q → List Bool :=
  Sum.elim (SourceClauseRowLiteralAddress.initial row r a s)
    (Sum.elim (SourceClauseGateSlotAddress.initial n a t slot w []
      saved output count) (fun _ => []))

noncomputable def addressed {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (saved output count : List Bool) :
    Stack q → List Bool :=
  Sum.elim (SourceClauseRowLiteralAddress.finalBank j row r a s)
    (Sum.elim (SourceClauseGateSlotAddress.initial n a t slot w []
      saved output count) (fun _ => []))

noncomputable def copied {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (saved output count : List Bool) :
    Stack q → List Bool :=
  BitMachineBroadcast.copied source temp targets (r * a + s).bits
    (addressed j row r a s n t slot w saved output count)

noncomputable def addressProgram {q : ℕ} (j : Fin q)
    (l : SourceLabelAddressMachine.Label) :=
  stackStmt addressEmbedding (SourceClauseRowLiteralAddress.program j l)

noncomputable def gateProgram {q : ℕ} (sign : Bool)
    (l : BitMachineRawSequence.Label
      (BitMachineRawSequence.Label MatrixAddressMachine.Label
        SourceClauseGateSlotAddress.CopyLabel)
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label SourceLabelAddressMachine.Label
          SourceClauseGateAffineAddress.CopyLabel)
        (BitMachineRawSequence.Label
          (BitMachineRawSequence.Label SourceClauseGateSuccessor.CopyLabel
            BinarySuccessorMachine.Label)
          (BitMachineRawSequence.Label SourceClauseGateMachine.PrepareLabel
            SourceClauseGateMachine.EmitLabel)))) :=
  stackStmt (gateEmbedding (q := q)) (SourceClauseGateSlotAddress.program sign l)

noncomputable def program {q : ℕ} (j : Fin q) (sign : Bool) :=
  BitMachineRawSequence.program
    (BitMachineRawSequence.program (addressProgram j) copyProgram
      CopyLabel.scan
      (false, (SourceLabelAddressMachine.counter.initial, none)) ((), none))
    (gateProgram sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))
    ((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none))
    ((false, ((), none)),
      (((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none)),
        ((((), none), none), SourceClauseGateMachine.control)))

theorem address_initial {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (saved output count : List Bool) :
    bank addressEmbedding (initial row r a s n t slot w saved output count)
      (SourceClauseRowLiteralAddress.initial row r a s) =
      initial row r a s n t slot w saved output count := by
  apply bank_eq_self
  intro k
  rfl

theorem address_final {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (saved output count : List Bool) :
    bank addressEmbedding (initial row r a s n t slot w saved output count)
      (SourceClauseRowLiteralAddress.finalBank j row r a s) =
      addressed j row r a s n t slot w saved output count := by
  funext k
  cases k with
  | inl x => exact bank_at addressEmbedding _ _ x
  | inr x =>
      rw [bank_outside]
      · rfl
      · intro ⟨u, hu⟩; cases hu

theorem address_run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (saved output count : List Bool)
    (h : row (.inl (j, 1)) = List.replicate r true) :
    ∃ ta ≤ MatrixAddressMachine.exactTime r a s +
        UnaryBinaryEncoding.coefficient * (r * a + s + 1) ^ 2 + 1,
      ((advance (addressProgram j))^[ta])
        (⟨some (BitMachineRawSequence.leftLabel .outer),
          (false, (SourceLabelAddressMachine.counter.initial, none)),
          initial row r a s n t slot w saved output count⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            SourceLabelAddressMachine.Label SourceLabelAddressMachine.Control) =
        ⟨none, (false, (SourceLabelAddressMachine.counter.initial, none)),
          addressed j row r a s n t slot w saved output count⟩ := by
  obtain ⟨ta, hta, ha⟩ := SourceClauseRowLiteralAddress.run j row r a s h
  have he := BitMachineStackRun.run addressEmbedding
    (initial row r a s n t slot w saved output count)
    (SourceClauseRowLiteralAddress.program j)
    (⟨some (BitMachineRawSequence.leftLabel .outer),
      (false, (SourceLabelAddressMachine.counter.initial, none)),
      SourceClauseRowLiteralAddress.initial row r a s⟩ :
      TM2.Cfg (fun _ : SourceClauseRowLiteralAddress.Stack q => Bool)
        SourceLabelAddressMachine.Label SourceLabelAddressMachine.Control) ta
  rw [ha] at he
  simp only [stackCfg,
    address_initial j row r a s n t slot w saved output count,
    address_final j row r a s n t slot w saved output count] at he
  exact ⟨ta, hta, he⟩

theorem addressed_source {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (saved output count : List Bool) :
    addressed j row r a s n t slot w saved output count source =
      (r * a + s).bits :=
  SourceClauseRowLiteralAddress.binary_result j row r a s

theorem addressed_temp {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (saved output count : List Bool) :
    addressed j row r a s n t slot w saved output count temp = [] := rfl

theorem copy_run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (saved output count : List Bool) :
    ((advance (copyProgram (q := q)))^[2 * (r * a + s).bits.length + 3])
      (⟨some CopyLabel.scan, ((), none),
        addressed j row r a s n t slot w saved output count⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) CopyLabel (Unit × Option Bool)) =
      ⟨none, ((), none),
        copied j row r a s n t slot w saved output count⟩ := by
  have h := BitMachineBroadcast.broadcast_run copyProgram source temp
    (by simp [source, temp]) targets
    (by simp [targets])
    (by simp [source, targets, literal])
    (by simp [temp, targets, literal])
    .scan .restore .finish rfl rfl () none (r * a + s).bits
    (addressed j row r a s n t slot w saved output count)
    (addressed_source j row r a s n t slot w saved output count)
    (addressed_temp j row r a s n t slot w saved output count)
  rw [show 2 * (r * a + s).bits.length + 3 =
    (2 * (r * a + s).bits.length + 2) + 1 by omega,
    Function.iterate_succ_apply']
  change advance copyProgram
    (BitMachineBroadcast.run copyProgram (2 * (r * a + s).bits.length + 2)
      (⟨some .scan, ((), none),
        addressed j row r a s n t slot w saved output count⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) CopyLabel (Unit × Option Bool))) = _
  rw [h]
  simp [advance, TM2.step, copyProgram, copied]

theorem gate_input {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (saved output count : List Bool)
    (k : SourceClauseGateSlotAddress.Stack) :
    copied j row r a s n t slot w saved output count
      (gateEmbedding k) =
    SourceClauseGateSlotAddress.initial n a t slot w
      (r * a + s).bits saved output count k := by
  by_cases hk : k = (.inr (.inr SourceClauseGateSuccessor.literal) :
      SourceClauseGateSlotAddress.Stack)
  · subst k
    simp [copied, BitMachineBroadcast.copied, source, temp, targets,
      literal, gateEmbedding, addressed,
      SourceClauseGateSlotAddress.initial,
      SourceClauseGateAffineAddress.initial,
      SourceClauseGateSuccessor.initial,
      SourceClauseGateSuccessor.literal,
      SourceClauseGateBroadcast.literalSource,
      SourceClauseGateBroadcast.initial]
  · simp [copied, BitMachineBroadcast.copied, source, temp, targets,
      literal, gateEmbedding, addressed, hk,
      SourceClauseGateSlotAddress.initial,
      SourceClauseGateAffineAddress.initial,
      SourceClauseGateSuccessor.initial,
      SourceClauseGateSuccessor.literal,
      SourceClauseGateBroadcast.literalSource,
      SourceClauseGateBroadcast.initial] at *
    rcases k with k | (k | (k | (k | k)))
    all_goals simp_all [SourceClauseGateSuccessor.literal,
      SourceClauseGateBroadcast.literalSource]
    fin_cases k <;> simp_all

noncomputable def finalBank {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (sign : Bool)
    (saved output count : List Bool) : Stack q → List Bool :=
  bank gateEmbedding (copied j row r a s n t slot w saved output count)
    (SourceClauseGateSlotAddress.finalBank n a t slot w
      ⟨r * a + s, sign⟩ saved output count)

theorem gate_ready {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (saved output count : List Bool) :
    bank gateEmbedding (copied j row r a s n t slot w saved output count)
      (SourceClauseGateSlotAddress.initial n a t slot w
        (r * a + s).bits saved output count) =
      copied j row r a s n t slot w saved output count := by
  apply bank_eq_self
  intro k
  exact (gate_input j row r a s n t slot w saved output count k).symm

theorem gate_run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    ∃ tg ≤ SourceClauseGateSlotAddress.cost n a t slot w
        ⟨r * a + s, sign⟩,
      ((advance (gateProgram (q := q) sign))^[tg])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)),
          ((false, ((), none)),
            (((false, (SourceLabelAddressMachine.counter.initial, none)),
                ((), none)),
              ((((), none), none), SourceClauseGateMachine.control))),
          copied j row r a s n t slot w saved output count⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label MatrixAddressMachine.Label
                SourceClauseGateSlotAddress.CopyLabel)
              (BitMachineRawSequence.Label
                (BitMachineRawSequence.Label SourceLabelAddressMachine.Label
                  SourceClauseGateAffineAddress.CopyLabel)
                (BitMachineRawSequence.Label
                  (BitMachineRawSequence.Label SourceClauseGateSuccessor.CopyLabel
                    BinarySuccessorMachine.Label)
                  (BitMachineRawSequence.Label SourceClauseGateMachine.PrepareLabel
                    SourceClauseGateMachine.EmitLabel))))
            ((Bool × (Unit × Option Bool)) ×
              ((SourceLabelAddressMachine.Control × (Unit × Option Bool)) ×
                (((Unit × Option Bool) × Option Bool) ×
                  (SourceClauseGateMachine.PrepareControl ×
                    SourceClauseGateMachine.EmitControl))))) =
        ⟨none,
          ((false, ((), none)),
            (((false, (SourceLabelAddressMachine.counter.initial, none)),
                ((), none)),
              ((((), none), none), SourceClauseGateMachine.control))),
          finalBank j row r a s n t slot w sign saved output count⟩ := by
  let l : EncodedCNF.Literal := ⟨r * a + s, sign⟩
  obtain ⟨tg, htg, hg⟩ := SourceClauseGateSlotAddress.run n a t slot w l
    saved output count
  have he := BitMachineStackRun.run gateEmbedding
    (copied j row r a s n t slot w saved output count)
    (SourceClauseGateSlotAddress.program sign)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)),
      ((false, ((), none)),
        (((false, (SourceLabelAddressMachine.counter.initial, none)),
            ((), none)),
          ((((), none), none), SourceClauseGateMachine.control))),
      SourceClauseGateSlotAddress.initial n a t slot w l.variable.bits
        saved output count⟩ :
      TM2.Cfg (fun _ : SourceClauseGateSlotAddress.Stack => Bool)
        (BitMachineRawSequence.Label
          (BitMachineRawSequence.Label MatrixAddressMachine.Label
            SourceClauseGateSlotAddress.CopyLabel)
          (BitMachineRawSequence.Label
            (BitMachineRawSequence.Label SourceLabelAddressMachine.Label
              SourceClauseGateAffineAddress.CopyLabel)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label SourceClauseGateSuccessor.CopyLabel
                BinarySuccessorMachine.Label)
              (BitMachineRawSequence.Label SourceClauseGateMachine.PrepareLabel
                SourceClauseGateMachine.EmitLabel))))
        ((Bool × (Unit × Option Bool)) ×
          ((SourceLabelAddressMachine.Control × (Unit × Option Bool)) ×
            (((Unit × Option Bool) × Option Bool) ×
              (SourceClauseGateMachine.PrepareControl ×
                SourceClauseGateMachine.EmitControl))))) tg
  rw [hg] at he
  simp only [stackCfg] at he
  rw [gate_ready j row r a s n t slot w saved output count] at he
  exact ⟨tg, htg, he⟩

noncomputable def cost (r a s n t slot w : ℕ) (sign : Bool) : ℕ :=
  MatrixAddressMachine.exactTime r a s +
  UnaryBinaryEncoding.coefficient * (r * a + s + 1) ^ 2 + 1 +
  (2 * (r * a + s).bits.length + 3) +
  SourceClauseGateSlotAddress.cost n a t slot w ⟨r * a + s, sign⟩ + 2

theorem run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (h : row (.inl (j, 1)) = List.replicate r true) :
    ∃ T ≤ cost r a s n t slot w sign,
      ((advance (program j sign))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))),
          (((false, (SourceLabelAddressMachine.counter.initial, none)),
              ((), none)),
            ((false, ((), none)),
              (((false, (SourceLabelAddressMachine.counter.initial, none)),
                  ((), none)),
                ((((), none), none), SourceClauseGateMachine.control)))),
          initial row r a s n t slot w saved output count⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label SourceLabelAddressMachine.Label
                CopyLabel)
              (BitMachineRawSequence.Label
                (BitMachineRawSequence.Label MatrixAddressMachine.Label
                  SourceClauseGateSlotAddress.CopyLabel)
                (BitMachineRawSequence.Label
                  (BitMachineRawSequence.Label SourceLabelAddressMachine.Label
                    SourceClauseGateAffineAddress.CopyLabel)
                  (BitMachineRawSequence.Label
                    (BitMachineRawSequence.Label SourceClauseGateSuccessor.CopyLabel
                      BinarySuccessorMachine.Label)
                    (BitMachineRawSequence.Label SourceClauseGateMachine.PrepareLabel
                      SourceClauseGateMachine.EmitLabel)))))
            ((SourceLabelAddressMachine.Control × (Unit × Option Bool)) ×
              ((Bool × (Unit × Option Bool)) ×
                ((SourceLabelAddressMachine.Control × (Unit × Option Bool)) ×
                  (((Unit × Option Bool) × Option Bool) ×
                    (SourceClauseGateMachine.PrepareControl ×
                      SourceClauseGateMachine.EmitControl)))))) =
        ⟨none,
          (((false, (SourceLabelAddressMachine.counter.initial, none)),
              ((), none)),
            ((false, ((), none)),
              (((false, (SourceLabelAddressMachine.counter.initial, none)),
                  ((), none)),
                ((((), none), none), SourceClauseGateMachine.control)))),
          finalBank j row r a s n t slot w sign saved output count⟩ := by
  obtain ⟨ta, hta, ha⟩ := address_run j row r a s n t slot w
    saved output count h
  have hc := copy_run j row r a s n t slot w saved output count
  obtain ⟨tab, htab, hab⟩ := BitMachineRawSequence.runs
    (addressProgram j) copyProgram
    (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
    CopyLabel.scan
    (false, (SourceLabelAddressMachine.counter.initial, none))
    (false, (SourceLabelAddressMachine.counter.initial, none))
    ((), none) ((), none)
    (initial row r a s n t slot w saved output count)
    (addressed j row r a s n t slot w saved output count)
    (copied j row r a s n t slot w saved output count)
    ta (2 * (r * a + s).bits.length + 3) ha hc
  obtain ⟨tg, htg, hg⟩ := gate_run j row r a s n t slot w sign
    saved output count
  obtain ⟨T, hT, hrun⟩ := BitMachineRawSequence.runs
    (BitMachineRawSequence.program (addressProgram j) copyProgram
      CopyLabel.scan
      (false, (SourceLabelAddressMachine.counter.initial, none)) ((), none))
    (gateProgram sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))
    ((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none))
    ((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none))
    ((false, ((), none)),
      (((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none)),
        ((((), none), none), SourceClauseGateMachine.control)))
    ((false, ((), none)),
      (((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none)),
        ((((), none), none), SourceClauseGateMachine.control)))
    (initial row r a s n t slot w saved output count)
    (copied j row r a s n t slot w saved output count)
    (finalBank j row r a s n t slot w sign saved output count)
    tab tg hab hg
  refine ⟨T, ?_, hrun⟩
  dsimp [cost] at hta htab htg ⊢
  omega

theorem final_row {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (h : row (.inl (j, 1)) = List.replicate r true)
    (k : SourceCSPRowQueryFrame.Stack q) :
    finalBank j row r a s n t slot w sign saved output count
      (.inl (.inl k)) = row k := by
  rw [finalBank, bank_outside]
  · simp only [copied, BitMachineBroadcast.copied,
      addressed, Sum.elim_inl, Sum.elim_inl]
    split_ifs with hs ht
    · exfalso; simp [source, temp] at hs
    · exfalso; simp [targets, literal] at ht
    · exact SourceClauseRowLiteralAddress.row_preserved j row r a s h k
  · intro ⟨x, hx⟩; cases hx

theorem final_saved {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    let p := slot * w + (n * a + t)
    finalBank j row r a s n t slot w sign saved output count
      (gateEmbedding
        (SourceClauseGateSlotAddress.gateEmbedding
          (SourceClauseGateAffineAddress.gateEmbedding
            (SourceClauseGateTwoAddress.embedding
              (SourceClauseGateMachine.embedding (.inr (.inl 0))))))) =
      (EncodedCNF.encodeClause
        (SourceClauseGatePrepare.thirdClause p ⟨r * a + s, sign⟩)).reverse ++
      (EncodedCNF.encodeClause (SourceClauseGatePrepare.secondClause p)).reverse ++
      (EncodedCNF.encodeClause
        (SourceClauseGatePrepare.firstClause p ⟨r * a + s, sign⟩)).reverse ++
      saved := by
  simp only [finalBank, bank_at, SourceClauseGateSlotAddress.final_saved]

theorem final_count {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s n t slot w : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    finalBank j row r a s n t slot w sign saved output count
      (gateEmbedding
        (SourceClauseGateSlotAddress.gateEmbedding
          (SourceClauseGateAffineAddress.gateEmbedding
            (SourceClauseGateTwoAddress.embedding
              (SourceClauseGateMachine.embedding (.inr (.inr ()))))))) =
      true :: true :: true :: count := by
  simp only [finalBank, bank_at, SourceClauseGateSlotAddress.final_count]

end EthInapproximability.CurrentPaper.SourceClauseRowGate
