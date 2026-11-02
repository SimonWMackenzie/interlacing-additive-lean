import EthInapproximability.CurrentPaper.SourceClauseGateAffineAddress

/-!
# Computing the unary slot offset before an OR gate

Given unary `n,a,t,j,w` and binary literal address, this program computes
`c=n*a+t` in unary, moves it into the affine-address input, then computes
`p=j*w+c` and emits the ordered three-CNF OR gate. For source translation,
`w=width a q+1`; the caller still enumerates clause/position slots.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseGateSlotAddress

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := Fin 6 ⊕ SourceClauseGateAffineAddress.Stack
def offsetEmbedding : Fin 6 ↪ Stack := Function.Embedding.inl
def gateEmbedding : SourceClauseGateAffineAddress.Stack ↪ Stack :=
  Function.Embedding.inr

def offsetSource : Stack := .inl 5
def temp : Stack := .inl 3
def affineOffset : Stack := .inr (.inl (.inl 2))
def targets : List Stack := [affineOffset]

inductive CopyLabel where
  | scan | restore | finish
  deriving DecidableEq, Fintype

def copyProgram : CopyLabel → TM2.Stmt (fun _ : Stack => Bool) CopyLabel
    (Unit × Option Bool)
  | .scan => BitMachineBroadcast.scanStep offsetSource temp .scan .restore
  | .restore => BitMachineBroadcast.restoreStep temp targets .restore .finish
  | .finish => .halt

def offsetInput (n a t : ℕ) : Fin 6 → List Bool :=
  (MatrixAddressMachine.cfg (some .outer) false
    (List.replicate n true) (List.replicate a true)
    (List.replicate t true) [] [] []).stk

def offsetOutput (n a t : ℕ) : Fin 6 → List Bool :=
  (MatrixAddressMachine.cfg none false
    (List.replicate n true) (List.replicate a true)
    (List.replicate t true) [] []
    (List.replicate (n * a + t) true)).stk

noncomputable def initial (n a t j w : ℕ)
    (lword saved output count : List Bool) : Stack → List Bool :=
  Sum.elim (offsetInput n a t)
    (SourceClauseGateAffineAddress.initial j w 0 lword saved output count)

noncomputable def offsetDone (n a t j w : ℕ)
    (lword saved output count : List Bool) : Stack → List Bool :=
  Sum.elim (offsetOutput n a t)
    (SourceClauseGateAffineAddress.initial j w 0 lword saved output count)

noncomputable def transferred (n a t j w : ℕ)
    (lword saved output count : List Bool) : Stack → List Bool :=
  BitMachineBroadcast.copied offsetSource temp targets
    (List.replicate (n * a + t) true)
    (offsetDone n a t j w lword saved output count)

def offsetProgram (q : MatrixAddressMachine.Label) :=
  stackStmt offsetEmbedding (MatrixAddressMachine.program q)

noncomputable def affineProgram (sign : Bool)
    (q : BitMachineRawSequence.Label
      (BitMachineRawSequence.Label SourceLabelAddressMachine.Label
        SourceClauseGateAffineAddress.CopyLabel)
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label SourceClauseGateSuccessor.CopyLabel
          BinarySuccessorMachine.Label)
        (BitMachineRawSequence.Label SourceClauseGateMachine.PrepareLabel
          SourceClauseGateMachine.EmitLabel))) :=
  stackStmt gateEmbedding (SourceClauseGateAffineAddress.program sign q)

noncomputable def program (sign : Bool) :=
  BitMachineRawSequence.program
    (BitMachineRawSequence.program offsetProgram copyProgram CopyLabel.scan
      false ((), none))
    (affineProgram sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))
    (false, ((), none))
    (((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none)),
      ((((), none), none), SourceClauseGateMachine.control))

theorem offset_initial (n a t j w : ℕ)
    (lword saved output count : List Bool) :
    bank offsetEmbedding (initial n a t j w lword saved output count)
      (offsetInput n a t) = initial n a t j w lword saved output count := by
  apply bank_eq_self
  intro k
  rfl

theorem offset_final (n a t j w : ℕ)
    (lword saved output count : List Bool) :
    bank offsetEmbedding (initial n a t j w lword saved output count)
      (offsetOutput n a t) = offsetDone n a t j w lword saved output count := by
  funext k
  cases k with
  | inl i => exact bank_at offsetEmbedding _ _ i
  | inr i =>
      rw [bank_outside]
      · rfl
      · intro ⟨u, hu⟩; cases hu

theorem offset_run (n a t j w : ℕ)
    (lword saved output count : List Bool) :
    ((advance offsetProgram)^[MatrixAddressMachine.exactTime n a t])
      (⟨some MatrixAddressMachine.Label.outer, false,
        initial n a t j w lword saved output count⟩ :
        TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool) =
      ⟨none, false, offsetDone n a t j w lword saved output count⟩ := by
  have h := MatrixAddressMachine.address_run n a t false []
  change ((advance MatrixAddressMachine.program)^[MatrixAddressMachine.exactTime n a t])
    (MatrixAddressMachine.cfg (some .outer) false
      (List.replicate n true) (List.replicate a true)
      (List.replicate t true) [] [] []) = _ at h
  have he := BitMachineStackRun.run offsetEmbedding
    (initial n a t j w lword saved output count)
    MatrixAddressMachine.program
    (MatrixAddressMachine.cfg (some .outer) false
      (List.replicate n true) (List.replicate a true)
      (List.replicate t true) [] [] [])
    (MatrixAddressMachine.exactTime n a t)
  rw [h] at he
  simp only [stackCfg] at he
  simp only [List.append_nil] at he
  change ((advance offsetProgram)^[MatrixAddressMachine.exactTime n a t])
    (⟨some .outer, false,
      bank offsetEmbedding (initial n a t j w lword saved output count)
        (offsetInput n a t)⟩ :
      TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool) =
    ⟨none, false,
      bank offsetEmbedding (initial n a t j w lword saved output count)
        (offsetOutput n a t)⟩ at he
  rw [offset_initial, offset_final] at he
  exact he

theorem copy_run (n a t j w : ℕ)
    (lword saved output count : List Bool) :
    let c := n * a + t
    ((advance copyProgram)^[2 * c + 3])
      (⟨some CopyLabel.scan, ((), none),
        offsetDone n a t j w lword saved output count⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)) =
      ⟨none, ((), none), transferred n a t j w lword saved output count⟩ := by
  dsimp only
  let c := n * a + t
  have h := BitMachineBroadcast.broadcast_run copyProgram offsetSource temp
    (by decide) targets (by simp [targets])
    (by simp [offsetSource, targets, affineOffset])
    (by simp [temp, targets, affineOffset])
    .scan .restore .finish rfl rfl () none
    (List.replicate c true)
    (offsetDone n a t j w lword saved output count) rfl rfl
  rw [show 2 * c + 3 = (2 * (List.replicate c true).length + 2) + 1 by simp,
    Function.iterate_succ_apply']
  change advance copyProgram
    (BitMachineBroadcast.run copyProgram (2 * (List.replicate c true).length + 2)
      (⟨some .scan, ((), none),
        offsetDone n a t j w lword saved output count⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool))) = _
  rw [h]
  simp [advance, TM2.step, copyProgram, transferred, c]

theorem affine_initial (n a t j w : ℕ)
    (lword saved output count : List Bool) :
    bank gateEmbedding (transferred n a t j w lword saved output count)
      (SourceClauseGateAffineAddress.initial j w (n * a + t)
        lword saved output count) =
      transferred n a t j w lword saved output count := by
  apply bank_eq_self
  intro k
  cases k with
  | inl i =>
      cases i with
      | inl z => fin_cases z <;>
          simp [transferred, BitMachineBroadcast.copied,
            offsetSource, temp, affineOffset, targets,
            offsetDone, gateEmbedding,
            SourceClauseGateAffineAddress.initial,
            SourceLabelAddressMachine.inputs,
            SourceLabelAddressMachine.ambient]
      | inr z => simp [transferred, BitMachineBroadcast.copied,
          offsetSource, temp, affineOffset, targets,
          offsetDone, gateEmbedding,
          SourceClauseGateAffineAddress.initial,
          SourceLabelAddressMachine.inputs,
          SourceLabelAddressMachine.ambient]
  | inr z => simp [transferred, BitMachineBroadcast.copied,
      offsetSource, temp, affineOffset, targets,
      offsetDone, gateEmbedding,
      SourceClauseGateAffineAddress.initial]

noncomputable def finalBank (n a t j w : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) : Stack → List Bool :=
  bank gateEmbedding (transferred n a t j w l.variable.bits saved output count)
    (SourceClauseGateAffineAddress.finalBank j w (n * a + t)
      l saved output count)

noncomputable def cost (n a t j w : ℕ) (l : EncodedCNF.Literal) : ℕ :=
  let c := n * a + t
  let p := j * w + c
  MatrixAddressMachine.exactTime n a t + (2 * c + 3) +
    (MatrixAddressMachine.exactTime j w c +
      UnaryBinaryEncoding.coefficient * (p + 1) ^ 2 +
      6 * p.bits.length +
      2 * (l.variable.bits.length + p.bits.length + (p + 1).bits.length) +
      SourceLiteralWriter.emitTime
        (SourceLiteralWriter.words (SourceClauseGatePrepare.firstClause p l)) +
      SourceLiteralWriter.emitTime
        (SourceLiteralWriter.words (SourceClauseGatePrepare.secondClause p)) +
      SourceLiteralWriter.emitTime
        (SourceLiteralWriter.words (SourceClauseGatePrepare.thirdClause p l)) + 37) + 2

theorem run (n a t j w : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    ∃ T ≤ cost n a t j w l,
      ((advance (program l.positive))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)),
          ((false, ((), none)),
            (((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none)),
              ((((), none), none), SourceClauseGateMachine.control))),
          initial n a t j w l.variable.bits saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label MatrixAddressMachine.Label CopyLabel)
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
            (((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none)),
              ((((), none), none), SourceClauseGateMachine.control))),
          finalBank n a t j w l saved output count⟩ := by
  let c := n * a + t
  obtain ⟨tab, htab, hab⟩ := BitMachineRawSequence.runs
    offsetProgram copyProgram MatrixAddressMachine.Label.outer CopyLabel.scan
    false false ((), none) ((), none)
    (initial n a t j w l.variable.bits saved output count)
    (offsetDone n a t j w l.variable.bits saved output count)
    (transferred n a t j w l.variable.bits saved output count)
    (MatrixAddressMachine.exactTime n a t) (2 * c + 3)
    (offset_run n a t j w l.variable.bits saved output count)
    (copy_run n a t j w l.variable.bits saved output count)
  obtain ⟨tg, htg, hg⟩ := SourceClauseGateAffineAddress.run
    j w c l saved output count
  have hg' := BitMachineStackRun.run gateEmbedding
    (transferred n a t j w l.variable.bits saved output count)
    (SourceClauseGateAffineAddress.program l.positive)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))),
      (((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none)),
        ((((), none), none), SourceClauseGateMachine.control)),
      SourceClauseGateAffineAddress.initial j w c l.variable.bits
        saved output count⟩ :
      TM2.Cfg (fun _ : SourceClauseGateAffineAddress.Stack => Bool)
        (BitMachineRawSequence.Label
          (BitMachineRawSequence.Label SourceLabelAddressMachine.Label
            SourceClauseGateAffineAddress.CopyLabel)
          (BitMachineRawSequence.Label
            (BitMachineRawSequence.Label SourceClauseGateSuccessor.CopyLabel
              BinarySuccessorMachine.Label)
            (BitMachineRawSequence.Label SourceClauseGateMachine.PrepareLabel
              SourceClauseGateMachine.EmitLabel)))
        ((SourceLabelAddressMachine.Control × (Unit × Option Bool)) ×
          (((Unit × Option Bool) × Option Bool) ×
            (SourceClauseGateMachine.PrepareControl ×
              SourceClauseGateMachine.EmitControl)))) tg
  rw [hg] at hg'
  simp only [stackCfg] at hg'
  rw [affine_initial n a t j w l.variable.bits saved output count] at hg'
  obtain ⟨T, hT, hrun⟩ := BitMachineRawSequence.runs
    (BitMachineRawSequence.program offsetProgram copyProgram CopyLabel.scan
      false ((), none))
    (affineProgram l.positive)
    (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))
    (false, ((), none)) (false, ((), none))
    (((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none)),
      ((((), none), none), SourceClauseGateMachine.control))
    (((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none)),
      ((((), none), none), SourceClauseGateMachine.control))
    (initial n a t j w l.variable.bits saved output count)
    (transferred n a t j w l.variable.bits saved output count)
    (finalBank n a t j w l saved output count)
    tab tg hab hg'
  refine ⟨T, ?_, hrun⟩
  dsimp [c, cost] at htab htg ⊢
  omega

theorem source_prefix_address (n a q j t : ℕ) :
    j * (SourceBooleanEncoding.width a q + 1) + (n * a + t) =
      n * a + j * (SourceBooleanEncoding.width a q + 1) + t := by
  omega

theorem final_saved (n a t j w : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    let p := j * w + (n * a + t)
    finalBank n a t j w l saved output count
      (gateEmbedding
        (SourceClauseGateAffineAddress.gateEmbedding
          (SourceClauseGateTwoAddress.embedding
            (SourceClauseGateMachine.embedding (.inr (.inl 0)))))) =
      (EncodedCNF.encodeClause (SourceClauseGatePrepare.thirdClause p l)).reverse ++
      (EncodedCNF.encodeClause (SourceClauseGatePrepare.secondClause p)).reverse ++
      (EncodedCNF.encodeClause (SourceClauseGatePrepare.firstClause p l)).reverse ++
      saved := by
  simp only [finalBank, bank_at, SourceClauseGateAffineAddress.final_saved]

theorem final_count (n a t j w : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    finalBank n a t j w l saved output count
      (gateEmbedding
        (SourceClauseGateAffineAddress.gateEmbedding
          (SourceClauseGateTwoAddress.embedding
            (SourceClauseGateMachine.embedding (.inr (.inr ())))))) =
      true :: true :: true :: count := by
  simp only [finalBank, bank_at, SourceClauseGateAffineAddress.final_count]

theorem final_output (n a t j w : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    finalBank n a t j w l saved output count
      (gateEmbedding
        (SourceClauseGateAffineAddress.gateEmbedding
          (SourceClauseGateTwoAddress.embedding
            (SourceClauseGateMachine.embedding (.inr (.inl 1)))))) = output := by
  simp only [finalBank, bank_at, SourceClauseGateAffineAddress.final_output]

end EthInapproximability.CurrentPaper.SourceClauseGateSlotAddress
