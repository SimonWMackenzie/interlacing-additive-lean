import EthInapproximability.CurrentPaper.SourceCSPRowLoopEncoded

/-!
# Encoded source header followed by the fixed physical row loop

The positive-header machine prepares the permanent row-loop bank; the loop
is then run in place through the existing stack embedding. One raw-sequence
handoff is charged. The final theorem starts at the canonical encoded source
bitstring and retains the exact whole-bank terminal state.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopBridgeSequence

open Turing BitMachineEncoding
open SourceCSPRowLoopController

abbrev Stack (q : Nat) := SourceCSPHeaderRowBridge.Stack q
abbrev HeaderLabel (a q : Nat) := BitMachineRawSequence.Label
  (SourceCSPHeaderRowBridge.HeaderLabel a q) SourceCSPHeaderRowBridge.Label5
abbrev HeaderControl := SourceCSPHeaderRowBridge.HeaderControl ×
  SourceCSPHeaderRowBridge.Control5
abbrev RowLabel (q a : Nat) := SourceCSPRowLoopController.Label q (a ^ q)
abbrev RowControl := SourceCSPRowLoopController.Control
abbrev Label (a q : Nat) := BitMachineRawSequence.Label
  (HeaderLabel a q) (RowLabel q a)
abbrev Control := BitMachineRawSequence.Control HeaderControl RowControl

def headerStart (a q : Nat) : HeaderLabel a q :=
  .inl (.inl (.inl (.inl (.inl BitMachineCopy.Label.scan))))

def rowStart (q a : Nat) : RowLabel q a := adminLabel .check

def rowProgram (q a : Nat) (l : RowLabel q a) :
    TM2.Stmt (fun _ : Stack q => Bool) (RowLabel q a) RowControl :=
  BitMachineStackEmbedding.stmt SourceCSPHeaderRowBridge.rowEmbedding
    id id id none (SourceCSPRowLoopController.program q (a ^ q) l)

def program (a q : Nat) : Label a q →
    TM2.Stmt (fun _ : Stack q => Bool) (Label a q) Control :=
  BitMachineRawSequence.program
    (SourceCSPHeaderRowBridge.fullProgram a q) (rowProgram q a)
    (rowStart q a)
    (SourceCSPHeaderRowBridge.headerStart,
      SourceCSPHeaderRowBridge.prepareStart)
    SourceCSPRowLoopController.initialControl

def headerCost (a q : Nat) (P : EncodedETHSource.ConstraintInstance a q) : Nat :=
  SourceCSPPositiveHeader.positiveBound a q
    (EncodedETHSource.constraintBits P).length
    P.constraints.bits.length P.vertices P.constraints +
    2 * (SourceCSPPositiveHeader.rows P).length +
    4 * (P.vertices - 1) + 2 * P.constraints + 14

theorem encoded_rows_run {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (hn : 0 < P.vertices) (hsize : SourceCSPCodec.ValidSize P) :
    ∃ (t : Nat) (costs : List Nat) (S : Stack q → List Bool),
      SourceCSPRowLoopAll.Charges
        (SourceCSPRowLoopEncoded.rowList P) costs ∧
      costs.length = P.constraints ∧
      t ≤ headerCost a q P + costs.sum + 4 ∧
      ((advance (program a q))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (headerStart a q)),
          ((SourceCSPHeaderRowBridge.headerStart,
            SourceCSPHeaderRowBridge.prepareStart),
            SourceCSPRowLoopController.initialControl),
          SourceCSPHeaderRowBridge.initial
            (EncodedETHSource.constraintBits P)⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label a q) Control) =
        ⟨none, ((SourceCSPHeaderRowBridge.headerStart,
          SourceCSPHeaderRowBridge.prepareStart),
          ((queryStart, resetStart), some true)), S⟩ ∧
      (fun k => S (SourceCSPHeaderRowBridge.rowEmbedding k)) =
        Sum.elim (SourceCSPRowQueryFrame.initial []
          (List.replicate (P.vertices - 1) true))
          (fun k : Fin 4 => if k = 1 then
            List.replicate (P.vertices - 1) true else []) := by
  obtain ⟨th, Sh, hth, hhead, hready⟩ :=
    SourceCSPHeaderRowBridge.encoded_row_ready P hn hsize
  obtain ⟨tr, costs, hcosts, hlen, htr, hrow⟩ :=
    SourceCSPRowLoopEncoded.encoded_rows_accept P hn
  let finalBank : SourceCSPHeaderRowBridge.RowOuter q → List Bool :=
    Sum.elim (SourceCSPRowQueryFrame.initial []
      (List.replicate (P.vertices - 1) true))
      (fun k : Fin 4 => if k = 1 then
        List.replicate (P.vertices - 1) true else [])
  let c : SourceCSPRowLoopController.Config q (a ^ q) :=
    ⟨some (rowStart q a), SourceCSPRowLoopController.initialControl,
      SourceCSPHeaderRowBridge.ready
        (SourceCSPPositiveHeader.rows P)
        (List.replicate (P.vertices - 1) true)
        (List.replicate P.constraints true)⟩
  have hrowC : ((advance (SourceCSPRowLoopController.program q (a ^ q)))^[tr]) c =
      ⟨none, ((queryStart, resetStart), some true), finalBank⟩ := by
    simpa only [c, rowStart, finalBank] using hrow
  have hh : (((advance (SourceCSPRowLoopController.program q (a ^ q)))^[tr]) c).l =
      none := by rw [hrowC]
  obtain ⟨u, hu, hrowLift⟩ := BitMachineStackEmbedding.outputs
    SourceCSPHeaderRowBridge.rowEmbedding Sh id id id
    (by intro v; rfl) none
    (SourceCSPRowLoopController.program q (a ^ q)) (rowProgram q a)
    (by intro l; rfl) c tr hh
  rw [hrowC] at hrowLift
  have hstartBank : BitMachineStackEmbedding.bank
      SourceCSPHeaderRowBridge.rowEmbedding Sh c.stk = Sh := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    exact (congrFun hready k).symm
  let Sfinal := BitMachineStackEmbedding.bank
    SourceCSPHeaderRowBridge.rowEmbedding Sh finalBank
  have hrowAmbient : ((advance (rowProgram q a))^[u])
      (⟨some (rowStart q a),
        SourceCSPRowLoopController.initialControl, Sh⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (RowLabel q a) RowControl) =
      ⟨none, ((queryStart, resetStart), some true), Sfinal⟩ := by
    simpa only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
      id_eq, hstartBank, finalBank, Sfinal, c, rowStart] using hrowLift
  obtain ⟨t, ht, hfull⟩ := BitMachineRawSequence.runs
    (SourceCSPHeaderRowBridge.fullProgram a q) (rowProgram q a)
    (headerStart a q) (rowStart q a)
    ((SourceCSPHeaderRowBridge.headerStart,
      SourceCSPHeaderRowBridge.prepareStart) : HeaderControl)
    (SourceCSPHeaderRowBridge.headerStart,
      SourceCSPHeaderRowBridge.prepareStart)
    SourceCSPRowLoopController.initialControl
    ((queryStart, resetStart), some true)
    (SourceCSPHeaderRowBridge.initial
      (EncodedETHSource.constraintBits P)) Sh Sfinal
    th u (by simpa only [headerStart] using hhead) hrowAmbient
  refine ⟨t, costs, Sfinal, hcosts, hlen, ?_, ?_, ?_⟩
  · dsimp only [headerCost]
    omega
  · simpa only [program] using hfull
  · funext k
    exact BitMachineStackEmbedding.bank_at
      SourceCSPHeaderRowBridge.rowEmbedding Sh finalBank k

end EthInapproximability.CurrentPaper.SourceCSPRowLoopBridgeSequence
