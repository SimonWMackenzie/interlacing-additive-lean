import EthInapproximability.CurrentPaper.SourceCSPRowLoopCost
import EthInapproximability.CurrentPaper.SourceCSPRowLoopBridgeSequence

/-!
# Numerical runtime of the encoded physical source-row loop

`totalBound` depends only on the canonical rows and fixed source parameters;
no intermediate machine bank or chosen witness appears in its statement.
The bound charges every row parser/query call, every physical bank reset and
cap copy, the unary counter/EOF transitions, and the header-to-loop handoff.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalCost

open Turing BitMachineEncoding
open SourceCSPRowLoopAll SourceCSPRowLoopCost

variable {n a q : Nat}

def rowBound (row : Row (n := n) (a := a) (q := q))
    (rest : List Bool) : Nat :=
  queryCost row rest n + 1 + resetBound row rest

def totalBound : List (Row (n := n) (a := a) (q := q)) → Nat
  | [] => 0
  | row :: tail => rowBound row (rowBytes tail) + totalBound tail

theorem charges_bound {rows : List (Row (n := n) (a := a) (q := q))}
    {costs : List Nat} (h : Charges rows costs) :
    costs.sum ≤ totalBound rows := by
  induction h with
  | nil => rfl
  | cons row tail U costs hproduced hcosts ih =>
      have hr := produced_reset_bound row (rowBytes tail)
        (List.replicate tail.length true) U hproduced
      simp only [List.sum_cons, totalBound, stepCost, rowBound]
      omega

theorem encoded_rows_bound {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (hn : 0 < P.vertices) :
    ∃ t,
      t ≤ totalBound (SourceCSPRowLoopEncoded.rowList P) + 3 ∧
      ((advance (SourceCSPRowLoopController.program q (a ^ q)))^[t])
        (⟨some (SourceCSPRowLoopController.adminLabel .check),
          SourceCSPRowLoopController.initialControl,
          SourceCSPHeaderRowBridge.ready
            (SourceCSPPositiveHeader.rows P)
            (List.replicate (P.vertices - 1) true)
            (List.replicate P.constraints true)⟩ :
          SourceCSPRowLoopController.Config q (a ^ q)) =
        ⟨none,
          ((SourceCSPRowLoopController.queryStart,
            SourceCSPRowLoopController.resetStart), some true),
          Sum.elim (SourceCSPRowQueryFrame.initial []
            (List.replicate (P.vertices - 1) true))
            (fun k : Fin 4 => if k = 1 then
              List.replicate (P.vertices - 1) true else [])⟩ := by
  obtain ⟨t, costs, hc, _, ht, hr⟩ :=
    SourceCSPRowLoopEncoded.encoded_rows_accept P hn
  have hb := charges_bound hc
  exact ⟨t, by omega, hr⟩

theorem encoded_full_bound {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (hn : 0 < P.vertices) (hsize : SourceCSPCodec.ValidSize P) :
    ∃ (t : Nat) (S : SourceCSPRowLoopBridgeSequence.Stack q → List Bool),
      t ≤ SourceCSPRowLoopBridgeSequence.headerCost a q P +
        totalBound (SourceCSPRowLoopEncoded.rowList P) + 4 ∧
      ((advance (SourceCSPRowLoopBridgeSequence.program a q))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (SourceCSPRowLoopBridgeSequence.headerStart a q)),
          ((SourceCSPHeaderRowBridge.headerStart,
            SourceCSPHeaderRowBridge.prepareStart),
            SourceCSPRowLoopController.initialControl),
          SourceCSPHeaderRowBridge.initial
            (EncodedETHSource.constraintBits P)⟩ :
          TM2.Cfg (fun _ : SourceCSPRowLoopBridgeSequence.Stack q => Bool)
            (SourceCSPRowLoopBridgeSequence.Label a q)
            SourceCSPRowLoopBridgeSequence.Control) =
        ⟨none, ((SourceCSPHeaderRowBridge.headerStart,
          SourceCSPHeaderRowBridge.prepareStart),
          ((SourceCSPRowLoopController.queryStart,
            SourceCSPRowLoopController.resetStart), some true)), S⟩ ∧
      (fun k => S (SourceCSPHeaderRowBridge.rowEmbedding k)) =
        Sum.elim (SourceCSPRowQueryFrame.initial []
          (List.replicate (P.vertices - 1) true))
          (fun k : Fin 4 => if k = 1 then
            List.replicate (P.vertices - 1) true else []) := by
  obtain ⟨t, costs, S, hc, _, ht, hr, hs⟩ :=
    SourceCSPRowLoopBridgeSequence.encoded_rows_run P hn hsize
  have hb := charges_bound hc
  exact ⟨t, S, by omega, hr, hs⟩

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalCost
