import EthInapproximability.CurrentPaper.SourceCSPGlobalPrepareFromCap

/-!
# Corrected row-loop lift in the global CSP table

The global row arm executes the actual all-input corrected row controller on
the physically prepared bank. This lift retains every header-side stack cell;
the row outcome is only a finite-control validation result, not emitted CNF.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGlobalRowsFromReady

open Turing BitMachineEncoding BitMachineStackEmbedding

theorem row_lift (a q : Nat)
    (before : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (t : Nat) (T : SourceCSPRowLoopController.Stack q → List Bool)
    (v : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl) (b : Bool)
    (rows cap unaryM : List Bool)
    (hready : (fun k => before (SourceCSPHeaderRowBridge.rowEmbedding k)) =
      SourceCSPHeaderRowBridge.ready rows cap unaryM)
    (hr : ((advance (SourceCSPRowLoopTotalController.program q (a ^ q)))^[t])
      (⟨some (SourceCSPRowLoopController.adminLabel .check),
        SourceCSPRowLoopController.initialControl,
        SourceCSPHeaderRowBridge.ready rows cap unaryM⟩ :
          SourceCSPRowLoopController.Config q (a ^ q)) =
      ⟨none, (v, some b), T⟩) :
    ∃ u S, u ≤ t ∧
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[u])
        (⟨some (.row (SourceCSPRowLoopController.adminLabel .check)),
          .row SourceCSPRowLoopController.initialControl, before⟩ :
          TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
            (SourceCSPGlobalDecisionProgram.Label a q)
            (SourceCSPGlobalDecisionProgram.Control a q)) =
        ⟨some .afterRow, .row (v, some b), S⟩ ∧
      (∀ k : SourceCSPRowLoopController.Stack q,
        S (SourceCSPHeaderRowBridge.rowEmbedding k) = T k) ∧
      (∀ k : SourceCSPGlobalDecisionProgram.Stack q,
        (¬ ∃ j, SourceCSPHeaderRowBridge.rowEmbedding j = k) →
          S k = before k) := by
  let localCfg : SourceCSPRowLoopController.Config q (a ^ q) :=
    ⟨some (SourceCSPRowLoopController.adminLabel .check),
      SourceCSPRowLoopController.initialControl,
      SourceCSPHeaderRowBridge.ready rows cap unaryM⟩
  have hhalt : (((advance
      (SourceCSPRowLoopTotalController.program q (a ^ q)))^[t])
      localCfg).l = none := by
    simpa only [localCfg] using congrArg (fun x => x.l) hr
  let read : SourceCSPGlobalDecisionProgram.Control a q →
      SourceCSPRowLoopController.Control :=
    fun x => match x with
      | .row w => w
      | _ => SourceCSPRowLoopController.initialControl
  have hleft : Function.LeftInverse read
      SourceCSPGlobalDecisionProgram.Control.row := by
    intro w
    rfl
  obtain ⟨ur, hur, hglobal⟩ := outputs
    SourceCSPHeaderRowBridge.rowEmbedding before
    SourceCSPGlobalDecisionProgram.Label.row
    SourceCSPGlobalDecisionProgram.Control.row
    read hleft (some .afterRow)
    (SourceCSPRowLoopTotalController.program q (a ^ q))
    (SourceCSPGlobalDecisionProgram.program a q)
    (fun _ => rfl) localCfg t hhalt
  rw [hr] at hglobal
  have hstart : BitMachineStackEmbedding.cfg
      SourceCSPHeaderRowBridge.rowEmbedding before
      SourceCSPGlobalDecisionProgram.Label.row
      SourceCSPGlobalDecisionProgram.Control.row
      (some .afterRow) localCfg =
      (⟨some (.row (SourceCSPRowLoopController.adminLabel .check)),
        .row SourceCSPRowLoopController.initialControl, before⟩ :
        TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
          (SourceCSPGlobalDecisionProgram.Label a q)
          (SourceCSPGlobalDecisionProgram.Control a q)) := by
    simp only [BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, localCfg]
    congr 1
    apply bank_eq_self
    intro k
    exact (congrFun hready k).symm
  rw [hstart] at hglobal
  let S := bank SourceCSPHeaderRowBridge.rowEmbedding before T
  refine ⟨ur, S, hur, ?_, ?_, ?_⟩
  · simpa only [S, BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, id_eq, Option.map_none] using hglobal
  · intro k
    exact bank_at SourceCSPHeaderRowBridge.rowEmbedding before T k
  · intro k hk
    exact bank_outside SourceCSPHeaderRowBridge.rowEmbedding before T k hk

/-- A physically prepared positive row bank is validated by the corrected
all-input controller. Its finite result agrees exactly with the codec's
all-row parse and final EOF predicate, with a cubic transition bound. -/
theorem global_rows_total (n m a q L : Nat)
    (source : List Bool)
    (before : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hn : 0 < n) (hm : m ≤ L) (hsource : source.length ≤ L)
    (hcapL : n - 1 ≤ q * L)
    (hready : (fun k => before (SourceCSPHeaderRowBridge.rowEmbedding k)) =
      SourceCSPHeaderRowBridge.ready source
        (List.replicate (n - 1) true) (List.replicate m true)) :
    ∃ (t : Nat) (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
      (v : SourceCSPRowLoopController.QueryControl ×
        SourceCSPRowLoopController.ResetControl) (b : Bool),
      t ≤ SourceCSPRowLoopTotalPolynomial.loopCoefficient q (a ^ q) *
        (L + 1) ^ 3 ∧
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
        (⟨some (.row (SourceCSPRowLoopController.adminLabel .check)),
          .row SourceCSPRowLoopController.initialControl, before⟩ :
          TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
            (SourceCSPGlobalDecisionProgram.Label a q)
            (SourceCSPGlobalDecisionProgram.Control a q)) =
        ⟨some .afterRow, .row (v, some b), S⟩ ∧
      (b = true ↔ ∃ rows : Fin m → SourceCSPCodec.Row n a q,
        SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m source =
          some (rows, [])) ∧
      S SourceCSPGlobalDecisionProgram.savedSource =
        before SourceCSPGlobalDecisionProgram.savedSource ∧
      S SourceCSPHeaderRowBridge.capSource =
        before SourceCSPHeaderRowBridge.capSource := by
  let cap := List.replicate (n - 1) true
  let E := SourceCSPPositiveRowTotalBridge.rowExtras m cap
  have hc : E 0 = List.replicate m true := rfl
  have hv : E 1 = cap := rfl
  have hs : E 3 = [] := rfl
  obtain ⟨tr, Tr, vr, br, htr, hrr, hsem⟩ :=
    SourceCSPRowLoopTotalPolynomial.rows_total_codec_cubic
      n a q m L source E hn hm hsource hcapL hc hv hs
  have hlocal : ((advance
      (SourceCSPRowLoopTotalController.program q (a ^ q)))^[tr])
      (⟨some (SourceCSPRowLoopController.adminLabel .check),
        SourceCSPRowLoopController.initialControl,
        SourceCSPHeaderRowBridge.ready source cap
          (List.replicate m true)⟩ :
            SourceCSPRowLoopController.Config q (a ^ q)) =
      ⟨none, (vr, some br), Tr⟩ := by
    simpa only [cap, E,
      SourceCSPPositiveRowTotalBridge.ready_eq_row_start
        source cap m] using hrr
  obtain ⟨u, S, hu, hrun, _, hforeign⟩ :=
    row_lift a q before tr Tr vr br source cap
      (List.replicate m true) hready hlocal
  refine ⟨u, S, vr, br, by omega, hrun, hsem, ?_, ?_⟩
  · apply hforeign
    rintro ⟨j, hj⟩
    cases j with
    | inl j =>
        simp [SourceCSPHeaderRowBridge.rowEmbedding,
          SourceCSPGlobalDecisionProgram.savedSource,
          SourceCSPHeaderRowBridge.scratch] at hj
    | inr j =>
        fin_cases j <;> simp
          [SourceCSPHeaderRowBridge.rowEmbedding,
          SourceCSPGlobalDecisionProgram.savedSource,
          SourceCSPHeaderRowBridge.scratch] at hj
  · apply hforeign
    rintro ⟨j, hj⟩
    cases j <;> simp [SourceCSPHeaderRowBridge.rowEmbedding,
      SourceCSPHeaderRowBridge.capSource] at hj

end EthInapproximability.CurrentPaper.SourceCSPGlobalRowsFromReady
