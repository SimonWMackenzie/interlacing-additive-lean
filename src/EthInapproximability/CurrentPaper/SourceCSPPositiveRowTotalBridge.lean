import EthInapproximability.CurrentPaper.SourceCSPPositiveRowEntry
import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalPolynomial

/-!
# Post-dispatch positive cap and corrected all-input row loop

One finite program runs the physical cap/row-bank entry and then the
corrected total row loop on the same ambient stacks. It starts from a
canonical vertex word and bounded unary count already supplied by the raw
header guard. No row-list acceptance is assumed in its machine control.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPPositiveRowTotalBridge

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack (q : Nat) := SourceCSPHeaderRowBridge.Stack q
abbrev EntryLabel (q : Nat) := BitMachineRawSequence.Label
  (SourceCSPPositiveRowEntry.CapEntryLabel q)
  SourceCSPHeaderRowBridge.Label5
abbrev EntryControl := SourceCSPPositiveRowEntry.CapEntryControl ×
  SourceCSPHeaderRowBridge.Control5
abbrev RowLabel (q a : Nat) := SourceCSPRowLoopController.Label q (a ^ q)
abbrev RowControl := SourceCSPRowLoopController.Control

def rowProgram (q a : Nat) (l : RowLabel q a) :
    TM2.Stmt (fun _ : Stack q => Bool) (RowLabel q a) RowControl :=
  stmt SourceCSPHeaderRowBridge.rowEmbedding id id id none
    (SourceCSPRowLoopTotalController.program q (a ^ q) l)

def entryInitial : EntryControl :=
  (((), (((none, none), (((none, none), (none, false)), none)))),
    SourceCSPHeaderRowBridge.prepareStart)

def program (a q : Nat) :=
  BitMachineRawSequence.program
    (SourceCSPPositiveRowEntry.program q) (rowProgram q a)
    (SourceCSPRowLoopController.adminLabel .check)
    entryInitial SourceCSPRowLoopController.initialControl

def rowExtras (m : Nat) (cap : List Bool) : Fin 4 → List Bool :=
  fun k => if k = 0 then List.replicate m true
    else if k = 1 then cap else []

theorem ready_eq_row_start {q : Nat} (source cap : List Bool) (m : Nat) :
    SourceCSPHeaderRowBridge.ready (q := q) source cap
      (List.replicate m true) =
      Sum.elim (SourceCSPRowQueryFrame.initial (q := q) source cap)
        (rowExtras m cap) := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

def entryBound (n m q : Nat) (source : List Bool) : Nat :=
  2 + q * (2 * m + 3) + 3 +
    (2 * n.bits.length + 2 + (2 * (q * m) + 2) + 1 +
      (q * m + 1) * (4 * n.bits.length + 5) + 3) + 1 +
    (2 * source.length + 4 * (n - 1) + 2 * m + 13) + 1

/-- On every raw row suffix, this one positive-path machine terminates and
reports the codec's exact all-row parse/EOF predicate, in a cubic input-length
bound after the guarded header's numeric premises are supplied. -/
theorem positive_rows_total (n m a q L : Nat)
    (before : SourceCSPBudgetFrame.Stack → List Bool)
    (hn : 0 < n) (hsize : n ≤ q * m) (hmL : m ≤ L)
    (hsourceL : (before SourceCSPPositiveSuffix.rowSlot).length ≤ L)
    (hcapL : n - 1 ≤ q * L)
    (hm : before (.inl (.inr 6)) = List.replicate m true)
    (hnword : before (.inl (.inl (.inl (.inl 0)))) = n.bits)
    (hstatus : before (.inr 0) = [])
    (htarget : before (.inr 1) = []) (hwork : before (.inr 2) = [])
    (hunused : ∀ k : Fin 7, 3 ≤ k.val → before (.inr k) = []) :
    ∃ t S v b,
      t ≤ entryBound n m q
        (before SourceCSPPositiveSuffix.rowSlot) +
        SourceCSPRowLoopTotalPolynomial.loopCoefficient q (a ^ q) *
          (L + 1) ^ 3 + 1 ∧
      ((advance (program a q))^[t])
        (⟨some (.inl (.inl (.inl SourceCSPPositiveCapEntry.start))),
          (entryInitial, SourceCSPRowLoopController.initialControl),
          SourceCSPPositiveRowEntry.initial before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (BitMachineRawSequence.Label (EntryLabel q) (RowLabel q a))
            (EntryControl × RowControl)) =
        ⟨none, (entryInitial, (v, some b)), S⟩ ∧
      (b = true ↔ ∃ rows : Fin m → SourceCSPCodec.Row n a q,
        SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m
          (before SourceCSPPositiveSuffix.rowSlot) = some (rows, [])) := by
  obtain ⟨te, Se, hte, hre, hready⟩ :=
    SourceCSPPositiveRowEntry.positive_row_ready n m q before
      hn hsize hm hnword hstatus htarget hwork hunused
  let source := before SourceCSPPositiveSuffix.rowSlot
  let cap := List.replicate (n - 1) true
  let E := rowExtras m cap
  have hcount : E 0 = List.replicate m true := rfl
  have hcap : E 1 = cap := rfl
  have hscratch : E 3 = [] := rfl
  obtain ⟨tr, Sr, vr, br, htr, hrr, hsem⟩ :=
    SourceCSPRowLoopTotalPolynomial.rows_total_codec_cubic
      n a q m L source E hn hmL hsourceL hcapL
      hcount hcap hscratch
  let localCfg : SourceCSPRowLoopController.Config q (a ^ q) :=
    ⟨some (SourceCSPRowLoopController.adminLabel .check),
      SourceCSPRowLoopController.initialControl,
      SourceCSPHeaderRowBridge.ready source cap (List.replicate m true)⟩
  have hlocal : ((advance
      (SourceCSPRowLoopTotalController.program q (a ^ q)))^[tr])
      localCfg = ⟨none, (vr, some br), Sr⟩ := by
    simpa only [localCfg, ready_eq_row_start source cap m, source,
      cap, E] using hrr
  have hhalt : (((advance
      (SourceCSPRowLoopTotalController.program q (a ^ q)))^[tr])
      localCfg).l = none := by rw [hlocal]
  obtain ⟨u, hu, hrowLift⟩ := outputs
    SourceCSPHeaderRowBridge.rowEmbedding Se id id id
    (fun _ => rfl) none
    (SourceCSPRowLoopTotalController.program q (a ^ q)) (rowProgram q a)
    (fun _ => rfl) localCfg tr hhalt
  rw [hlocal] at hrowLift
  have hstartBank : bank SourceCSPHeaderRowBridge.rowEmbedding
      Se localCfg.stk = Se := by
    apply bank_eq_self
    intro k
    exact (congrFun hready k).symm
  let Sfinal := bank SourceCSPHeaderRowBridge.rowEmbedding Se Sr
  have hambient : ((advance (rowProgram q a))^[u])
      (⟨some (SourceCSPRowLoopController.adminLabel .check),
        SourceCSPRowLoopController.initialControl, Se⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (RowLabel q a) RowControl) =
      ⟨none, (vr, some br), Sfinal⟩ := by
    simpa only [cfg, stackCfg, BitMachineInline.cfg, id_eq,
      hstartBank, Sfinal, localCfg] using hrowLift
  obtain ⟨t, ht, hfull⟩ := BitMachineRawSequence.runs
    (SourceCSPPositiveRowEntry.program q) (rowProgram q a)
    (.inl (.inl SourceCSPPositiveCapEntry.start) : EntryLabel q)
    (SourceCSPRowLoopController.adminLabel .check : RowLabel q a)
    entryInitial entryInitial
    SourceCSPRowLoopController.initialControl (vr, some br)
    (SourceCSPPositiveRowEntry.initial before) Se Sfinal
    te u (by simpa only [entryInitial] using hre) hambient
  refine ⟨t, Sfinal, vr, br, ?_, ?_, hsem⟩
  · dsimp only [entryBound] at hte ⊢
    omega
  · simpa only [program] using hfull

end EthInapproximability.CurrentPaper.SourceCSPPositiveRowTotalBridge
