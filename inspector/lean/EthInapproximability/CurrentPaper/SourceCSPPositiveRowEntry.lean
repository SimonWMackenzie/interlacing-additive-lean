import EthInapproximability.CurrentPaper.SourceCSPPositiveCapEntry
import EthInapproximability.CurrentPaper.SourceCSPHeaderRowBridge

/-!
# Physical post-dispatch positive entry in the shared row bank

The guarded raw header and branch selector use the input-side bank.  This
adapter reserves the row-loop bank as genuine blank foreign stacks, runs the
one-push positive cap machine, then uses the existing physical row-preparation
copies.  Its hypotheses identify an actual positive post-dispatch bank; it
does not assume that every raw input reaches those hypotheses.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPPositiveRowEntry

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack (q : Nat) := SourceCSPHeaderRowBridge.Stack q
abbrev CapLabel (q : Nat) := SourceCSPPositiveCapEntry.CapLabel q
abbrev CapControl := SourceCSPPositiveCapEntry.CapControl

def initial {q : Nat} (before : SourceCSPBudgetFrame.Stack → List Bool) :
    Stack q → List Bool
  | .inl k => before k
  | .inr _ => []

def capProgram {q : Nat} (l : BitMachineRawSequence.Label Unit (CapLabel q)) :=
  stmt (SourceCSPHeaderRowBridge.headerEmbedding (q := q)) id id id none
    (SourceCSPPositiveCapEntry.program q l)

/-- An actual positive cap run on the shared bank leaves all row-loop stacks
blank and retains the source suffix; no semantic row is manufactured. -/
theorem framed_positive (n m q : Nat)
    (before : SourceCSPBudgetFrame.Stack → List Bool)
    (hn : 0 < n) (hsize : n ≤ q * m)
    (hm : before (.inl (.inr 6)) = List.replicate m true)
    (hnword : before (.inl (.inl (.inl (.inl 0)))) = n.bits)
    (hstatus : before (.inr 0) = [])
    (htarget : before (.inr 1) = []) (hwork : before (.inr 2) = [])
    (hunused : ∀ k : Fin 7, 3 ≤ k.val → before (.inr k) = []) :
    ∃ t v S,
      t ≤ 2 + q * (2 * m + 3) + 3 +
        (2 * n.bits.length + 2 + (2 * (q * m) + 2) + 1 +
          (q * m + 1) * (4 * n.bits.length + 5) + 3) + 1 ∧
      ((advance (capProgram (q := q)))^[t])
        (⟨some (.inl SourceCSPPositiveCapEntry.start),
          ((), (((none, none), (((none, none), (none, false)), none)) : CapControl)),
          initial before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (BitMachineRawSequence.Label Unit (CapLabel q))
            (Unit × CapControl)) =
        ⟨none, ((), ((none, none), v)), S⟩ ∧
      S SourceCSPHeaderRowBridge.source =
        before SourceCSPPositiveSuffix.rowSlot ∧
      S SourceCSPHeaderRowBridge.count = List.replicate m true ∧
      S SourceCSPHeaderRowBridge.capSource =
        true :: List.replicate (n - 1) true ∧
      (∀ k : SourceCSPRowQueryFrame.Stack q ⊕ Fin 5,
        S (.inr k) = []) := by
  obtain ⟨tc, vc, Sc, htc, hrc, hcap, hmc, hrow⟩ :=
    SourceCSPPositiveCapEntry.positive_success_row n m q before
      hn hsize hm hnword hstatus htarget hwork hunused
  let localCfg : TM2.Cfg (fun _ : SourceCSPBudgetFrame.Stack => Bool)
      (BitMachineRawSequence.Label Unit (CapLabel q)) (Unit × CapControl) :=
    ⟨some (.inl SourceCSPPositiveCapEntry.start),
      ((), (((none, none), (((none, none), (none, false)), none)) : CapControl)),
      before⟩
  have hhalt : (((advance (SourceCSPPositiveCapEntry.program q))^[tc])
      localCfg).l = none := by
    simpa only [localCfg] using congrArg (fun c => c.l) hrc
  obtain ⟨t, ht, hr⟩ := outputs
    (SourceCSPHeaderRowBridge.headerEmbedding (q := q))
    (initial before) id id id (fun _ => rfl) none
    (SourceCSPPositiveCapEntry.program q) (capProgram (q := q))
    (fun _ => rfl) localCfg tc hhalt
  have hstart : cfg
      (SourceCSPHeaderRowBridge.headerEmbedding (q := q))
      (initial before) id id none localCfg =
      (⟨some (.inl SourceCSPPositiveCapEntry.start),
        ((), (((none, none), (((none, none), (none, false)), none)) : CapControl)),
        initial before⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (BitMachineRawSequence.Label Unit (CapLabel q))
          (Unit × CapControl)) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    rfl
  rw [hrc, hstart] at hr
  let S := bank (SourceCSPHeaderRowBridge.headerEmbedding (q := q))
    (initial before) Sc
  refine ⟨t, vc, S, ht.trans htc, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [S, cfg, stackCfg, BitMachineInline.cfg,
      id_eq, Option.map_none] using hr
  · change bank (SourceCSPHeaderRowBridge.headerEmbedding (q := q))
      _ _ (SourceCSPHeaderRowBridge.headerEmbedding
        SourceCSPPositiveSuffix.rowSlot) = _
    rw [bank_at]
    exact hrow
  · change bank (SourceCSPHeaderRowBridge.headerEmbedding (q := q))
      _ _ (SourceCSPHeaderRowBridge.headerEmbedding (.inl (.inr 6))) = _
    rw [bank_at]
    exact hmc
  · change bank (SourceCSPHeaderRowBridge.headerEmbedding (q := q))
      _ _ (SourceCSPHeaderRowBridge.headerEmbedding (.inr 6)) = _
    rw [bank_at]
    exact hcap
  · intro k
    change bank (SourceCSPHeaderRowBridge.headerEmbedding (q := q))
      (initial before) Sc (.inr k) = []
    rw [bank_outside]
    · rfl
    · rintro ⟨j, hj⟩
      cases hj

abbrev CapEntryLabel (q : Nat) :=
  BitMachineRawSequence.Label Unit (CapLabel q)
abbrev CapEntryControl := Unit × CapControl

def program (q : Nat) :=
  BitMachineRawSequence.program (capProgram (q := q))
    (SourceCSPHeaderRowBridge.prepareProgram (q := q))
    (.inl (.inl (.inl (.inl .scan))) :
      SourceCSPHeaderRowBridge.Label5)
    (((), (((none, none), (((none, none), (none, false)), none)) : CapControl)) :
      CapEntryControl)
    SourceCSPHeaderRowBridge.prepareStart

/-- The real suffix, unary count, and computed vertex cap are physically
copied into the exact ready bank of the corrected row-loop controller. -/
theorem positive_row_ready (n m q : Nat)
    (before : SourceCSPBudgetFrame.Stack → List Bool)
    (hn : 0 < n) (hsize : n ≤ q * m)
    (hm : before (.inl (.inr 6)) = List.replicate m true)
    (hnword : before (.inl (.inl (.inl (.inl 0)))) = n.bits)
    (hstatus : before (.inr 0) = [])
    (htarget : before (.inr 1) = []) (hwork : before (.inr 2) = [])
    (hunused : ∀ k : Fin 7, 3 ≤ k.val → before (.inr k) = []) :
    ∃ t S,
      t ≤ 2 + q * (2 * m + 3) + 3 +
        (2 * n.bits.length + 2 + (2 * (q * m) + 2) + 1 +
          (q * m + 1) * (4 * n.bits.length + 5) + 3) + 1 +
        (2 * (before SourceCSPPositiveSuffix.rowSlot).length +
          4 * (n - 1) + 2 * m + 13) + 1 ∧
      ((advance (program q))^[t])
        (⟨some (.inl (.inl SourceCSPPositiveCapEntry.start)),
          (((), (((none, none), (((none, none), (none, false)), none)) :
            CapControl)), SourceCSPHeaderRowBridge.prepareStart),
          initial before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (BitMachineRawSequence.Label
              (CapEntryLabel q) SourceCSPHeaderRowBridge.Label5)
            (CapEntryControl × SourceCSPHeaderRowBridge.Control5)) =
        ⟨none, (((), (((none, none), (((none, none), (none, false)), none)) :
          CapControl)), SourceCSPHeaderRowBridge.prepareStart), S⟩ ∧
      (fun k => S (SourceCSPHeaderRowBridge.rowEmbedding k)) =
        SourceCSPHeaderRowBridge.ready
          (before SourceCSPPositiveSuffix.rowSlot)
          (List.replicate (n - 1) true)
          (List.replicate m true) := by
  obtain ⟨tc, vc, Sc, htc, hrc, hrow, hm', hcap, hblank⟩ :=
    framed_positive n m q before hn hsize hm hnword
      hstatus htarget hwork hunused
  obtain ⟨tp, htp, hrp⟩ := SourceCSPHeaderRowBridge.prepare_run Sc
    (before SourceCSPPositiveSuffix.rowSlot)
    (List.replicate (n - 1) true) (List.replicate m true)
    hrow hcap hm' hblank
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (capProgram (q := q))
    (SourceCSPHeaderRowBridge.prepareProgram (q := q))
    (.inl SourceCSPPositiveCapEntry.start : CapEntryLabel q)
    (.inl (.inl (.inl (.inl .scan))) :
      SourceCSPHeaderRowBridge.Label5)
    (((), (((none, none), (((none, none), (none, false)), none)) :
      CapControl)) : CapEntryControl)
    ((), ((none, none), vc))
    SourceCSPHeaderRowBridge.prepareStart
    SourceCSPHeaderRowBridge.prepareStart
    (initial before) Sc
    (SourceCSPHeaderRowBridge.prepared Sc
      (before SourceCSPPositiveSuffix.rowSlot)
      (List.replicate (n - 1) true)
      (List.replicate m true))
    tc tp hrc hrp
  refine ⟨t,
    SourceCSPHeaderRowBridge.prepared Sc
      (before SourceCSPPositiveSuffix.rowSlot)
      (List.replicate (n - 1) true)
      (List.replicate m true), ?_, ?_, ?_⟩
  · simp only [List.length_replicate] at htp
    omega
  · simpa only [program] using hr
  · exact SourceCSPHeaderRowBridge.prepared_ready Sc
      (before SourceCSPPositiveSuffix.rowSlot)
      (List.replicate (n - 1) true)
      (List.replicate m true) hblank

end EthInapproximability.CurrentPaper.SourceCSPPositiveRowEntry
