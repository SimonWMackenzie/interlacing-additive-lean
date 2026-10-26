import EthInapproximability.CurrentPaper.SourceCSPPositiveSuffix

/-!
# Positive-branch entry after guarded dispatch

The raw-input guard has already consumed its status bit, leaving the unary
constraint count in the original count cell.  The earlier budget controller
expects a leading success bit in that cell.  This one physical push restores
that local calling convention; no source or scratch stack is reconstructed.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPPositiveCapEntry

open Turing BitMachineEncoding

abbrev Stack := SourceCSPBudgetFrame.Stack
abbrev CapLabel (q : Nat) := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label Unit (SourceFixedUnaryBudget.Label q))
  SourceCSPVertexCap.Label
abbrev CapControl := (Option Bool × Option Bool) × SourceCSPVertexCap.Control

def prependProgram (_ : Unit) :
    TM2.Stmt (fun _ : Stack => Bool) Unit Unit :=
  .push (.inl (.inr 6)) (fun _ => true) .halt

def program (q : Nat) :=
  BitMachineRawSequence.program prependProgram
    (SourceCSPBudgetFrame.positiveCapProgram q)
    (.inl (.inl ()) : CapLabel q) ()
    (((none, none), (((none, none), (none, false)), none)) : CapControl)

def start : Unit := ()

/-- The post-dispatch unary count is adapted to the previously checked
positive-cap machine, with one extra transition and one raw-sequence handoff. -/
theorem positive_success (n m q : Nat) (before : Stack → List Bool)
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
      ((advance (program q))^[t])
        (⟨some (.inl start), ((),
          (((none, none), (((none, none), (none, false)), none)) : CapControl)),
          before⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label Unit (CapLabel q))
            (Unit × CapControl)) =
        ⟨none, ((), ((none, none), v)), S⟩ ∧
      S (.inr 6) = true :: List.replicate (n - 1) true ∧
      S (.inl (.inr 6)) = List.replicate m true := by
  let mid := Function.update before (.inl (.inr 6))
    (true :: List.replicate m true)
  have hprep : ((advance prependProgram)^[1])
      (⟨some (), (), before⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Unit Unit) =
      ⟨none, (), mid⟩ := by
    simp [advance, TM2.step, TM2.stepAux, prependProgram, mid, hm]
  have hcount : mid (.inl (.inr 6)) =
      true :: List.replicate m true := by simp [mid]
  have hnword' : mid (.inl (.inl (.inl (.inl 0)))) = n.bits := by
    simp [mid, hnword]
  have hstatus' : mid (.inr 0) = [] := by simp [mid, hstatus]
  have htarget' : mid (.inr 1) = [] := by simp [mid, htarget]
  have hwork' : mid (.inr 2) = [] := by simp [mid, hwork]
  have hunused' : ∀ k : Fin 7, 3 ≤ k.val → mid (.inr k) = [] := by
    intro k hk
    simp [mid, hunused k hk]
  obtain ⟨tc, vc, Sc, htc, hrc, hcap, hmc⟩ :=
    SourceCSPBudgetFrame.positive_cap_success n m q mid hn hsize
      hcount hnword' hstatus' htarget' hwork' hunused'
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    prependProgram (SourceCSPBudgetFrame.positiveCapProgram q)
    () (.inl (.inl ()) : CapLabel q)
    () ()
    (((none, none), (((none, none), (none, false)), none)) : CapControl)
    ((none, none), vc) before mid Sc 1 tc hprep hrc
  refine ⟨t, vc, Sc, ?_, ?_, hcap, hmc⟩
  · omega
  · simpa only [program, start] using hr

/-- The same entry machine terminates for every canonical vertex word and
bounded unary count. Its physical cap-status bit is true exactly for the
positive budget range; this statement does not assume the size promise. -/
theorem positive_total (n m q : Nat) (before : Stack → List Bool)
    (hm : before (.inl (.inr 6)) = List.replicate m true)
    (hnword : before (.inl (.inl (.inl (.inl 0)))) = n.bits)
    (hstatus : before (.inr 0) = [])
    (htarget : before (.inr 1) = []) (hwork : before (.inr 2) = [])
    (hunused : ∀ k : Fin 7, 3 ≤ k.val → before (.inr k) = []) :
    ∃ t v S,
      t ≤ 2 + q * (2 * m + 3) + 3 +
        (2 * n.bits.length + 2 + (2 * (q * m) + 2) + 1 +
          (q * m + 1) * (4 * n.bits.length + 5) + 3) + 1 ∧
      ((advance (program q))^[t])
        (⟨some (.inl start), ((),
          (((none, none), (((none, none), (none, false)), none)) : CapControl)),
          before⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label Unit (CapLabel q))
            (Unit × CapControl)) =
        ⟨none, ((), ((none, none), v)), S⟩ ∧
      (S (.inr 6)).head? = some (decide (0 < n ∧ n ≤ q * m)) ∧
      (0 < n ∧ n ≤ q * m →
        S (.inr 6) = true :: List.replicate (n - 1) true) ∧
      S (.inl (.inr 6)) = List.replicate m true := by
  let mid := Function.update before (.inl (.inr 6))
    (true :: List.replicate m true)
  have hprep : ((advance prependProgram)^[1])
      (⟨some (), (), before⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Unit Unit) =
      ⟨none, (), mid⟩ := by
    simp [advance, TM2.step, TM2.stepAux, prependProgram, mid, hm]
  have hcount : mid (.inl (.inr 6)) =
      true :: List.replicate m true := by simp [mid]
  have hnword' : mid (.inl (.inl (.inl (.inl 0)))) = n.bits := by
    simp [mid, hnword]
  have hstatus' : mid (.inr 0) = [] := by simp [mid, hstatus]
  have htarget' : mid (.inr 1) = [] := by simp [mid, htarget]
  have hwork' : mid (.inr 2) = [] := by simp [mid, hwork]
  have hunused' : ∀ k : Fin 7, 3 ≤ k.val → mid (.inr k) = [] := by
    intro k hk
    simp [mid, hunused k hk]
  obtain ⟨tb, Sb, htb, hrb, _, hbudget, hsource, hnpres, hpres⟩ :=
    SourceCSPBudgetFrame.budget_success q m mid hcount
      hstatus' htarget' hwork'
  have hready : SourceCSPBudgetFrame.VertexReady Sb n
      (List.replicate (q * m) true) := by
    refine ⟨hnpres.trans hnword', hbudget, ?_, ?_, ?_, ?_⟩
    · rw [hpres 3 (by decide)]; exact hunused' 3 (by decide)
    · rw [hpres 4 (by decide)]; exact hunused' 4 (by decide)
    · rw [hpres 5 (by decide)]; exact hunused' 5 (by decide)
    · rw [hpres 6 (by decide)]; exact hunused' 6 (by decide)
  obtain ⟨tv, vv, Sv, htv, hrv, hhead, hsuccess, _, hmPres⟩ :=
    SourceCSPBudgetFrame.vertex_framed n
      (List.replicate (q * m) true) Sb hready
  obtain ⟨tc, htc, hrc⟩ := BitMachineRawSequence.runs
    (SourceCSPBudgetFrame.budgetProgram q)
    SourceCSPBudgetFrame.vertexProgram
    (.inl () : BitMachineRawSequence.Label Unit
      (SourceFixedUnaryBudget.Label q))
    (.check (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)) :
      SourceCSPVertexCap.Label)
    ((none, none) : Option Bool × Option Bool) (none, none)
    ((((none, none), (none, false)), none) : SourceCSPVertexCap.Control) vv
    mid Sb Sv tb tv hrb hrv
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    prependProgram (SourceCSPBudgetFrame.positiveCapProgram q)
    () (.inl (.inl ()) : CapLabel q)
    () ()
    (((none, none), (((none, none), (none, false)), none)) : CapControl)
    ((none, none), vv) before mid Sv 1 tc hprep
    (by simpa only [SourceCSPBudgetFrame.positiveCapProgram] using hrc)
  refine ⟨t, vv, Sv, ?_, ?_, ?_, ?_, hmPres.trans hsource⟩
  · simp only [List.length_replicate] at htv
    omega
  · simpa only [program, start] using hr
  · simpa only [List.length_replicate] using hhead
  · intro hv
    apply hsuccess
    simpa only [List.length_replicate] using hv

/-- On successful positive-cap inputs, the unread row suffix is retained
literally, so the row-loop preparation copies real parsed source bits. -/
theorem positive_success_row (n m q : Nat) (before : Stack → List Bool)
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
      ((advance (program q))^[t])
        (⟨some (.inl start), ((),
          (((none, none), (((none, none), (none, false)), none)) : CapControl)),
          before⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label Unit (CapLabel q))
            (Unit × CapControl)) =
        ⟨none, ((), ((none, none), v)), S⟩ ∧
      S (.inr 6) = true :: List.replicate (n - 1) true ∧
      S (.inl (.inr 6)) = List.replicate m true ∧
      S SourceCSPPositiveSuffix.rowSlot =
        before SourceCSPPositiveSuffix.rowSlot := by
  let mid := Function.update before (.inl (.inr 6))
    (true :: List.replicate m true)
  have hprep : ((advance prependProgram)^[1])
      (⟨some (), (), before⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Unit Unit) =
      ⟨none, (), mid⟩ := by
    simp [advance, TM2.step, TM2.stepAux, prependProgram, mid, hm]
  have hcount : mid (.inl (.inr 6)) =
      true :: List.replicate m true := by simp [mid]
  have hnword' : mid (.inl (.inl (.inl (.inl 0)))) = n.bits := by
    simp [mid, hnword]
  have hstatus' : mid (.inr 0) = [] := by simp [mid, hstatus]
  have htarget' : mid (.inr 1) = [] := by simp [mid, htarget]
  have hwork' : mid (.inr 2) = [] := by simp [mid, hwork]
  have hunused' : ∀ k : Fin 7, 3 ≤ k.val → mid (.inr k) = [] := by
    intro k hk
    simp [mid, hunused k hk]
  obtain ⟨tc, vc, Sc, htc, hrc, hcap, hmc, hrow⟩ :=
    SourceCSPPositiveSuffix.positive_cap_success_row n m q mid hn hsize
      hcount hnword' hstatus' htarget' hwork' hunused'
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    prependProgram (SourceCSPBudgetFrame.positiveCapProgram q)
    () (.inl (.inl ()) : CapLabel q)
    () ()
    (((none, none), (((none, none), (none, false)), none)) : CapControl)
    ((none, none), vc) before mid Sc 1 tc hprep hrc
  refine ⟨t, vc, Sc, ?_, ?_, hcap, hmc, ?_⟩
  · omega
  · simpa only [program, start] using hr
  · rw [hrow]
    simp [mid, SourceCSPPositiveSuffix.rowSlot]

end EthInapproximability.CurrentPaper.SourceCSPPositiveCapEntry
