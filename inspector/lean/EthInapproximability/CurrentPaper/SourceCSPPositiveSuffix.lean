import EthInapproximability.CurrentPaper.SourceCSPPositiveHeader
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-!
# Preserved row suffix after the positive-header program

The guarded header and budget/cap subroutines have disjoint stack support
from the unread CSP rows. This companion exposes the physical preservation
needed to attach the reusable row controller.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPPositiveSuffix

open Turing BitMachineEncoding BitMachineStackEmbedding

private theorem embedded_outside {K J L V : Type*}
    [DecidableEq K] [DecidableEq J]
    (ι : K ↪ J) (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (l : L) (v : V) (before : J → List Bool) (t : Nat) (j : J)
    (hj : ¬ ∃ k, ι k = j) :
    (((advance (fun l => stmt ι id id id none (P l)))^[t])
      (⟨some l, v, before⟩ : TM2.Cfg (fun _ : J => Bool) L V)).stk j = before j := by
  let localCfg : TM2.Cfg (fun _ : K => Bool) L V :=
    ⟨some l, v, fun k => before (ι k)⟩
  have hstart : stackCfg ι before localCfg =
      (⟨some l, v, before⟩ : TM2.Cfg (fun _ : J => Bool) L V) := by
    simp only [stackCfg, localCfg, bank_restrict]
  rw [← hstart]
  change (((advance (fun l => stackStmt ι
      (BitMachineInline.stmt id id id none (P l))))^[t])
      (stackCfg ι before localCfg)).stk j = before j
  rw [BitMachineStackRun.run]
  exact bank_outside ι before _ j hj

abbrev rowSlot : SourceCSPBudgetFrame.Stack := .inl (.inl (.inl (.inr 0)))

theorem budget_success_row (q m : Nat)
    (before : SourceCSPBudgetFrame.Stack → List Bool)
    (hword : before (.inl (.inr 6)) = true :: List.replicate m true)
    (hstatus : before (.inr 0) = [])
    (htarget : before (.inr 1) = []) (hwork : before (.inr 2) = []) :
    ∃ t S, t ≤ q * (2 * m + 3) + 3 ∧
      ((advance (SourceCSPBudgetFrame.budgetProgram q))^[t])
        (⟨some (.inl ()), (none, none), before⟩ :
          TM2.Cfg (fun _ : SourceCSPBudgetFrame.Stack => Bool)
            (BitMachineRawSequence.Label Unit (SourceFixedUnaryBudget.Label q))
            (Option Bool × Option Bool)) =
        ⟨none, (none, none), S⟩ ∧
      S (.inr 1) = List.replicate (q * m) true ∧
      S (.inl (.inr 6)) = List.replicate m true ∧
      S (.inl (.inl (.inl (.inl 0)))) =
        before (.inl (.inl (.inl (.inl 0)))) ∧
      (∀ k : Fin 7, 3 ≤ k.val → S (.inr k) = before (.inr k)) ∧
      S rowSlot = before rowSlot := by
  let mid := SourceCSPBudgetFrame.afterPeel m before
  have hpeel : ((advance SourceCSPBudgetFrame.peelProgram)^[1])
      (⟨some (), none, before⟩ :
        TM2.Cfg (fun _ : SourceCSPBudgetFrame.Stack => Bool) Unit (Option Bool)) =
      ⟨none, some true, mid⟩ :=
    SourceCSPBudgetFrame.peel_success m before hword hstatus
  have hsource : mid (.inl (.inr 6)) = List.replicate m true := by
    simp [mid, SourceCSPBudgetFrame.afterPeel]
  have htarget' : mid (.inr 1) = [] := by
    simp [mid, SourceCSPBudgetFrame.afterPeel, htarget]
  have hwork' : mid (.inr 2) = [] := by
    simp [mid, SourceCSPBudgetFrame.afterPeel, hwork]
  obtain ⟨tm, Sm, htm, hrm, hbudget, hsource', _, hvertex, hpres⟩ :=
    SourceCSPBudgetFrame.multiplier_framed q m mid hsource htarget' hwork'
  have hrowm : Sm rowSlot = mid rowSlot := by
    have h := embedded_outside SourceCSPBudgetFrame.multiplierEmbedding
      (SourceFixedUnaryBudget.program (q := q)) (.start 0) none mid tm
      rowSlot (by
        rintro ⟨k, hk⟩
        fin_cases k <;> simp [SourceCSPBudgetFrame.multiplierEmbedding, rowSlot] at hk)
    change (((advance (SourceCSPBudgetFrame.multiplierProgram q))^[tm])
      (⟨some (.start 0), none, mid⟩ :
        TM2.Cfg (fun _ : SourceCSPBudgetFrame.Stack => Bool)
          (SourceFixedUnaryBudget.Label q) (Option Bool))).stk rowSlot =
        mid rowSlot at h
    rw [hrm] at h
    exact h
  have hrowmid : mid rowSlot = before rowSlot := by
    simp [mid, SourceCSPBudgetFrame.afterPeel, rowSlot]
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    SourceCSPBudgetFrame.peelProgram
    (SourceCSPBudgetFrame.multiplierProgram q) ()
    (.start 0 : SourceFixedUnaryBudget.Label q)
    (none : Option Bool) (some true) (none : Option Bool) none
    before mid Sm 1 tm hpeel hrm
  refine ⟨t, Sm, by omega, ?_, ?_, hsource', ?_, ?_, hrowm.trans hrowmid⟩
  · simpa only [SourceCSPBudgetFrame.budgetProgram] using hr
  · exact hbudget
  · simpa [mid, SourceCSPBudgetFrame.afterPeel] using hvertex
  · intro k hk
    rw [hpres k hk]
    have hne : k ≠ (0 : Fin 7) := by omega
    simp [mid, SourceCSPBudgetFrame.afterPeel, hne]

theorem positive_cap_success_row (n m q : Nat)
    (before : SourceCSPBudgetFrame.Stack → List Bool)
    (hn : 0 < n) (hsize : n ≤ q * m)
    (hword : before (.inl (.inr 6)) = true :: List.replicate m true)
    (hnword : before (.inl (.inl (.inl (.inl 0)))) = n.bits)
    (hstatus : before (.inr 0) = [])
    (htarget : before (.inr 1) = []) (hwork : before (.inr 2) = [])
    (hunused : ∀ k : Fin 7, 3 ≤ k.val → before (.inr k) = []) :
    ∃ t v S, t ≤ q * (2 * m + 3) + 3 +
        (2 * n.bits.length + 2 + (2 * (q * m) + 2) + 1 +
          (q * m + 1) * (4 * n.bits.length + 5) + 3) + 1 ∧
      ((advance (SourceCSPBudgetFrame.positiveCapProgram q))^[t])
        (⟨some (.inl (.inl ())),
          ((none, none), (((none, none), (none, false)), none)), before⟩ :
          TM2.Cfg (fun _ : SourceCSPBudgetFrame.Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label Unit (SourceFixedUnaryBudget.Label q))
              SourceCSPVertexCap.Label)
            ((Option Bool × Option Bool) × SourceCSPVertexCap.Control)) =
        ⟨none, ((none, none), v), S⟩ ∧
      S (.inr 6) = true :: List.replicate (n - 1) true ∧
      S (.inl (.inr 6)) = List.replicate m true ∧
      S rowSlot = before rowSlot := by
  obtain ⟨tb, Sb, htb, hrb, hbudget, hm, hnpres, hpres, hrowb⟩ :=
    budget_success_row q m before hword hstatus htarget hwork
  have hready : SourceCSPBudgetFrame.VertexReady Sb n
      (List.replicate (q * m) true) := by
    refine ⟨hnpres.trans hnword, hbudget, ?_, ?_, ?_, ?_⟩
    · rw [hpres 3 (by decide)]; exact hunused 3 (by decide)
    · rw [hpres 4 (by decide)]; exact hunused 4 (by decide)
    · rw [hpres 5 (by decide)]; exact hunused 5 (by decide)
    · rw [hpres 6 (by decide)]; exact hunused 6 (by decide)
  obtain ⟨tv, vv, Sv, htv, hrv, _, hsuccess, _, hmPres⟩ :=
    SourceCSPBudgetFrame.vertex_framed n
      (List.replicate (q * m) true) Sb hready
  have hrowv : Sv rowSlot = Sb rowSlot := by
    have h := embedded_outside SourceCSPBudgetFrame.vertexEmbedding
      SourceCSPVertexCap.program
      (.check (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
      (((none, none), (none, false)), none) Sb tv rowSlot (by
        rintro ⟨k, hk⟩
        fin_cases k <;> simp [SourceCSPBudgetFrame.vertexEmbedding, rowSlot] at hk)
    change (((advance SourceCSPBudgetFrame.vertexProgram)^[tv])
      (⟨some (.check (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        (((none, none), (none, false)), none), Sb⟩ :
        TM2.Cfg (fun _ : SourceCSPBudgetFrame.Stack => Bool)
          SourceCSPVertexCap.Label SourceCSPVertexCap.Control)).stk rowSlot =
      Sb rowSlot at h
    rw [hrv] at h
    exact h
  have hpositive : 0 < n ∧ n ≤ (List.replicate (q * m) true).length := by
    simpa only [List.length_replicate] using And.intro hn hsize
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourceCSPBudgetFrame.budgetProgram q)
    SourceCSPBudgetFrame.vertexProgram
    (.inl () : BitMachineRawSequence.Label Unit (SourceFixedUnaryBudget.Label q))
    (.check (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    ((none, none) : Option Bool × Option Bool) (none, none)
    ((((none, none), (none, false)), none) : SourceCSPVertexCap.Control) vv
    before Sb Sv tb tv hrb hrv
  refine ⟨t, vv, Sv, ?_, ?_, hsuccess hpositive, hmPres.trans hm,
    hrowv.trans hrowb⟩
  · simp only [List.length_replicate] at htv
    omega
  · simpa only [SourceCSPBudgetFrame.positiveCapProgram] using hr

/-- The encoded positive-header run retains the unread canonical row stream
on the very same physical stack while preparing unary `m` and `n-1`. -/
theorem encoded_positive_row_suffix {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (hn : 0 < P.vertices) (hsize : SourceCSPCodec.ValidSize P) :
    ∃ t v S,
      t ≤ SourceCSPPositiveHeader.positiveBound a q
        (EncodedETHSource.constraintBits P).length
        P.constraints.bits.length P.vertices P.constraints ∧
      ((advance (SourceCSPPositiveHeader.fullHeaderProgram a q))^[t])
        (⟨some (.inl (.inl (.inl (.inl BitMachineCopy.Label.scan)))),
          (((((none, none), (((none, none), none), none)),
            ((none, none), (none, false)))),
            ((none, none), (((none, none), (none, false)), none))),
          SourceCSPPositiveHeader.initial (EncodedETHSource.constraintBits P)⟩ :
          TM2.Cfg (fun _ : SourceCSPPositiveHeader.Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label
                (SourceCSPConstraintGuard.HeaderLabel a q)
                SourceCSPQueryRange.Label)
              (BitMachineRawSequence.Label
                (BitMachineRawSequence.Label Unit (SourceFixedUnaryBudget.Label q))
                SourceCSPVertexCap.Label))
            ((SourceCSPConstraintGuard.HeaderControl × SourceCSPQueryRange.Control) ×
              ((Option Bool × Option Bool) × SourceCSPVertexCap.Control))) =
        ⟨none,
          ((((none, none), (((none, none), none), none)),
            ((none, none), (none, false))), ((none, none), v)), S⟩ ∧
      S (.inr 6) = true :: List.replicate (P.vertices - 1) true ∧
      S (.inl (.inr 6)) = List.replicate P.constraints true ∧
      S rowSlot = SourceCSPPositiveHeader.rows P := by
  let input := EncodedETHSource.constraintBits P
  obtain ⟨th, vh, Sh, hth, hrh, hnword, hmword, hrows, hextras⟩ :=
    SourceCSPPositiveHeader.framed_encoded_guard P
  have hready : ∀ k : Fin 7, 3 ≤ k.val → Sh (.inr k) = [] := by
    intro k _
    exact hextras k
  obtain ⟨tp, vp, Sp, htp, hrp, hcap, hm, hrow⟩ :=
    positive_cap_success_row P.vertices P.constraints q Sh hn hsize
      hmword hnword (hextras 0) (hextras 1) (hextras 2) hready
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourceCSPPositiveHeader.headerProgram a q)
    (SourceCSPBudgetFrame.positiveCapProgram q)
    (.inl (.inl (.inl BitMachineCopy.Label.scan)) :
      BitMachineRawSequence.Label (SourceCSPConstraintGuard.HeaderLabel a q)
        SourceCSPQueryRange.Label)
    (.inl (.inl ()) : BitMachineRawSequence.Label
      (BitMachineRawSequence.Label Unit (SourceFixedUnaryBudget.Label q))
      SourceCSPVertexCap.Label)
    (((none, none), (((none, none), none), none)),
      ((none, none), (none, false))) vh
    ((none, none), (((none, none), (none, false)), none))
    ((none, none), vp)
    (SourceCSPPositiveHeader.initial input) Sh Sp th tp hrh hrp
  refine ⟨t, vp, Sp, ?_, ?_, hcap, hm, hrow.trans hrows⟩
  · change t ≤ SourceCSPPositiveHeader.positiveBound a q input.length
      P.constraints.bits.length P.vertices P.constraints
    dsimp only [input]
    unfold SourceCSPPositiveHeader.positiveBound
    omega
  · simpa only [SourceCSPPositiveHeader.fullHeaderProgram, input] using hr

end EthInapproximability.CurrentPaper.SourceCSPPositiveSuffix
