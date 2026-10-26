import EthInapproximability.CurrentPaper.SourceCSPConstraintGuard
import EthInapproximability.CurrentPaper.SourceFixedUnaryBudget
import EthInapproximability.CurrentPaper.SourceCSPVertexCap

/-!
# Shared stacks for the guarded constraint count and vertex budget

The preceding m-guard leaves `[status] ++ unary m` on its output stack. A
literal pop records the status separately, after which the fixed-q
multiplier constructs the `q*m` budget. The positive-vertex cap checker will
use the same bank; zero vertices are a separate branch.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPBudgetFrame

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceCSPInputFrame.Stack ⊕ Fin 7

def inputEmbedding : SourceCSPInputFrame.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := by intro x y h; exact Sum.inl.inj h

def multiplierEmbedding : Fin 3 ↪ Stack where
  toFun k := if k = 0 then .inl (.inr 6)
    else if k = 1 then .inr 1 else .inr 2
  inj' := by intro x y h; fin_cases x <;> fin_cases y <;> simp_all

def vertexEmbedding : Fin 6 ↪ Stack where
  toFun k := if k = 0 then .inl (.inl (.inl (.inl 0)))
    else if k = 1 then .inr 1 else if k = 2 then .inr 3
    else if k = 3 then .inr 4 else if k = 4 then .inr 5 else .inr 6
  inj' := by intro x y h; fin_cases x <;> fin_cases y <;> simp_all

def peelProgram (_ : Unit) : TM2.Stmt (fun _ : Stack => Bool) Unit (Option Bool) :=
  .pop (.inl (.inr 6)) (fun _ b => b)
    (.push (.inr 0) (fun b => b.getD false) .halt)

theorem peel_success (m : Nat) (before : Stack → List Bool)
    (hword : before (.inl (.inr 6)) = true :: List.replicate m true)
    (hstatus : before (.inr 0) = []) :
    advance peelProgram (⟨some (), none, before⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Unit (Option Bool)) =
      ⟨none, some true,
        Function.update (Function.update before (.inl (.inr 6))
          (List.replicate m true)) (.inr 0) [true]⟩ := by
  simp [advance, TM2.step, TM2.stepAux, peelProgram, hword, hstatus]

def multiplierProgram (q : Nat) (l : SourceFixedUnaryBudget.Label q) :=
  stmt multiplierEmbedding id id id none (SourceFixedUnaryBudget.program l)

theorem multiplier_framed (q m : Nat) (before : Stack → List Bool)
    (hsource : before (.inl (.inr 6)) = List.replicate m true)
    (htarget : before (.inr 1) = []) (hwork : before (.inr 2) = []) :
    ∃ t S, t ≤ q * (2 * m + 3) + 1 ∧
      ((advance (multiplierProgram q))^[t])
        (⟨some (.start 0), none, before⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (SourceFixedUnaryBudget.Label q) (Option Bool)) =
        ⟨none, none, S⟩ ∧
      S (.inr 1) = List.replicate (q * m) true ∧
      S (.inl (.inr 6)) = List.replicate m true ∧
      S (.inr 0) = before (.inr 0) ∧
      S (.inl (.inl (.inl (.inl 0)))) =
        before (.inl (.inl (.inl (.inl 0)))) ∧
      (∀ k : Fin 7, 3 ≤ k.val → S (.inr k) = before (.inr k)) := by
  obtain ⟨t, ht, hr⟩ := SourceFixedUnaryBudget.multiply q m
  let localCfg : SourceFixedUnaryBudget.Config q :=
    ⟨some (.start 0), none,
      SourceFixedUnaryBudget.contents (List.replicate m true) []⟩
  have hhalt : (((advance (SourceFixedUnaryBudget.program (q := q)))^[t])
      localCfg).l = none := by
    simpa only [localCfg, SourceFixedUnaryBudget.run] using
      congrArg (fun c => c.l) hr
  obtain ⟨u, hu, hrun⟩ := outputs multiplierEmbedding before id id id
    (fun _ => rfl) none (SourceFixedUnaryBudget.program (q := q))
    (multiplierProgram q) (fun _ => rfl) localCfg t hhalt
  have hstart : cfg multiplierEmbedding before id id none localCfg =
      (⟨some (.start 0), none, before⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          (SourceFixedUnaryBudget.Label q) (Option Bool)) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k
    · exact hsource.symm
    · exact htarget.symm
    · exact hwork.symm
  change ((advance (SourceFixedUnaryBudget.program (q := q)))^[t]) localCfg = _ at hr
  rw [hr, hstart] at hrun
  refine ⟨u, bank multiplierEmbedding before
    (SourceFixedUnaryBudget.contents (List.replicate m true)
      (List.replicate (q * m) true)), hu.trans ht,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [cfg, stackCfg, BitMachineInline.cfg,
      id_eq, Option.map_none] using hrun
  · change bank multiplierEmbedding before _ (multiplierEmbedding 1) = _
    rw [bank_at]
    rfl
  · change bank multiplierEmbedding before _ (multiplierEmbedding 0) = _
    rw [bank_at]
    rfl
  · apply bank_outside
    rintro ⟨k, hk⟩
    fin_cases k <;> simp [multiplierEmbedding] at hk
  · apply bank_outside
    rintro ⟨k, hk⟩
    fin_cases k <;> simp [multiplierEmbedding] at hk
  · intro k hk
    apply bank_outside
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [multiplierEmbedding] at hj <;> omega

def afterPeel (m : Nat) (before : Stack → List Bool) : Stack → List Bool :=
  Function.update (Function.update before (.inl (.inr 6))
    (List.replicate m true)) (.inr 0) [true]

def budgetProgram (q : Nat) :=
  BitMachineRawSequence.program peelProgram (multiplierProgram q)
    (.start 0 : SourceFixedUnaryBudget.Label q)
    (none : Option Bool) (none : Option Bool)

theorem budget_success (q m : Nat) (before : Stack → List Bool)
    (hword : before (.inl (.inr 6)) = true :: List.replicate m true)
    (hstatus : before (.inr 0) = [])
    (htarget : before (.inr 1) = []) (hwork : before (.inr 2) = []) :
    ∃ t S, t ≤ q * (2 * m + 3) + 3 ∧
      ((advance (budgetProgram q))^[t])
        (⟨some (.inl ()), (none, none), before⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label Unit (SourceFixedUnaryBudget.Label q))
            (Option Bool × Option Bool)) =
        ⟨none, (none, none), S⟩ ∧
      S (.inr 0) = [true] ∧
      S (.inr 1) = List.replicate (q * m) true ∧
      S (.inl (.inr 6)) = List.replicate m true ∧
      S (.inl (.inl (.inl (.inl 0)))) =
        before (.inl (.inl (.inl (.inl 0)))) ∧
      (∀ k : Fin 7, 3 ≤ k.val → S (.inr k) = before (.inr k)) := by
  let mid := afterPeel m before
  have hpeel : ((advance peelProgram)^[1])
      (⟨some (), none, before⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Unit (Option Bool)) =
      ⟨none, some true, mid⟩ := by
    exact peel_success m before hword hstatus
  have hsource : mid (.inl (.inr 6)) = List.replicate m true := by
    simp [mid, afterPeel]
  have htarget' : mid (.inr 1) = [] := by
    simp [mid, afterPeel, htarget]
  have hwork' : mid (.inr 2) = [] := by
    simp [mid, afterPeel, hwork]
  obtain ⟨tm, Sm, htm, hrm, hbudget, hsource', hstatus', hn, hunused⟩ :=
    multiplier_framed q m mid hsource htarget' hwork'
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    peelProgram (multiplierProgram q) ()
    (.start 0 : SourceFixedUnaryBudget.Label q)
    (none : Option Bool) (some true) (none : Option Bool) none
    before mid Sm 1 tm hpeel hrm
  refine ⟨t, Sm, ?_, hr, ?_, hbudget, hsource', ?_, ?_⟩
  · omega
  · simpa [mid, afterPeel] using hstatus'
  · simpa [mid, afterPeel] using hn
  · intro k hk
    rw [hunused k hk]
    have hne : k ≠ (0 : Fin 7) := by omega
    simp [mid, afterPeel, hne]

def vertexProgram (l : SourceCSPVertexCap.Label) :=
  stmt vertexEmbedding id id id none (SourceCSPVertexCap.program l)

def VertexReady (S : Stack → List Bool) (n : Nat) (budget : List Bool) : Prop :=
  S (.inl (.inl (.inl (.inl 0)))) = n.bits ∧
    S (.inr 1) = budget ∧
    S (.inr 3) = [] ∧ S (.inr 4) = [] ∧
    S (.inr 5) = [] ∧ S (.inr 6) = []

theorem vertex_framed (n : Nat) (budget : List Bool)
    (before : Stack → List Bool) (hready : VertexReady before n budget) :
    ∃ t v S, t ≤ 2 * n.bits.length + 2 + (2 * budget.length + 2) + 1 +
          (budget.length + 1) * (4 * n.bits.length + 5) + 3 ∧
      ((advance vertexProgram)^[t])
        (⟨some (.check (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
          (((none, none), (none, false)), none), before⟩ :
          TM2.Cfg (fun _ : Stack => Bool) SourceCSPVertexCap.Label
            SourceCSPVertexCap.Control) = ⟨none, v, S⟩ ∧
      (S (.inr 6)).head? = some (decide (0 < n ∧ n ≤ budget.length)) ∧
      (0 < n ∧ n ≤ budget.length →
        S (.inr 6) = true :: List.replicate (n - 1) true) ∧
      S (.inr 0) = before (.inr 0) ∧
      S (.inl (.inr 6)) = before (.inl (.inr 6)) := by
  obtain ⟨t, c, ht, hr, hh, hhead, hsuccess⟩ :=
    SourceCSPVertexCap.guard_total n budget
  let localCfg : SourceCSPVertexCap.Config :=
    ⟨some (.check (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
      (((none, none), (none, false)), none),
      SourceCSPQueryRange.contents n.bits budget [] [] [] []⟩
  have hhalt : (((advance SourceCSPVertexCap.program)^[t]) localCfg).l = none := by
    simpa only [localCfg, SourceCSPVertexCap.run, hh] using
      congrArg (fun c => c.l) hr
  obtain ⟨u, hu, hrun⟩ := outputs vertexEmbedding before id id id
    (fun _ => rfl) none SourceCSPVertexCap.program vertexProgram
    (fun _ => rfl) localCfg t hhalt
  have hstart : cfg vertexEmbedding before id id none localCfg =
      (⟨some (.check (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        (((none, none), (none, false)), none), before⟩ :
        TM2.Cfg (fun _ : Stack => Bool) SourceCSPVertexCap.Label
          SourceCSPVertexCap.Control) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k
    · exact hready.1.symm
    · exact hready.2.1.symm
    · exact hready.2.2.1.symm
    · exact hready.2.2.2.1.symm
    · exact hready.2.2.2.2.1.symm
    · exact hready.2.2.2.2.2.symm
  change ((advance SourceCSPVertexCap.program)^[t]) localCfg = _ at hr
  rw [hr, hstart] at hrun
  let S := bank vertexEmbedding before c.stk
  refine ⟨u, c.var, S, hu.trans ht, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [S, cfg, stackCfg, BitMachineInline.cfg,
      id_eq, hh, Option.map_none] using hrun
  · change (bank vertexEmbedding before c.stk (vertexEmbedding 5)).head? = _
    rw [bank_at]
    exact hhead
  · intro hv
    change bank vertexEmbedding before c.stk (vertexEmbedding 5) = _
    rw [bank_at]
    exact hsuccess hv
  · apply bank_outside
    rintro ⟨k, hk⟩
    fin_cases k <;> simp [vertexEmbedding] at hk
  · apply bank_outside
    rintro ⟨k, hk⟩
    fin_cases k <;> simp [vertexEmbedding] at hk

def positiveCapProgram (q : Nat) :=
  BitMachineRawSequence.program (budgetProgram q) vertexProgram
    (.check (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    ((none, none) : Option Bool × Option Bool)
    ((((none, none), (none, false)), none) : SourceCSPVertexCap.Control)

theorem positive_cap_success (n m q : Nat) (before : Stack → List Bool)
    (hn : 0 < n) (hsize : n ≤ q * m)
    (hword : before (.inl (.inr 6)) = true :: List.replicate m true)
    (hnword : before (.inl (.inl (.inl (.inl 0)))) = n.bits)
    (hstatus : before (.inr 0) = [])
    (htarget : before (.inr 1) = []) (hwork : before (.inr 2) = [])
    (hunused : ∀ k : Fin 7, 3 ≤ k.val → before (.inr k) = []) :
    ∃ t v S, t ≤ q * (2 * m + 3) + 3 +
        (2 * n.bits.length + 2 + (2 * (q * m) + 2) + 1 +
          (q * m + 1) * (4 * n.bits.length + 5) + 3) + 1 ∧
      ((advance (positiveCapProgram q))^[t])
        (⟨some (.inl (.inl ())),
          ((none, none), (((none, none), (none, false)), none)), before⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label Unit (SourceFixedUnaryBudget.Label q))
              SourceCSPVertexCap.Label)
            ((Option Bool × Option Bool) × SourceCSPVertexCap.Control)) =
        ⟨none, ((none, none), v), S⟩ ∧
      S (.inr 6) = true :: List.replicate (n - 1) true ∧
      S (.inl (.inr 6)) = List.replicate m true := by
  obtain ⟨tb, Sb, htb, hrb, _, hbudget, hm, hnpres, hpres⟩ :=
    budget_success q m before hword hstatus htarget hwork
  have hready : VertexReady Sb n (List.replicate (q * m) true) := by
    refine ⟨hnpres.trans hnword, hbudget, ?_, ?_, ?_, ?_⟩
    · rw [hpres 3 (by decide)]; exact hunused 3 (by decide)
    · rw [hpres 4 (by decide)]; exact hunused 4 (by decide)
    · rw [hpres 5 (by decide)]; exact hunused 5 (by decide)
    · rw [hpres 6 (by decide)]; exact hunused 6 (by decide)
  obtain ⟨tv, vv, Sv, htv, hrv, _, hsuccess, _, hmPres⟩ :=
    vertex_framed n (List.replicate (q * m) true) Sb hready
  have hpositive : 0 < n ∧ n ≤ (List.replicate (q * m) true).length := by
    simpa only [List.length_replicate] using And.intro hn hsize
  have hcap := hsuccess hpositive
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (budgetProgram q) vertexProgram
    (.inl () : BitMachineRawSequence.Label Unit (SourceFixedUnaryBudget.Label q))
    (.check (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)) :
      SourceCSPVertexCap.Label)
    ((none, none) : Option Bool × Option Bool) (none, none)
    ((((none, none), (none, false)), none) : SourceCSPVertexCap.Control) vv
    before Sb Sv tb tv hrb hrv
  refine ⟨t, vv, Sv, ?_, ?_, hcap, hmPres.trans hm⟩
  · simp only [List.length_replicate] at htv
    omega
  · simpa only [positiveCapProgram] using hr

end EthInapproximability.CurrentPaper.SourceCSPBudgetFrame
