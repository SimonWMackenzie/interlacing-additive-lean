import Paper2.ThrJoin
import Paper2.MIdent

/-! Unit 3 (lock v12 App. D; T44/U10), lane a-success-table-12, segment (1): the threshold producer and the
sample-dimension producer joined as ONE fixed program.

Bank `JM = ThrProducer.TK ⊕ (MProducer.MK ⊕ Fin 1)` (the admitted threshold-producer bank, the admitted
sample-dimension-producer bank, one copy scratch). ONE fixed program `tmProg` = four parts joined by three
production `BitMachineRawSequence` handoffs:

1. admitted `copyProgram`: unary `k` from the producer counter cell `ThrProducer.ctrC` appended to the blank
   `MProducer` cell 1 (source kept, scratch blank before and after);
2. the admitted `ThrProducer.thrProg` lifted to the TK region (`stackStmt`), run charged by `ThrProducer.thr_run`;
3. admitted `copyProgram`: the produced threshold (`ThrProducer.thrC`) appended to the blank `MProducer` cell 0;
4. the admitted `MProducer.mProg` lifted to the MK region, run charged by `MProducer.m_run`.

Start bank `TM0 k v L`: the admitted threshold start bank `ThrProducer.T0 k v` on TK (unary k in the counter,
unary `v i` as the source of log region i), unary `L` in MK cell 2, everything else blank.
Nothing is inserted between the parts: the MK inputs `b` (= the threshold) and `k` are copied by charged programs.

`tm_run_sched`: at `v = ![LookupSeed.width L, width L, outerWidth L, restorationWidth L, coverWidth n m L Δ γ]`,
`L = clog₂ n`, the threshold is `sourceBudget L (restorationDepth L) (coverDepth n m L Δ γ) k` (admitted
`ThrJoin.budget_eq`) and the MK outputs are `mY = sourceCols …` (cell 10) and `mX = sourceRows …` (cell 13)
(admitted `MProducer.cols_eq`, `MProducer.rows_eq`). -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

namespace Paper2.TMFront

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

abbrev TK := ThrProducer.TK
abbrev MK := MProducer.MK
abbrev JM := TK ⊕ (MK ⊕ Fin 1)

def tc (x : TK) : JM := .inl x
def mc (x : MK) : JM := .inr (.inl x)
def sc : JM := .inr (.inr 0)

def ιT : TK ↪ JM := ⟨Sum.inl, fun _ _ h => Sum.inl_injective h⟩
def ιM : MK ↪ JM := ⟨fun x => .inr (.inl x), fun a b h => by simpa using h⟩

def e1 : Fin 3 ↪ JM := ⟨![tc ThrProducer.ctrC, mc 1, sc], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [tc, mc, sc]⟩
def e2 : Fin 3 ↪ JM := ⟨![tc ThrProducer.thrC, mc 0, sc], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [tc, mc, sc]⟩

def cp (e : Fin 3 ↪ JM) := MatrixStage4ScalarPreparationOps.copyProgram e
abbrev oc := (none : Option Bool)
def pT := fun l => stackStmt ιT (ThrProducer.thrProg l)
def pM := fun l => stackStmt ιM (MProducer.mProg l)

def f1 := BitMachineRawSequence.program (cp e1) pT ThrProducer.thrStart oc ThrProducer.thrCtl
def g1 := (oc, ThrProducer.thrCtl)
def f2 := BitMachineRawSequence.program f1 (cp e2) BitMachineCopy.Label.scan g1 oc
def g2 := (g1, oc)
/-- The threshold + sample-dimension producer: ONE fixed program (no machine constants). -/
def tmProg := BitMachineRawSequence.program f2 pM MProducer.mStart g2 MProducer.mCtl
def tmCtl := (g2, MProducer.mCtl)
def labelOfP {L σ : Type*} {K : Type*} (_P : L → TM2.Stmt (fun _ : K => Bool) L σ) (l : L) : L := l
def tmStart := labelOfP tmProg (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))

/-- Start bank: the admitted threshold start bank on TK, unary `L` in MK cell 2, everything else blank. -/
def TM0 (k : ℕ) (v : Fin 5 → ℕ) (L : ℕ) : JM → List Bool :=
  Sum.elim (ThrProducer.T0 k v)
    (Sum.elim (Function.update (fun _ => []) (2 : MK) (MProducer.u L)) (fun _ => []))

/-- The produced threshold value (the literal value of `ThrProducer.thr_run`). -/
def thrVal (k : ℕ) (v : Fin 5 → ℕ) : ℕ := k * ThrProducer.Xv v + (Nat.clog 2 (v 0) + 1)

/-- The exit facts of `ThrProducer.thr_run` (copied literally). -/
def TFacts (k : ℕ) (v : Fin 5 → ℕ) (F : TK → List Bool) : Prop :=
  F ThrProducer.thrC = ThrProducer.u (k * ThrProducer.Xv v + (Nat.clog 2 (v 0) + 1)) ∧
  F ThrProducer.xC = ThrProducer.u (ThrProducer.Xv v) ∧ F ThrProducer.ctrC = [] ∧
  F ThrProducer.scrC = [] ∧ (∀ i, F (ThrProducer.outI i) = ThrProducer.u (Nat.clog 2 (v i))) ∧
  (∀ i, F (ThrProducer.srcI i) = ThrProducer.u (v i))

/-- The exit facts of `MProducer.m_run` (copied literally). -/
def MFacts (b k L : ℕ) (F : MK → List Bool) : Prop :=
  F 0 = MProducer.u b ∧ F 1 = MProducer.u k ∧ F 2 = MProducer.u L ∧ F 3 = MProducer.u (b - 1) ∧
  F 4 = MProducer.u (2 ^ (b - 1)) ∧ F 5 = MProducer.u (k + b - 1) ∧
  F 6 = MProducer.u (2 ^ (k + b - 1)) ∧ F 7 = MProducer.u ((2 ^ (b - 1)) + 1) ∧
  F 8 = MProducer.u (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) ∧
  F 9 = MProducer.u (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) ∧
  F 10 = MProducer.u ((12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) +
    (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1)))) ∧ F 11 = [] ∧
  F 12 = MProducer.u ((L + (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) - 1) % L) ∧
  F 13 = MProducer.u ((L + (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) - 1) / L) ∧
  F 14 = [] ∧ F 15 = [] ∧ F 16 = [] ∧ F 17 = []

/-- The explicit clock of `tm_run`. -/
def tmBd (k : ℕ) (v : Fin 5 → ℕ) (L : ℕ) : ℕ :=
  (2 * k + 2) + ThrProducer.thrBd k v + (2 * thrVal k v + 2) + MProducer.mBd (thrVal k v) k L + 3

theorem tm_run (k : ℕ) (v : Fin 5 → ℕ) (L : ℕ) :
    ∃ t ≤ tmBd k v L, ∃ vc, ∃ FT : TK → List Bool, ∃ FM : MK → List Bool,
      ((advance tmProg)^[t]) (⟨some tmStart, tmCtl, TM0 k v L⟩ : TM2.Cfg (fun _ : JM => Bool) _ _) =
        ⟨none, vc, Sum.elim FT (Sum.elim FM (fun _ => []))⟩ ∧
      TFacts k v FT ∧ MFacts (thrVal k v) k L FM := by
  obtain ⟨b, hb⟩ : ∃ b, b = thrVal k v := ⟨_, rfl⟩
  -- (1) copy k into MK cell 1
  obtain ⟨S0, hS0⟩ : ∃ S, S = TM0 k v L := ⟨_, rfl⟩
  have h1 := MatrixStage4ScalarPreparationOps.copy_run e1 S0 (by rw [hS0]; rfl)
  have l1 : (S0 (e1 0)).length = k := by
    rw [hS0]; show (ThrProducer.T0 k v ThrProducer.ctrC).length = k
    simp [ThrProducer.T0, ThrProducer.ctrC, ThrProducer.u]
  rw [l1] at h1
  obtain ⟨B1, hB1⟩ : ∃ B, B = Function.update S0 (e1 1) (S0 (e1 0) ++ S0 (e1 1)) := ⟨_, rfl⟩
  rw [← hB1] at h1
  have b1_t : ∀ x, B1 (tc x) = ThrProducer.T0 k v x := fun x => by
    rw [hB1, Function.update_of_ne (by simp [e1, tc, mc]), hS0]; rfl
  have b1_m1 : B1 (mc 1) = MProducer.u k := by
    rw [hB1]; show Function.update S0 (e1 1) _ (e1 1) = _
    rw [Function.update_self, hS0]
    show ThrProducer.T0 k v ThrProducer.ctrC ++ [] = _
    simp [ThrProducer.T0, ThrProducer.ctrC, ThrProducer.u, MProducer.u]
  have b1_m : ∀ x : MK, x ≠ 1 → B1 (mc x) = S0 (mc x) := fun x hx => by
    rw [hB1, Function.update_of_ne (by simpa [e1, mc] using hx)]
  have b1_s : B1 sc = [] := by
    rw [hB1, Function.update_of_ne (by simp [e1, sc, mc]), hS0]; rfl
  -- (2) the threshold producer on TK
  obtain ⟨t2, ht2, vc2, FT, hrun2, hT⟩ := ThrProducer.thr_run k v
  have hA := BitMachineStackRun.run ιT B1 ThrProducer.thrProg
    (⟨some ThrProducer.thrStart, ThrProducer.thrCtl, ThrProducer.T0 k v⟩ : TM2.Cfg (fun _ : TK => Bool) _ _) t2
  rw [hrun2] at hA
  have hA0 : stackCfg ιT B1
      (⟨some ThrProducer.thrStart, ThrProducer.thrCtl, ThrProducer.T0 k v⟩ : TM2.Cfg (fun _ : TK => Bool) _ _) =
      ⟨some ThrProducer.thrStart, ThrProducer.thrCtl, B1⟩ := by
    simp only [stackCfg]
    rw [bank_eq_self ιT B1 (ThrProducer.T0 k v) (fun x => (b1_t x).symm)]
  rw [hA0] at hA
  obtain ⟨B2, hB2⟩ : ∃ B, B = bank ιT B1 FT := ⟨_, rfl⟩
  have hA' : ((advance pT)^[t2])
      (⟨some ThrProducer.thrStart, ThrProducer.thrCtl, B1⟩ : TM2.Cfg (fun _ : JM => Bool) _ _) =
      ⟨none, vc2, B2⟩ := by rw [hB2]; exact hA
  have b2_t : ∀ x, B2 (tc x) = FT x := fun x => by rw [hB2]; exact bank_at ιT B1 FT x
  have b2_r : ∀ y, B2 (.inr y) = B1 (.inr y) := fun y => by
    rw [hB2]; exact bank_outside ιT _ _ _ (by rintro ⟨z, hz⟩; cases hz)
  have hthr : FT ThrProducer.thrC = ThrProducer.u b := by rw [hb]; exact hT.1
  -- (3) copy the threshold into MK cell 0
  have h3 := MatrixStage4ScalarPreparationOps.copy_run e2 B2 (by
    show B2 (.inr (.inr 0)) = []; rw [b2_r]; exact b1_s)
  have l3 : (B2 (e2 0)).length = b := by
    show (B2 (tc ThrProducer.thrC)).length = b
    rw [b2_t, hthr]; simp [ThrProducer.u]
  rw [l3] at h3
  obtain ⟨B3, hB3⟩ : ∃ B, B = Function.update B2 (e2 1) (B2 (e2 0) ++ B2 (e2 1)) := ⟨_, rfl⟩
  rw [← hB3] at h3
  have b3_t : ∀ x, B3 (tc x) = FT x := fun x => by
    rw [hB3, Function.update_of_ne (by simp [e2, tc, mc]), b2_t]
  have b3_s : B3 sc = [] := by
    rw [hB3, Function.update_of_ne (by simp [e2, sc, mc])]
    show B2 (.inr (.inr 0)) = []; rw [b2_r]; exact b1_s
  have b3_m0 : B3 (mc 0) = MProducer.u b := by
    rw [hB3]; show Function.update B2 (e2 1) _ (e2 1) = _
    rw [Function.update_self]
    show B2 (tc ThrProducer.thrC) ++ B2 (.inr (.inl 0)) = _
    rw [b2_t, hthr, b2_r]
    show ThrProducer.u b ++ B1 (mc 0) = _
    rw [b1_m 0 (by decide), hS0]
    show ThrProducer.u b ++ Function.update (fun _ => []) (2 : MK) (MProducer.u L) 0 = _
    rw [Function.update_of_ne (by decide), List.append_nil]; rfl
  have b3_m : ∀ x : MK, x ≠ 0 → B3 (mc x) = B1 (mc x) := fun x hx => by
    rw [hB3, Function.update_of_ne (by simpa [e2, mc] using hx)]
    exact b2_r _
  -- (4) the sample-dimension producer on MK
  have hM0 : bank ιM B3 (MProducer.M0 b k L) = B3 := by
    apply bank_eq_self
    intro x
    show _ = B3 (mc x)
    by_cases h0 : x = 0
    · subst h0; rw [b3_m0]; simp [MProducer.M0]
    · rw [b3_m x h0]
      by_cases h1' : x = 1
      · subst h1'; rw [b1_m1]; simp [MProducer.M0]
      · rw [b1_m x h1', hS0]
        show _ = Function.update (fun _ => []) (2 : MK) (MProducer.u L) x
        simp only [MProducer.M0, Function.update_apply, if_neg h0, if_neg h1']
  obtain ⟨t4, ht4, vc4, FM, hrun4, hM⟩ := MProducer.m_run b k L
  have hB := BitMachineStackRun.run ιM B3 MProducer.mProg
    (⟨some MProducer.mStart, MProducer.mCtl, MProducer.M0 b k L⟩ : TM2.Cfg (fun _ : MK => Bool) _ _) t4
  rw [hrun4] at hB
  have hB0 : stackCfg ιM B3
      (⟨some MProducer.mStart, MProducer.mCtl, MProducer.M0 b k L⟩ : TM2.Cfg (fun _ : MK => Bool) _ _) =
      ⟨some MProducer.mStart, MProducer.mCtl, B3⟩ := by
    simp only [stackCfg]
    rw [hM0]
  rw [hB0] at hB
  have hB' : ((advance pM)^[t4])
      (⟨some MProducer.mStart, MProducer.mCtl, B3⟩ : TM2.Cfg (fun _ : JM => Bool) _ _) =
      ⟨none, vc4, bank ιM B3 FM⟩ := hB
  have hfin : bank ιM B3 FM = Sum.elim FT (Sum.elim FM (fun _ => [])) := by
    funext x
    rcases x with x | (y | f)
    · rw [bank_outside ιM _ _ _ (by rintro ⟨z, hz⟩; cases hz)]; exact b3_t x
    · exact bank_at ιM B3 FM y
    · rw [bank_outside ιM _ _ _ (by rintro ⟨z, hz⟩; cases hz)]
      have hf : f = 0 := Subsingleton.elim _ _
      subst hf; exact b3_s
  rw [hfin] at hB'
  -- (5) the three charged handoffs
  obtain ⟨a2, ha2, R2⟩ := BitMachineRawSequence.runs (cp e1) pT BitMachineCopy.Label.scan
    ThrProducer.thrStart oc oc ThrProducer.thrCtl _ S0 B1 B2 (2 * k + 2) t2 h1 hA'
  obtain ⟨a3, ha3, R3⟩ := BitMachineRawSequence.runs f1 (cp e2) (leftLabel BitMachineCopy.Label.scan)
    BitMachineCopy.Label.scan g1 _ oc oc S0 B2 B3 a2 (2 * b + 2) R2 h3
  obtain ⟨a4, ha4, R4⟩ := BitMachineRawSequence.runs f2 pM (leftLabel (leftLabel BitMachineCopy.Label.scan))
    MProducer.mStart g2 _ MProducer.mCtl _ S0 B3 _ a3 t4 R3 hB'
  refine ⟨a4, ?_, (g2, vc4), FT, FM, ?_, hT, ?_⟩
  · unfold tmBd; rw [← hb]
    generalize ThrProducer.thrBd k v = TB at *
    generalize MProducer.mBd b k L = MB at *
    omega
  · rw [← hS0]; exact R4
  · rw [← hb]; exact hM

/-- The scheduled count vector read by the threshold producer (the order of `ThrJoin.budget_eq`). -/
def vS (n m Δ : ℕ) (γ : ℚ) : Fin 5 → ℕ :=
  ![LookupSeed.width (Nat.clog 2 n), SourceProfileParameters.width (Nat.clog 2 n),
    SourceProfileParameters.outerWidth (Nat.clog 2 n),
    ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 n),
    ParameterizedCanonicalSource.coverWidth n m (Nat.clog 2 n) Δ γ]

/-- The scheduled threshold is the literal `sourceBudget` (admitted `ThrJoin.budget_eq`, by exact name). -/
theorem thrVal_sched (n m Δ : ℕ) (γ : ℚ) (k : ℕ) :
    thrVal k (vS n m Δ γ) =
      SourceRecursiveNoSampling.sourceBudget (Nat.clog 2 n)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
        (ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ) k :=
  ThrJoin.budget_eq n m Δ γ k

/-- **Segment (1).** The joined threshold + sample-dimension producer at the H-A3 schedule: from the
threshold start bank on the scheduled counts, unary `k` and unary `L = clog₂ n`, ONE fixed program produces
the threshold `sourceBudget L r q k` and the sample dimensions `mY = sourceCols L r q k` (MK cell 10) and
`mX = sourceRows L r q k` (MK cell 13); exact exit bank (`TFacts`, `MFacts`), explicit clock. -/
theorem tm_run_sched (n m Δ : ℕ) (γ : ℚ) (k : ℕ) :
    ∃ t ≤ tmBd k (vS n m Δ γ) (Nat.clog 2 n), ∃ vc, ∃ FT : TK → List Bool, ∃ FM : MK → List Bool,
      ((advance tmProg)^[t])
          (⟨some tmStart, tmCtl, TM0 k (vS n m Δ γ) (Nat.clog 2 n)⟩ : TM2.Cfg (fun _ : JM => Bool) _ _) =
        ⟨none, vc, Sum.elim FT (Sum.elim FM (fun _ => []))⟩ ∧
      TFacts k (vS n m Δ γ) FT ∧ MFacts (thrVal k (vS n m Δ γ)) k (Nat.clog 2 n) FM ∧
      FT ThrProducer.thrC = ThrProducer.u (SourceRecursiveNoSampling.sourceBudget (Nat.clog 2 n)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
        (ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ) k) ∧
      FM 0 = MProducer.u (SourceRecursiveNoSampling.sourceBudget (Nat.clog 2 n)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
        (ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ) k) ∧
      FM 1 = MProducer.u k ∧ FM 2 = MProducer.u (Nat.clog 2 n) ∧
      FM 10 = MProducer.u (SourceRecursiveNoSampling.sourceCols (Nat.clog 2 n)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
        (ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ) k) ∧
      FM 13 = MProducer.u (SourceRecursiveNoSampling.sourceRows (Nat.clog 2 n)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
        (ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ) k) := by
  obtain ⟨t, ht, vc, FT, FM, hr, hT, hM⟩ := tm_run k (vS n m Δ γ) (Nat.clog 2 n)
  have hMF := hM
  have hb := thrVal_sched n m Δ γ k
  unfold MFacts at hM
  rw [hb] at hM
  obtain ⟨h0, h1, h2, -, -, -, -, -, -, -, h10, -, -, h13, -⟩ := hM
  refine ⟨t, ht, vc, FT, FM, hr, hT, hMF, ?_, h0, h1, h2, ?_, ?_⟩
  · rw [hT.1]; exact congrArg ThrProducer.u hb
  · rw [h10, MProducer.cols_eq]
  · rw [h13, MProducer.rows_eq]

end

#print axioms tm_run
#print axioms thrVal_sched
#print axioms tm_run_sched

end Paper2.TMFront
