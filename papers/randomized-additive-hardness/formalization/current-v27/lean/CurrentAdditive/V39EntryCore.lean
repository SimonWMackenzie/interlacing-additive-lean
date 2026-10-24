import CurrentAdditive.V39SeedJoin

/-! Unit 3, segment (4), second part: an entry evaluator with EXACT restore.
Bank `JE = JL ⊕ Fin 6`: the loop bank beside six retained cells (0: row word,
1: column word, 2: serialized level-`K` row code, 3: serialized level-`K` column
code, 4: unary `K`, 5: the answer output cell). ONE fixed program `coreProg`:
`CopyAll` of cells 0-4 into `r1 Xc`, `r1 Yc`, `nC 0`, `nC 1`, `ctr`; `entryProg`
(the k-fold loop and the seed lookup) lifted by `Sum.inl`; `CopyAll` of the answer
cell `ansC` into cell 5; `ClearAll` of `nC 0`, `nC 1`, `r1 Xc`, `r1 Yc`, `ansC`.
From the ready bank `readyE` (retained cells filled, answer cell blank) it halts in
EXACTLY the same bank with `[b]` in cell 5, `b` the entry of the iterated
construction (at the public schedule: `codedCanonicalEntry` of the two words).
This is the per-entry contract of an `EntryRuns` instance except for the indexed
fetch of the two words (not done here). -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39RLoop

noncomputable section

open Paper2
open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries
open BitMachineRawSequence (leftLabel)
open Paper2.TemplateStep (J RS nC r1 r2)

abbrev JE := JL ⊕ Fin 6

def inL : JL ↪ JE := ⟨Sum.inl, Sum.inl_injective⟩
def ret (i : Fin 6) : JE := .inr i

def cpE (a b : JE) (hab : a ≠ b) (ha : a ≠ .inl scr) (hb : b ≠ .inl scr) : Fin 3 ↪ JE :=
  ⟨![a, b, .inl scr], by
    intro u v h
    fin_cases u <;> fin_cases v <;> simp_all⟩

def cpIn : Fin 5 → (Fin 3 ↪ JE) :=
  ![cpE (ret 0) (.inl (jC (r1 RequestSelect.Xc))) (by simp [ret]) (by simp [ret]) (by simp [jC, scr]),
    cpE (ret 1) (.inl (jC (r1 RequestSelect.Yc))) (by simp [ret]) (by simp [ret]) (by simp [jC, scr]),
    cpE (ret 2) (.inl (jC (nC 0))) (by simp [ret]) (by simp [ret]) (by simp [jC, scr]),
    cpE (ret 3) (.inl (jC (nC 1))) (by simp [ret]) (by simp [ret]) (by simp [jC, scr]),
    cpE (ret 4) (.inl ctr) (by simp [ret]) (by simp [ret]) (by simp [ctr, scr])]

def cpOut : Fin 1 → (Fin 3 ↪ JE) :=
  ![cpE (.inl ansC) (ret 5) (by simp [ret]) (by simp [ansC, rv, jC, scr]) (by simp [ret])]

def clOut : Fin 5 → JE :=
  ![.inl (jC (nC 0)), .inl (jC (nC 1)), .inl (jC (r1 RequestSelect.Xc)),
    .inl (jC (r1 RequestSelect.Yc)), .inl ansC]

theorem clOut_injective : Function.Injective clOut := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    first
    | rfl
    | (simp [clOut, ansC, rv, jC, nC, r1, r2, RequestSelect.Xc, RequestSelect.Yc] at h)

def entryL := fun l => stackStmt inL (entryProg l)

def ctlE0 := (((none : Option Bool), bodyCtl), (SeedEntryMachine.readInitial, (none : Option Bool)))
def e1p := BitMachineRawSequence.program (CopyAll.prog cpIn) entryL
  (BitMachineRawSequence.leftLabel (.inl ())) (none : Option Bool) ctlE0
def e2p := BitMachineRawSequence.program e1p (CopyAll.prog cpOut) (.inl ⟨0, by omega⟩)
  ((none : Option Bool), ctlE0) (none : Option Bool)
/-- The entry evaluator: ONE fixed program. -/
def coreProg := BitMachineRawSequence.program e2p (ClearAll.prog clOut) ⟨0, by omega⟩
  (((none : Option Bool), ctlE0), (none : Option Bool)) (none : Option Bool)
def coreCtl := ((((none : Option Bool), ctlE0), (none : Option Bool)), (none : Option Bool))
def coreStart := FetchIndexed.labelOf coreProg (leftLabel (leftLabel (leftLabel
  (.inl ⟨0, by omega⟩ : CopyAll.Lab 5))))

theorem liftE {Kk L V : Type*} [DecidableEq Kk] (ι : Kk ↪ JE)
    (P : L → TM2.Stmt (fun _ : Kk => Bool) L V)
    (W : JE → List Bool) (S T : Kk → List Bool) (hS : ∀ k, S k = W (ι k)) (l : L) (v v' : V)
    (t : ℕ)
    (hrun : ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) =
      ⟨none, v', T⟩) :
    ((advance (fun l => stackStmt ι (P l)))^[t])
        (⟨some l, v, W⟩ : TM2.Cfg (fun _ : JE => Bool) L V) =
      ⟨none, v', bank ι W T⟩ := by
  have hs := BitMachineStackRun.run ι W P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) t
  rw [hrun] at hs
  simp only [stackCfg] at hs
  rwa [bank_eq_self ι W S hS] at hs

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

theorem bankL_Xc (g : EncodedGraph.Graph) (r k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k)
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k) :
    bankL g r k x y (jC (r1 RequestSelect.Xc)) =
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).1.encode x := rfl
theorem bankL_Yc (g : EncodedGraph.Graph) (r k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k)
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k) :
    bankL g r k x y (jC (r1 RequestSelect.Yc)) =
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.encode y := rfl
theorem bankL_nC0 (g : EncodedGraph.Graph) (r k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k)
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k) :
    bankL g r k x y (jC (nC 0)) = encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).1 := rfl
theorem bankL_nC1 (g : EncodedGraph.Graph) (r k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k)
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k) :
    bankL g r k x y (jC (nC 1)) = encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2 := rfl

/-- The loop bank at rest: `J`, `E`, counter and scratch blank, the master copy in `M`. -/
def restL (g : EncodedGraph.Graph) (r : ℕ) : JL → List Bool :=
  Sum.elim (Sum.elim (fun _ => []) (fun _ => []))
    (Sum.elim (master (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r) ![[], []])

/-- The ready bank: the rest bank beside the six retained cells. -/
def readyE (g : EncodedGraph.Graph) (r : ℕ) (xw yw cR cC : List Bool) (K : ℕ) (out : List Bool) :
    JE → List Bool :=
  Sum.elim (restL (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r)
    ![xw, yw, cR, cC, List.replicate K true, out]

theorem readyE_ret (g : EncodedGraph.Graph) (r : ℕ) (xw yw cR cC : List Bool) (K : ℕ)
    (out : List Bool) :
    readyE (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r xw yw cR cC K out (ret 0) = xw ∧
    readyE (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r xw yw cR cC K out (ret 1) = yw ∧
    readyE (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r xw yw cR cC K out (ret 2) = cR ∧
    readyE (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r xw yw cR cC K out (ret 3) = cC ∧
    readyE (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r xw yw cR cC K out (ret 4) =
      List.replicate K true ∧
    readyE (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r xw yw cR cC K out (ret 5) = out :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cpIn_hsd : ∀ i j, cpIn i 0 ≠ cpIn j 1 := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [cpIn, cpE, ret]
theorem cpIn_hzd : ∀ i j, cpIn i 2 ≠ cpIn j 1 := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [cpIn, cpE, jC, scr, ctr]
theorem cpIn_hdd : ∀ i j, cpIn i 1 = cpIn j 1 → i = j := by
  intro i j h; fin_cases i <;> fin_cases j <;>
    simp_all [cpIn, cpE, jC, nC, r1, ctr, RequestSelect.Xc, RequestSelect.Yc]

/-- Exact charged composition clock of the concrete recursive entry program. -/
def coreClock (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K : ℕ)
    (x0 : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (y0 : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) : ℕ :=
    let x := (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q K).1 x0
    let y := (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q K).2 y0
    let activity := V39EdgeSourceFront.edgeActivity g hg (by omega) r hq
    let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q K
    let c := seedRecursiveCodes g.vertices p s q₁ q₂ w Q K
    let sd := V39RecursiveTable.seedRequest activity K x0 y0
    let C0 := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q 0
    let c0 := seedRecursiveCodes g.vertices p s q₁ q₂ w Q 0
    let Lin := (C.1.encode x).length + (C.2.encode y).length + (encodeCode c.1).length +
      (encodeCode c.2).length + K
    let Lout := (encodeCode c0.1).length + (encodeCode c0.2).length + (C0.1.encode sd.1).length +
      (C0.2.encode sd.2).length + 1
  ((5 * (2 * Lin + 3) + 1 +
        (K * (loopBd g hg hs r hq ξ K x0 y0 + 2) + 1 + (9 * p + 13) + 1) + 1) +
        (1 * (2 * 1 + 3) + 1) + 1) + (5 * (Lout + 1) + 1) + 1

theorem core_run (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K : ℕ)
    (x0 : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (y0 : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    let x := (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q K).1 x0
    let y := (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q K).2 y0
    let activity := V39EdgeSourceFront.edgeActivity g hg (by omega) r hq
    let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q K
    let c := seedRecursiveCodes g.vertices p s q₁ q₂ w Q K
    let sd := V39RecursiveTable.seedRequest activity K x0 y0
    let C0 := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q 0
    let c0 := seedRecursiveCodes g.vertices p s q₁ q₂ w Q 0
    let Lin := (C.1.encode x).length + (C.2.encode y).length + (encodeCode c.1).length +
      (encodeCode c.2).length + K
    let Lout := (encodeCode c0.1).length + (encodeCode c0.2).length + (C0.1.encode sd.1).length +
      (C0.2.encode sd.2).length + 1
    ∃ t ≤ ((5 * (2 * Lin + 3) + 1 +
        (K * (loopBd g hg hs r hq ξ K x0 y0 + 2) + 1 + (9 * p + 13) + 1) + 1) +
        (1 * (2 * 1 + 3) + 1) + 1) + (5 * (Lout + 1) + 1) + 1, ∃ v,
      ((advance coreProg)^[t])
        (⟨some coreStart, coreCtl,
          readyE (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r
            (C.1.encode x) (C.2.encode y) (encodeCode c.1) (encodeCode c.2) K []⟩ :
          TM2.Cfg (fun _ : JE => Bool) _ _) =
        ⟨none, v, readyE (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r
            (C.1.encode x) (C.2.encode y) (encodeCode c.1) (encodeCode c.2) K
            [V39RecursiveTable.matrix activity K x0 y0]⟩ := by
  intro x y activity C c sd C0 c0 Lin Lout
  set R0 := readyE (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r
    (C.1.encode x) (C.2.encode y) (encodeCode c.1) (encodeCode c.2) K [] with hR0
  set b := V39RecursiveTable.matrix activity K x0 y0 with hb
  -- (1) copies in
  obtain ⟨t1, ht1, v1, r1run⟩ := CopyAll.all_run cpIn cpIn_hsd cpIn_hzd cpIn_hdd R0
    (fun i => by fin_cases i <;> rfl) Lin
    (by
      intro i
      fin_cases i
      · show (C.1.encode x).length ≤ Lin; omega
      · show (C.2.encode y).length ≤ Lin; omega
      · show (encodeCode c.1).length ≤ Lin; omega
      · show (encodeCode c.2).length ≤ Lin; omega
      · show (List.replicate K true).length ≤ Lin; simp [Lin])
    none
  set B1 := CopyAll.done cpIn 5 R0 with hB1
  have hS1 : ∀ a : JL, bankL g r K x y a = B1 (inL a) := by
    intro a
    by_cases hX : a = jC (r1 RequestSelect.Xc)
    · subst hX
      rw [hB1, show inL (jC (r1 RequestSelect.Xc)) = cpIn 0 1 from rfl,
        CopyAll.done_dst cpIn cpIn_hdd R0 0]; exact (List.append_nil _).symm
    by_cases hY : a = jC (r1 RequestSelect.Yc)
    · subst hY
      rw [hB1, show inL (jC (r1 RequestSelect.Yc)) = cpIn 1 1 from rfl,
        CopyAll.done_dst cpIn cpIn_hdd R0 1]; exact (List.append_nil _).symm
    by_cases h0 : a = jC (nC 0)
    · subst h0
      rw [hB1, show inL (jC (nC 0)) = cpIn 2 1 from rfl, CopyAll.done_dst cpIn cpIn_hdd R0 2]; exact (List.append_nil _).symm
    by_cases h1 : a = jC (nC 1)
    · subst h1
      rw [hB1, show inL (jC (nC 1)) = cpIn 3 1 from rfl, CopyAll.done_dst cpIn cpIn_hdd R0 3]; exact (List.append_nil _).symm
    by_cases hc : a = ctr
    · subst hc
      rw [hB1, show inL ctr = cpIn 4 1 from rfl, CopyAll.done_dst cpIn cpIn_hdd R0 4]
      show List.replicate K true = List.replicate K true ++ []
      simp
    rw [hB1, CopyAll.done_off cpIn R0 (inL a) (by
      intro j; fin_cases j
      · intro h; exact hX (Sum.inl_injective h).symm
      · intro h; exact hY (Sum.inl_injective h).symm
      · intro h; exact h0 (Sum.inl_injective h).symm
      · intro h; exact h1 (Sum.inl_injective h).symm
      · intro h; exact hc (Sum.inl_injective h).symm) 5]
    rcases a with (j | z) | cc
    · show J0 K x y j = []
      exact J0_support K x y j (fun h => h0 (by rw [h]; rfl)) (fun h => h1 (by rw [h]; rfl))
        (fun h => hX (by rw [h]; rfl)) (fun h => hY (by rw [h]; rfl))
    · rfl
    · rcases cc with z | i
      · rfl
      · fin_cases i
        · exact absurd rfl hc
        · rfl
  -- (2) the loop and the seed lookup
  obtain ⟨t2, ht2, v2, r2run⟩ := seed_join g hg hp hs r hq ξ K x0 y0
  have r2L := liftE inL entryProg B1 _ _ hS1 _ _ _ _ r2run
  set F := Function.update (bankL (n := g.vertices) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) g r 0 sd.1 sd.2) ansC [b] with hF
  set B2 := bank inL B1 F with hB2
  obtain ⟨u1, hu1, s1⟩ := BitMachineRawSequence.runs (CopyAll.prog cpIn) entryL (.inl ⟨0, by omega⟩)
    (BitMachineRawSequence.leftLabel (.inl ())) none v1 ctlE0 v2 R0 B1 B2 t1 t2 r1run r2L
  have hB2l : ∀ a, B2 (.inl a) = F a := fun a => bank_at inL B1 F a
  have hB2r : ∀ i, B2 (.inr i) = R0 (.inr i) := by
    intro i
    rw [hB2, bank_outside inL B1 F (.inr i) (by rintro ⟨kk, hkk⟩; cases hkk), hB1,
      CopyAll.done_off cpIn R0 (.inr i) (by intro j; fin_cases j <;> simp [cpIn, cpE]) 5]
  -- (3) the answer out
  obtain ⟨t3, ht3, v3, r3run⟩ := CopyAll.all_run cpOut
    (by intro i j; fin_cases i; fin_cases j; simp [cpOut, cpE, ret])
    (by intro i j; fin_cases i; fin_cases j; simp [cpOut, cpE, ret])
    (by intro i j _; fin_cases i; fin_cases j; rfl) B2
    (by intro i; fin_cases i; show B2 (.inl scr) = []; rw [hB2l, hF,
      Function.update_of_ne (by simp [scr, ansC, rv, jC])]; rfl) 1
    (by intro i; fin_cases i; show (B2 (.inl ansC)).length ≤ 1; rw [hB2l, hF,
      Function.update_self]; simp)
    none
  set B3 := CopyAll.done cpOut 1 B2 with hB3
  obtain ⟨u2, hu2, s2⟩ := BitMachineRawSequence.runs e1p (CopyAll.prog cpOut)
    (leftLabel (.inl ⟨0, by omega⟩)) (.inl ⟨0, by omega⟩) ((none : Option Bool), ctlE0)
    ((none : Option Bool), v2) none v3 R0 B2 B3 u1 t3 s1 r3run
  have h3off : ∀ a, a ≠ ret 5 → B3 a = B2 a := by
    intro a ha
    rw [hB3]
    exact CopyAll.done_off cpOut B2 a (by intro j; fin_cases j; intro h; exact ha h.symm) 1
  have h3out : B3 (ret 5) = [b] := by
    rw [hB3, show ret 5 = cpOut 0 1 from rfl, CopyAll.done_dst cpOut
      (by intro i j _; fin_cases i; fin_cases j; rfl) B2 0]
    show B2 (.inl ansC) ++ B2 (.inr 5) = [b]
    rw [hB2l, hB2r, hF, Function.update_self]; rfl
  -- (4) clear the level-0 residue
  obtain ⟨t4, ht4, v4, r4run⟩ := ClearAll.all_run clOut clOut_injective Lout B3
    (by
      intro j
      fin_cases j
      · show (B3 (.inl (jC (nC 0)))).length ≤ Lout
        rw [h3off _ (by simp [ret]), hB2l, hF, Function.update_of_ne (by simp [ansC, rv, jC, nC, r2]),
          bankL_nC0]
        show (encodeCode c0.1).length ≤ Lout
        simp only [Lout]; omega
      · show (B3 (.inl (jC (nC 1)))).length ≤ Lout
        rw [h3off _ (by simp [ret]), hB2l, hF, Function.update_of_ne (by simp [ansC, rv, jC, nC, r2]),
          bankL_nC1]
        show (encodeCode c0.2).length ≤ Lout
        simp only [Lout]; omega
      · show (B3 (.inl (jC (r1 RequestSelect.Xc)))).length ≤ Lout
        rw [h3off _ (by simp [ret]), hB2l, hF, Function.update_of_ne (by simp [ansC, rv, jC, r1, r2]),
          bankL_Xc]
        simp only [Lout, C0]; omega
      · show (B3 (.inl (jC (r1 RequestSelect.Yc)))).length ≤ Lout
        rw [h3off _ (by simp [ret]), hB2l, hF, Function.update_of_ne (by simp [ansC, rv, jC, r1, r2]),
          bankL_Yc]
        simp only [Lout, C0]; omega
      · show (B3 (.inl ansC)).length ≤ Lout
        rw [h3off _ (by simp [ret]), hB2l, hF, Function.update_self]; simp [Lout])
    none
  set B4 := ClearAll.clearFrom clOut 0 B3 with hB4
  obtain ⟨u3, hu3, s3⟩ := BitMachineRawSequence.runs e2p (ClearAll.prog clOut)
    (leftLabel (leftLabel (.inl ⟨0, by omega⟩))) ⟨0, by omega⟩ (((none : Option Bool), ctlE0),
      (none : Option Bool)) (((none : Option Bool), ctlE0), v3) none v4 R0 B3 B4 u2 t4 s2 r4run
  have hfinal : B4 = readyE (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r
      (C.1.encode x) (C.2.encode y) (encodeCode c.1) (encodeCode c.2) K [b] := by
    funext a
    rcases a with a | i
    · by_cases hin : ∃ j, clOut j = .inl a
      · rw [hB4, clr_in clOut B3 _ hin]
        obtain ⟨j, hj⟩ := hin
        obtain ⟨j', rfl⟩ : ∃ j' : J, a = jC j' := by
          fin_cases j
          · exact ⟨nC 0, (Sum.inl_injective hj).symm⟩
          · exact ⟨nC 1, (Sum.inl_injective hj).symm⟩
          · exact ⟨r1 RequestSelect.Xc, (Sum.inl_injective hj).symm⟩
          · exact ⟨r1 RequestSelect.Yc, (Sum.inl_injective hj).symm⟩
          · exact ⟨r2 (.inr (.inr 4)), (Sum.inl_injective hj).symm⟩
        rfl
      · push_neg at hin
        rw [hB4, clr_out clOut B3 _ hin, h3off _ (by simp [ret]), hB2l, hF,
          Function.update_of_ne (fun h => hin 4 (by rw [h]; rfl))]
        show bankL g r 0 sd.1 sd.2 a = restL g r a
        rcases a with (j | z) | cc
        · show J0 0 sd.1 sd.2 j = []
          exact J0_support 0 sd.1 sd.2 j (fun h => hin 0 (by rw [h]; rfl))
            (fun h => hin 1 (by rw [h]; rfl)) (fun h => hin 2 (by rw [h]; rfl))
            (fun h => hin 3 (by rw [h]; rfl))
        · rfl
        · rcases cc with z | i
          · rfl
          · fin_cases i
            · rfl
            · rfl
    · by_cases h5 : i = 5
      · subst h5
        rw [hB4, clr_out clOut B3 _ (by intro j; fin_cases j <;> simp [clOut]),
          show (Sum.inr 5 : JE) = ret 5 from rfl, h3out]
        exact ((readyE_ret (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r
          (C.1.encode x) (C.2.encode y) (encodeCode c.1) (encodeCode c.2) K [b]).2.2.2.2.2).symm
      · rw [hB4, clr_out clOut B3 _ (by intro j; fin_cases j <;> simp [clOut]),
          h3off _ (by simp [ret, h5]), hB2r, hR0]
        have E0 := readyE_ret (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r
          (C.1.encode x) (C.2.encode y) (encodeCode c.1) (encodeCode c.2) K []
        have E1 := readyE_ret (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r
          (C.1.encode x) (C.2.encode y) (encodeCode c.1) (encodeCode c.2) K [b]
        fin_cases i
        · show readyE g r _ _ _ _ K [] (ret 0) = readyE g r _ _ _ _ K [b] (ret 0)
          rw [E0.1, E1.1]
        · show readyE g r _ _ _ _ K [] (ret 1) = readyE g r _ _ _ _ K [b] (ret 1)
          rw [E0.2.1, E1.2.1]
        · show readyE g r _ _ _ _ K [] (ret 2) = readyE g r _ _ _ _ K [b] (ret 2)
          rw [E0.2.2.1, E1.2.2.1]
        · show readyE g r _ _ _ _ K [] (ret 3) = readyE g r _ _ _ _ K [b] (ret 3)
          rw [E0.2.2.2.1, E1.2.2.2.1]
        · show readyE g r _ _ _ _ K [] (ret 4) = readyE g r _ _ _ _ K [b] (ret 4)
          rw [E0.2.2.2.2.1, E1.2.2.2.2.1]
        · exact absurd rfl h5
  refine ⟨u3, ?_, ((((none : Option Bool), ctlE0), (none : Option Bool)), v4), ?_⟩
  · omega
  · rw [← hfinal]; exact s3

end

#print axioms clOut_injective
#print axioms core_run

end CurrentAdditive.V39RLoop
