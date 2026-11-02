import EthInapproximability.CurrentPaper.G5fLevelTest
import EthInapproximability.CurrentPaper.G5fCleanCall

/-!
# Segment 1, component: the joined per-level test with physical `clog` (private lane owner:b-g5-6)

On ANY bank `K`: work cells `W` (operands `a b`, temporary `t`, verdict log `O`), a region `R.e` for the
admitted `clog` machine (blank before and after), and source cells. ONE fixed program `levelTest`:

1. `clogBlk rows`: charged copy of `rows` into the region's input cell, one charged push of the fuel
   bit, the CLEAN `clog` call (`G5fCleanCall`), the comparator block `clog rows ≤ T` (verdict pushed on
   `O`), a charged clear of the region's input cell;
2. `clogBlk cols` likewise;
3. the comparator blocks `cost ≤ T`, `2 ≤ rows`, `2 ≤ cols` (`G5fLevelTest.blk2`, `blk1`).

Exit bank EXACT: `update S W.O (five verdict bits :: S W.O)`, every other cell unchanged (region and
work cells blank again). `level_full_iff`: the five bits are all `true` iff, together with the
level-independent block, the level passes `Parameters.Accepted`.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5fLevelFull

open Turing BitMachineEncoding BitMachineStackEmbedding
open G5fLevelTest (Cells Out)

abbrev LM := ExactParameterMachineLog.machine

variable {K : Type} [DecidableEq K]

/-- Clear one cell (charged: one pop per bit, plus one). -/
def clrP (c : K) : Unit → TM2.Stmt (fun _ : K => Bool) Unit (Option Bool) :=
  fun _ => .pop c (fun _ b => b) (.branch Option.isSome (.goto fun _ => ()) .halt)

theorem clr_run (c : K) : ∀ (L : List Bool) (S : K → List Bool) (v : Option Bool), S c = L →
    ((advance (clrP c))^[L.length + 1])
        (⟨some (), v, S⟩ : TM2.Cfg (fun _ : K => Bool) Unit (Option Bool)) =
      ⟨none, none, Function.update S c []⟩ := by
  intro L
  induction L with
  | nil =>
    intro S v h
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one]
    simp only [advance, TM2.step, clrP, TM2.stepAux, h, List.head?_nil, List.tail_nil,
      Option.isSome_none, cond_false, Option.getD_some]
  | cons b L ih =>
    intro S v h
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : advance (clrP c)
        (⟨some (), v, S⟩ : TM2.Cfg (fun _ : K => Bool) Unit (Option Bool)) =
        ⟨some (), some b, Function.update S c L⟩ := by
      simp only [advance, TM2.step, clrP, TM2.stepAux, h, List.head?_cons, List.tail_cons,
        Option.isSome_some, cond_true, Option.getD_some]
    rw [hstep, ih _ _ (Function.update_self _ _ _), Function.update_idem]

/-- Push one `true` (the fuel bit). -/
def pushP (c : K) : Unit → TM2.Stmt (fun _ : K => Bool) Unit Unit :=
  fun _ => .push c (fun _ => true) .halt

theorem push_run (c : K) (S : K → List Bool) :
    ((advance (pushP c))^[1]) (⟨some (), (), S⟩ : TM2.Cfg (fun _ : K => Bool) Unit Unit) =
      ⟨none, (), Function.update S c (true :: S c)⟩ := rfl

/-- The `clog` region, disjoint from the work cells. -/
structure Reg (W : Cells K) where
  e : BitMachineIteration.Stack LM ↪ K
  hW : ∀ k, Out W (e k)

variable {W : Cells K}

/-- The region's input cell and fuel cell. -/
abbrev Reg.x (R : Reg W) : K := R.e (.inl LM.input)
abbrev Reg.f (R : Reg W) : K := R.e (.inr 0)

omit [DecidableEq K] in
theorem Reg.xf (R : Reg W) : R.x ≠ R.f := by
  intro h; have := R.e.injective h; cases this

/-- A source cell: outside the work cells and the region. -/
def Src (W : Cells K) (R : Reg W) (s : K) : Prop := Out W s ∧ ∀ k, R.e k ≠ s

def c2 := G5fLevelTest.c2
def cLog : BitMachineIteration.Control LM := (LM.initial, none)

/-- `clog |src| ≤ |T|` as one charged block with a clean region. -/
def clogBlk (R : Reg W) (src T : K) (hs : Src W R src) (hT : Src W R T) :=
  BitMachineRawSequence.program
    (G5fPadCore.cp3 src R.x W.t (fun h => hs.2 _ h.symm) hs.1.2.2.1 (R.hW _).2.2.1)
    (BitMachineRawSequence.program (pushP R.f)
      (BitMachineRawSequence.program (G5fCleanCall.callProgram LM R.e)
        (BitMachineRawSequence.program
          (G5fLevelTest.blk2 W R.x T (R.hW _) hT.1 true true false) (clrP R.x) ()
          G5fLevelTest.c2 none)
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)) cLog (G5fLevelTest.c2, none))
      (BitMachineRawSequence.leftLabel (.inr .testFuel)) () (cLog, (G5fLevelTest.c2, none)))
    (BitMachineRawSequence.leftLabel ()) none ((), (cLog, (G5fLevelTest.c2, none)))

def clogCtrl : Option Bool × (Unit × (BitMachineIteration.Control LM ×
    ((Option Bool × (Option Bool × EntryUnaryCompare.CV)) × Option Bool))) :=
  (none, ((), (cLog, (G5fLevelTest.c2, none))))

theorem clogBlk_run (R : Reg W) (src T : K) (hs : Src W R src) (hT : Src W R T)
    (S : K → List Bool) (m n : ℕ) (hsrc : S src = List.replicate m true)
    (hTS : S T = List.replicate n true) (hreg : ∀ k, S (R.e k) = [])
    (ha : S W.a = []) (hb : S W.b = []) (ht : S W.t = []) :
    ∃ u ≤ (2 * m + 2) + (1 + ((BitMachineIteration.roundBound ExactParameterMachineLog.machine m
        ((UnaryBinaryEncoding.coefficient + 6) * (m + 1) ^ 2) + 1) +
        (((2 * Nat.clog 2 m + 2) + ((2 * n + 2) + (max (Nat.clog 2 m) n + 2) + 1) + 1) +
          (Nat.clog 2 m + 1) + 1) + 1) + 1) + 1,
      ((advance (clogBlk R src T hs hT))^[u])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), clogCtrl, S⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, clogCtrl,
          Function.update S W.O
            (EntryUnaryCompare.verdict true true false (Nat.clog 2 m) n :: S W.O)⟩ := by
  have hxS : S R.x = [] := hreg _
  have hfS : S R.f = [] := hreg _
  -- 1. load
  have s1 := G5fPadCore.cp3_run src R.x W.t (fun h => hs.2 _ h.symm) hs.1.2.2.1 (R.hW _).2.2.1
    S hxS ht
  rw [hsrc, List.length_replicate] at s1
  set S1 := Function.update S R.x (List.replicate m true) with hS1
  -- 2. fuel
  have s2 := push_run R.f S1
  have e2 : S1 R.f = [] := by rw [hS1, Function.update_of_ne R.xf.symm]; exact hfS
  rw [e2] at s2
  set S2 := Function.update S1 R.f [true] with hS2
  -- 3. clean clog call
  have hstart : ∀ k, S2 (R.e k) = G5fCleanCall.startRegion LM (List.replicate m true) k := by
    intro k
    rcases k with k | k
    · by_cases hk : k = LM.input
      · subst hk
        rw [G5fCleanCall.startRegion_input, hS2, Function.update_of_ne R.xf, hS1]
        exact Function.update_self _ _ _
      · have h1 : R.e (.inl k) ≠ R.f := by
          intro h; have := R.e.injective h; cases this
        have h2 : R.e (.inl k) ≠ R.x := by
          intro h; have := R.e.injective h; exact hk (Sum.inl_injective this)
        rw [G5fCleanCall.startRegion_other _ _ _ hk, hS2, Function.update_of_ne h1, hS1,
          Function.update_of_ne h2]
        exact hreg _
    · fin_cases k
      · show S2 R.f = _
        rw [hS2, Function.update_self]; rfl
      · have h1 : R.e (.inr 1) ≠ R.f := by
          intro h; have := R.e.injective h; simp at this
        have h2 : R.e (.inr 1) ≠ R.x := by
          intro h; have := R.e.injective h; cases this
        show S2 (R.e (.inr 1)) = _
        rw [hS2, Function.update_of_ne h1, hS1, Function.update_of_ne h2, hreg]; rfl
  obtain ⟨t3, ht3, s3⟩ := G5fCleanCall.clog_call_run R.e S2 m hstart
  have hS3 : bank R.e S2 (BitMachineIteration.finished LM
      (List.replicate (Nat.clog 2 m) true)).stk =
      Function.update S R.x (List.replicate (Nat.clog 2 m) true) := by
    funext z
    by_cases hz : ∃ k, R.e k = z
    · obtain ⟨k, rfl⟩ := hz
      rw [bank_at]
      by_cases hk : k = .inl LM.input
      · subst hk
        rw [G5fCleanCall.finished_input]
        exact (Function.update_self R.x (List.replicate (Nat.clog 2 m) true) S).symm
      · rw [G5fCleanCall.finished_other _ _ _ hk]
        have h2 : R.e k ≠ R.x := fun h => hk (R.e.injective h)
        rw [Function.update_of_ne h2, hreg]
    · rw [bank_outside _ _ _ _ hz]
      have h1 : z ≠ R.f := fun h => hz ⟨_, h.symm⟩
      have h2 : z ≠ R.x := fun h => hz ⟨_, h.symm⟩
      rw [hS2, Function.update_of_ne h1, hS1, Function.update_of_ne h2, Function.update_of_ne h2]
  rw [hS3] at s3
  set S3 := Function.update S R.x (List.replicate (Nat.clog 2 m) true) with hS3'
  -- 4. compare
  have hxO : R.x ≠ W.O := (R.hW _).2.2.2
  obtain ⟨t4, ht4, w4, s4⟩ := G5fLevelTest.blk2_run W R.x T (R.hW _) hT.1 true true false S3
    (Nat.clog 2 m) n (Function.update_self _ _ _)
    (by rw [hS3', Function.update_of_ne (fun h => hT.2 _ h.symm)]; exact hTS)
    (by rw [hS3', Function.update_of_ne (R.hW _).1.symm]; exact ha)
    (by rw [hS3', Function.update_of_ne (R.hW _).2.1.symm]; exact hb)
    (by rw [hS3', Function.update_of_ne (R.hW _).2.2.1.symm]; exact ht)
  have eO : S3 W.O = S W.O := by rw [hS3', Function.update_of_ne hxO.symm]
  rw [eO] at s4
  -- 5. clear the region input cell
  have s5 := clr_run R.x (List.replicate (Nat.clog 2 m) true)
    (Function.update S3 W.O (EntryUnaryCompare.verdict true true false (Nat.clog 2 m) n :: S W.O))
    none (by rw [Function.update_of_ne hxO, hS3', Function.update_self])
  have hfin : Function.update (Function.update S3 W.O
      (EntryUnaryCompare.verdict true true false (Nat.clog 2 m) n :: S W.O)) R.x [] =
      Function.update S W.O (EntryUnaryCompare.verdict true true false (Nat.clog 2 m) n :: S W.O) := by
    have hSx : Function.update S R.x [] = S := Function.update_eq_self_iff.mpr hxS.symm
    rw [Function.update_comm hxO.symm, hS3', Function.update_idem, hSx]
  rw [hfin, List.length_replicate] at s5
  obtain ⟨u4, hu4, r4⟩ := BitMachineRawSequence.runs _ (clrP R.x) _ () G5fLevelTest.c2 _ none none
    _ _ _ _ _ s4 s5
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs _ _ _ _ cLog _ _ _ _ _ _ _ _ s3 r4
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs _ _ _ _ () _ _ _ _ _ _ _ _ s2 r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs _ _ _ _ none _ _ _ _ _ _ _ _ s1 r2
  exact ⟨u1, by omega, r1⟩

#print axioms clr_run
#print axioms push_run
#print axioms clogBlk_run

/-- The clog block's clock. -/
def clogB (m n : ℕ) : ℕ :=
  (2 * m + 2) + (1 + ((BitMachineIteration.roundBound ExactParameterMachineLog.machine m
    ((UnaryBinaryEncoding.coefficient + 6) * (m + 1) ^ 2) + 1) +
    (((2 * Nat.clog 2 m + 2) + ((2 * n + 2) + (max (Nat.clog 2 m) n + 2) + 1) + 1) +
      (Nat.clog 2 m + 1) + 1) + 1) + 1) + 1

/-- The level's source cells. -/
structure LSrcs (W : Cells K) (R : Reg W) where
  cost : K
  rows : K
  cols : K
  T : K
  hcost : Src W R cost
  hrows : Src W R rows
  hcols : Src W R cols
  hT : Src W R T

/-- **ONE fixed per-level test program.** -/
def levelProgram (R : Reg W) (X : LSrcs W R) :=
  BitMachineRawSequence.program (clogBlk R X.rows X.T X.hrows X.hT)
    (BitMachineRawSequence.program (clogBlk R X.cols X.T X.hcols X.hT)
      (BitMachineRawSequence.program
        (G5fLevelTest.blk2 W X.cost X.T X.hcost.1 X.hT.1 true true false)
        (BitMachineRawSequence.program (G5fLevelTest.blk1 W X.rows X.hrows.1 false false true)
          (G5fLevelTest.blk1 W X.cols X.hcols.1 false false true)
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) G5fLevelTest.c1 G5fLevelTest.c1)
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
        G5fLevelTest.c2 (G5fLevelTest.c1, G5fLevelTest.c1))
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
      clogCtrl (G5fLevelTest.c2, (G5fLevelTest.c1, G5fLevelTest.c1)))
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    clogCtrl (clogCtrl, (G5fLevelTest.c2, (G5fLevelTest.c1, G5fLevelTest.c1)))

theorem level_run (R : Reg W) (X : LSrcs W R) (S : K → List Bool) (cost rows cols T : ℕ)
    (h1 : S X.cost = List.replicate cost true) (h2 : S X.rows = List.replicate rows true)
    (h3 : S X.cols = List.replicate cols true) (h4 : S X.T = List.replicate T true)
    (hreg : ∀ k, S (R.e k) = []) (ha : S W.a = []) (hb : S W.b = []) (ht : S W.t = []) :
    ∃ u ≤ clogB rows T + clogB cols T + ((2 * cost + 2) + ((2 * T + 2) + (max cost T + 2) + 1) + 1) +
        ((2 * rows + 2) + (1 + (max rows 1 + 2) + 1) + 1) +
        ((2 * cols + 2) + (1 + (max cols 1 + 2) + 1) + 1) + 4, ∃ w,
      ((advance (levelProgram R X))^[u])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          (clogCtrl, (clogCtrl, (G5fLevelTest.c2, (G5fLevelTest.c1, G5fLevelTest.c1)))), S⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, (clogCtrl, (clogCtrl, (G5fLevelTest.c2, (G5fLevelTest.c1, w)))),
          Function.update S W.O
            (EntryUnaryCompare.verdict false false true cols 1 ::
              EntryUnaryCompare.verdict false false true rows 1 ::
              EntryUnaryCompare.verdict true true false cost T ::
              EntryUnaryCompare.verdict true true false (Nat.clog 2 cols) T ::
              EntryUnaryCompare.verdict true true false (Nat.clog 2 rows) T :: S W.O)⟩ := by
  have hOa : W.a ≠ W.O := W.aO
  have hOb : W.b ≠ W.O := W.bO
  have hOt : W.t ≠ W.O := W.tO
  have keep : ∀ (S' : K → List Bool) (z : K) (u : List Bool), z ≠ W.O →
      Function.update S' W.O u z = S' z := fun S' z u h => Function.update_of_ne h _ _
  have hrO : ∀ k, R.e k ≠ W.O := fun k => (R.hW k).2.2.2
  obtain ⟨u1, hu1, r1⟩ := clogBlk_run R X.rows X.T X.hrows X.hT S rows T h2 h4 hreg ha hb ht
  set S1 := Function.update S W.O
    (EntryUnaryCompare.verdict true true false (Nat.clog 2 rows) T :: S W.O) with hS1
  obtain ⟨u2, hu2, r2⟩ := clogBlk_run R X.cols X.T X.hcols X.hT S1 cols T
    (by rw [hS1, keep _ _ _ X.hcols.1.2.2.2]; exact h3) (by rw [hS1, keep _ _ _ X.hT.1.2.2.2]; exact h4)
    (fun k => by rw [hS1, keep _ _ _ (hrO k)]; exact hreg k)
    (by rw [hS1, keep _ _ _ hOa]; exact ha) (by rw [hS1, keep _ _ _ hOb]; exact hb)
    (by rw [hS1, keep _ _ _ hOt]; exact ht)
  rw [hS1, G5fLevelTest.upd_upd_O, Function.update_self] at r2
  set S2 := Function.update S W.O
    (EntryUnaryCompare.verdict true true false (Nat.clog 2 cols) T ::
      EntryUnaryCompare.verdict true true false (Nat.clog 2 rows) T :: S W.O) with hS2
  obtain ⟨u3, hu3, w3, r3⟩ := G5fLevelTest.blk2_run W X.cost X.T X.hcost.1 X.hT.1 true true false
    S2 cost T (by rw [hS2, keep _ _ _ X.hcost.1.2.2.2]; exact h1)
    (by rw [hS2, keep _ _ _ X.hT.1.2.2.2]; exact h4)
    (by rw [hS2, keep _ _ _ hOa]; exact ha) (by rw [hS2, keep _ _ _ hOb]; exact hb)
    (by rw [hS2, keep _ _ _ hOt]; exact ht)
  rw [hS2, G5fLevelTest.upd_upd_O, Function.update_self] at r3
  set S3 := Function.update S W.O
    (EntryUnaryCompare.verdict true true false cost T ::
      EntryUnaryCompare.verdict true true false (Nat.clog 2 cols) T ::
      EntryUnaryCompare.verdict true true false (Nat.clog 2 rows) T :: S W.O) with hS3
  obtain ⟨u4, hu4, w4, r4⟩ := G5fLevelTest.blk1_run W X.rows X.hrows.1 false false true S3 rows
    (by rw [hS3, keep _ _ _ X.hrows.1.2.2.2]; exact h2)
    (by rw [hS3, keep _ _ _ hOa]; exact ha) (by rw [hS3, keep _ _ _ hOb]; exact hb)
    (by rw [hS3, keep _ _ _ hOt]; exact ht)
  rw [hS3, G5fLevelTest.upd_upd_O, Function.update_self] at r4
  set S4 := Function.update S W.O
    (EntryUnaryCompare.verdict false false true rows 1 ::
      EntryUnaryCompare.verdict true true false cost T ::
      EntryUnaryCompare.verdict true true false (Nat.clog 2 cols) T ::
      EntryUnaryCompare.verdict true true false (Nat.clog 2 rows) T :: S W.O) with hS4
  obtain ⟨u5, hu5, w5, r5⟩ := G5fLevelTest.blk1_run W X.cols X.hcols.1 false false true S4 cols
    (by rw [hS4, keep _ _ _ X.hcols.1.2.2.2]; exact h3)
    (by rw [hS4, keep _ _ _ hOa]; exact ha) (by rw [hS4, keep _ _ _ hOb]; exact hb)
    (by rw [hS4, keep _ _ _ hOt]; exact ht)
  rw [hS4, G5fLevelTest.upd_upd_O, Function.update_self] at r5
  obtain ⟨v4, hv4, q4⟩ := BitMachineRawSequence.runs _ _ _ _ G5fLevelTest.c1 _ G5fLevelTest.c1 _
    _ _ _ _ _ r4 r5
  obtain ⟨v3, hv3, q3⟩ := BitMachineRawSequence.runs _ _ _ _ G5fLevelTest.c2 _
    (G5fLevelTest.c1, G5fLevelTest.c1) _ _ _ _ _ _ r3 q4
  obtain ⟨v2, hv2, q2⟩ := BitMachineRawSequence.runs _ _ _ _ clogCtrl _
    (G5fLevelTest.c2, (G5fLevelTest.c1, G5fLevelTest.c1)) _ _ _ _ _ _ r2 q3
  obtain ⟨v1, hv1, q1⟩ := BitMachineRawSequence.runs _ _ _ _ clogCtrl _
    (clogCtrl, (G5fLevelTest.c2, (G5fLevelTest.c1, G5fLevelTest.c1))) _ _ _ _ _ _ r1 q2
  have hu1' : u1 ≤ clogB rows T := hu1
  have hu2' : u2 ≤ clogB cols T := hu2
  exact ⟨v1, by omega, (none, ((), w5)), q1⟩

/-- **The joined per-level test decides the level.** With the level's words
(`cost = y_j + j`, rows, columns) and the threshold word `T = 2^(Sstar b c |E|)`, the five bits pushed
by `levelProgram` are all `true` iff (given the level-independent block) the level passes `Accepted`. -/
theorem level_full_iff {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (c b : ℕ)
    (initial : Iteration.State) (j : ℕ) (hE : 1 ≤ Fintype.card E) :
    Parameters.Accepted (EffectiveIteration.runParameters G c b initial j) ↔
      (G5fAccepted.Good b c (Fintype.card E) 0 ∧ 2 ^ 24 ≤ G5fAccepted.Sstar b c (Fintype.card E) ∧
        c ≤ 2 ^ G5fAccepted.Sstar b c (Fintype.card E) ∧
        b ≤ 2 ^ G5fAccepted.Sstar b c (Fintype.card E) ∧
        Nat.clog 2 (Fintype.card E + 2) ≤ 2 ^ G5fAccepted.Sstar b c (Fintype.card E)) ∧
      (EntryUnaryCompare.verdict false false true (Iteration.run G c b initial j).matrix.columns 1 = true ∧
        EntryUnaryCompare.verdict false false true (Iteration.run G c b initial j).matrix.rows 1 = true ∧
        EntryUnaryCompare.verdict true true false ((Iteration.run G c b initial j).budget + j)
          (2 ^ G5fAccepted.Sstar b c (Fintype.card E)) = true ∧
        EntryUnaryCompare.verdict true true false
          (Nat.clog 2 (Iteration.run G c b initial j).matrix.columns)
          (2 ^ G5fAccepted.Sstar b c (Fintype.card E)) = true ∧
        EntryUnaryCompare.verdict true true false
          (Nat.clog 2 (Iteration.run G c b initial j).matrix.rows)
          (2 ^ G5fAccepted.Sstar b c (Fintype.card E)) = true) := by
  rw [G5fLevelTest.level_bits_iff G c b initial j hE]
  tauto

#print axioms level_run
#print axioms level_full_iff

end EthInapproximability.CurrentPaper.G5fLevelFull
