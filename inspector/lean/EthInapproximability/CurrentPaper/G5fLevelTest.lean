import EthInapproximability.CurrentPaper.G5fPadCore
import EthInapproximability.CurrentPaper.G5fAccepted
import EthInapproximability.CurrentPaper.EntryUnaryCompare

/-!
# Segment 1, component: the per-level comparator (private lane owner:b-g5-6)

ONE fixed program `testProgram W cost lr lc T rows cols` on ANY bank type `K`: five charged blocks,
sequenced by the admitted `BitMachineRawSequence.program`; each block copies its operands (the admitted
`MatrixStage4ScalarPreparationOps.copyProgram`, through the blank temporary `W.t`) into the blank
operand cells `W.a`, `W.b` (or pushes unary `1` into `W.b`) and runs the admitted comparator
`EntryUnaryCompare.program`, which pushes its verdict bit on the verdict cell `W.O` and blanks `W.a`,
`W.b`. Exit bank EXACT: `update S W.O (v₅ :: v₄ :: v₃ :: v₂ :: v₁ :: S W.O)`, every other cell
unchanged. The five bits are, in order of pushing,
`cost ≤ T`, `lr ≤ T`, `lc ≤ T`, `2 ≤ rows`, `2 ≤ cols` (`bits_true_iff`).

With `cost = y_j + j`, `lr = clog rows_j`, `lc = clog cols_j`, `T = 2^(Sstar b c |E|)` these are exactly
the level-dependent conjuncts of `G5fAccepted.accepted_run_iff_threshold` (`level_bits_iff`).

NOT here: the computation of `lr`, `lc` (clog with a cleaned scratch) and of the threshold word `T`;
the integration of this comparator into the k-round loop; the front.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5fLevelTest

open Turing BitMachineEncoding

variable {K : Type}

/-- The work cells: comparison operands `a b`, copy temporary `t`, verdict log `O`. -/
structure Cells (K : Type) where
  a : K
  b : K
  t : K
  O : K
  nd : [a, b, t, O].Nodup

namespace Cells
variable (W : Cells K)
theorem ab : W.a ≠ W.b := by have := W.nd; simp_all [List.nodup_cons]
theorem at' : W.a ≠ W.t := by have := W.nd; simp_all [List.nodup_cons]
theorem aO : W.a ≠ W.O := by have := W.nd; simp_all [List.nodup_cons]
theorem bt : W.b ≠ W.t := by have := W.nd; simp_all [List.nodup_cons]
theorem bO : W.b ≠ W.O := by have := W.nd; simp_all [List.nodup_cons]
theorem tO : W.t ≠ W.O := by have := W.nd; simp_all [List.nodup_cons]
end Cells

variable [DecidableEq K]

/-- A source cell outside the work cells. -/
def Out (W : Cells K) (x : K) : Prop := x ≠ W.a ∧ x ≠ W.b ∧ x ≠ W.t ∧ x ≠ W.O

/-- Two-source block: `verdict lt eq gt |x| |y|` pushed on `O`. -/
def blk2 (W : Cells K) (x y : K) (hx : Out W x) (hy : Out W y) (lt eq gt : Bool) :=
  BitMachineRawSequence.program (G5fPadCore.cp3 x W.a W.t hx.1 hx.2.2.1 W.at')
    (BitMachineRawSequence.program (G5fPadCore.cp3 y W.b W.t hy.2.1 hy.2.2.1 W.bt)
      (EntryUnaryCompare.program W.a W.b W.O lt eq gt) EntryUnaryCompare.CL.loop none (none, none))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none (none, (none, none))

/-- Push unary `1` into the blank operand `b`. -/
def oneP (W : Cells K) : Unit → TM2.Stmt (fun _ : K => Bool) Unit Unit :=
  fun _ => .push W.b (fun _ => true) .halt

theorem oneP_run (W : Cells K) (S : K → List Bool) :
    ((advance (oneP W))^[1]) (⟨some (), (), S⟩ : TM2.Cfg (fun _ : K => Bool) Unit Unit) =
      ⟨none, (), Function.update S W.b (true :: S W.b)⟩ := rfl

/-- One-source block: `verdict lt eq gt |x| 1` pushed on `O`. -/
def blk1 (W : Cells K) (x : K) (hx : Out W x) (lt eq gt : Bool) :=
  BitMachineRawSequence.program (G5fPadCore.cp3 x W.a W.t hx.1 hx.2.2.1 W.at')
    (BitMachineRawSequence.program (oneP W)
      (EntryUnaryCompare.program W.a W.b W.O lt eq gt) EntryUnaryCompare.CL.loop () (none, none))
    (BitMachineRawSequence.leftLabel ()) none ((), (none, none))

theorem final_eq (W : Cells K) (S : K → List Bool) (ha : S W.a = []) (hb : S W.b = [])
    (u w : List Bool) (v : Bool) :
    Function.update (Function.update (Function.update (Function.update
      (Function.update S W.a u) W.b w) W.a []) W.b []) W.O (v :: S W.O) =
      Function.update S W.O (v :: S W.O) := by
  funext z
  by_cases hzO : z = W.O
  · subst hzO; simp only [Function.update_self]
  · rw [Function.update_of_ne hzO, Function.update_of_ne hzO]
    by_cases hzb : z = W.b
    · subst hzb; rw [Function.update_self, hb]
    · rw [Function.update_of_ne hzb]
      by_cases hza : z = W.a
      · subst hza; rw [Function.update_self, ha]
      · rw [Function.update_of_ne hza, Function.update_of_ne hzb, Function.update_of_ne hza]

theorem blk2_run (W : Cells K) (x y : K) (hx : Out W x) (hy : Out W y) (lt eq gt : Bool)
    (S : K → List Bool) (m n : ℕ) (hxS : S x = List.replicate m true)
    (hyS : S y = List.replicate n true) (ha : S W.a = []) (hb : S W.b = []) (ht : S W.t = []) :
    ∃ u ≤ (2 * m + 2) + ((2 * n + 2) + (max m n + 2) + 1) + 1, ∃ w,
      ((advance (blk2 W x y hx hy lt eq gt))^[u])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, (none, (none, none))), S⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, (none, (none, w)),
          Function.update S W.O (EntryUnaryCompare.verdict lt eq gt m n :: S W.O)⟩ := by
  have s1 := G5fPadCore.cp3_run x W.a W.t hx.1 hx.2.2.1 W.at' S ha ht
  rw [hxS, List.length_replicate] at s1
  set S1 := Function.update S W.a (List.replicate m true) with hS1
  have s2 := G5fPadCore.cp3_run y W.b W.t hy.2.1 hy.2.2.1 W.bt S1
    (by rw [hS1, Function.update_of_ne (Ne.symm W.ab)]; exact hb)
    (by rw [hS1, Function.update_of_ne (Ne.symm W.at')]; exact ht)
  have e2 : S1 y = List.replicate n true := by
    rw [hS1, Function.update_of_ne hy.1]; exact hyS
  rw [e2, List.length_replicate] at s2
  set S2 := Function.update S1 W.b (List.replicate n true) with hS2
  obtain ⟨t3, ht3, w, s3⟩ := EntryUnaryCompare.compare_run W.a W.b W.O W.ab W.aO W.bO lt eq gt S2
    (none, none) m n
    (by rw [hS2, Function.update_of_ne W.ab, hS1, Function.update_self])
    (by rw [hS2, Function.update_self])
  have eO : S2 W.O = S W.O := by
    rw [hS2, hS1, Function.update_of_ne (Ne.symm W.bO), Function.update_of_ne (Ne.symm W.aO)]
  rw [eO, hS2, hS1, final_eq W S ha hb] at s3
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs _ _ BitMachineCopy.Label.scan
    EntryUnaryCompare.CL.loop none none (none, none) w _ _ _ _ _ s2 s3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs _ _ BitMachineCopy.Label.scan _ none none
    _ _ _ _ _ _ _ s1 r2
  exact ⟨u1, by omega, w, r1⟩

theorem blk1_run (W : Cells K) (x : K) (hx : Out W x) (lt eq gt : Bool)
    (S : K → List Bool) (m : ℕ) (hxS : S x = List.replicate m true)
    (ha : S W.a = []) (hb : S W.b = []) (ht : S W.t = []) :
    ∃ u ≤ (2 * m + 2) + (1 + (max m 1 + 2) + 1) + 1, ∃ w,
      ((advance (blk1 W x hx lt eq gt))^[u])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, ((), (none, none))), S⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, (none, ((), w)),
          Function.update S W.O (EntryUnaryCompare.verdict lt eq gt m 1 :: S W.O)⟩ := by
  have s1 := G5fPadCore.cp3_run x W.a W.t hx.1 hx.2.2.1 W.at' S ha ht
  rw [hxS, List.length_replicate] at s1
  set S1 := Function.update S W.a (List.replicate m true) with hS1
  have s2 := oneP_run W S1
  have e2 : S1 W.b = [] := by rw [hS1, Function.update_of_ne (Ne.symm W.ab)]; exact hb
  rw [e2] at s2
  set S2 := Function.update S1 W.b [true] with hS2
  obtain ⟨t3, ht3, w, s3⟩ := EntryUnaryCompare.compare_run W.a W.b W.O W.ab W.aO W.bO lt eq gt S2
    (none, none) m 1
    (by rw [hS2, Function.update_of_ne W.ab, hS1, Function.update_self])
    (by rw [hS2, Function.update_self]; rfl)
  have eO : S2 W.O = S W.O := by
    rw [hS2, hS1, Function.update_of_ne (Ne.symm W.bO), Function.update_of_ne (Ne.symm W.aO)]
  rw [eO, hS2, hS1, final_eq W S ha hb] at s3
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs (oneP W) _ () EntryUnaryCompare.CL.loop
    () () (none, none) w _ _ _ _ _ s2 s3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs _ _ BitMachineCopy.Label.scan _ none none
    _ _ _ _ _ _ _ s1 r2
  exact ⟨u1, by omega, w, r1⟩

/-- The source cells of the per-level test, all outside the work cells. -/
structure Srcs (W : Cells K) where
  cost : K
  lr : K
  lc : K
  T : K
  rows : K
  cols : K
  hcost : Out W cost
  hlr : Out W lr
  hlc : Out W lc
  hT : Out W T
  hrows : Out W rows
  hcols : Out W cols

def c2 : Option Bool × (Option Bool × EntryUnaryCompare.CV) := (none, (none, (none, none)))
def c1 : Option Bool × (Unit × EntryUnaryCompare.CV) := (none, ((), (none, none)))

/-- ONE fixed program: five blocks. -/
def testProgram (W : Cells K) (X : Srcs W) :=
  BitMachineRawSequence.program (blk2 W X.cost X.T X.hcost X.hT true true false)
    (BitMachineRawSequence.program (blk2 W X.lr X.T X.hlr X.hT true true false)
      (BitMachineRawSequence.program (blk2 W X.lc X.T X.hlc X.hT true true false)
        (BitMachineRawSequence.program (blk1 W X.rows X.hrows false false true)
          (blk1 W X.cols X.hcols false false true)
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) c1 c1)
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)) c2 (c1, c1))
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)) c2 (c2, (c1, c1)))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)) c2 (c2, (c2, (c1, c1)))

theorem upd_upd_O (W : Cells K) (S : K → List Bool) (u v : List Bool) :
    Function.update (Function.update S W.O u) W.O v = Function.update S W.O v :=
  Function.update_idem _ _ _

/-- **The per-level comparator run.** Exact exit bank; clock linear in the operand lengths. -/
theorem test_run (W : Cells K) (X : Srcs W) (S : K → List Bool)
    (cost lr lc T rows cols : ℕ)
    (h1 : S X.cost = List.replicate cost true) (h2 : S X.lr = List.replicate lr true)
    (h3 : S X.lc = List.replicate lc true) (h4 : S X.T = List.replicate T true)
    (h5 : S X.rows = List.replicate rows true) (h6 : S X.cols = List.replicate cols true)
    (ha : S W.a = []) (hb : S W.b = []) (ht : S W.t = []) :
    ∃ u ≤ 10 * (cost + lr + lc + 3 * T + rows + cols) + 100, ∃ w,
      ((advance (testProgram W X))^[u])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          (c2, (c2, (c2, (c1, c1)))), S⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, (c2, (c2, (c2, (c1, w)))),
          Function.update S W.O
            (EntryUnaryCompare.verdict false false true cols 1 ::
              EntryUnaryCompare.verdict false false true rows 1 ::
              EntryUnaryCompare.verdict true true false lc T ::
              EntryUnaryCompare.verdict true true false lr T ::
              EntryUnaryCompare.verdict true true false cost T :: S W.O)⟩ := by
  have hOa : W.a ≠ W.O := W.aO
  have hOb : W.b ≠ W.O := W.bO
  have hOt : W.t ≠ W.O := W.tO
  have keep : ∀ (S' : K → List Bool) (z : K) (u : List Bool), z ≠ W.O →
      Function.update S' W.O u z = S' z := fun S' z u h => Function.update_of_ne h _ _
  obtain ⟨u1, hu1, w1, r1⟩ := blk2_run W X.cost X.T X.hcost X.hT true true false S cost T h1 h4
    ha hb ht
  set S1 := Function.update S W.O (EntryUnaryCompare.verdict true true false cost T :: S W.O)
    with hS1
  obtain ⟨u2, hu2, w2, r2⟩ := blk2_run W X.lr X.T X.hlr X.hT true true false S1 lr T
    (by rw [hS1, keep _ _ _ X.hlr.2.2.2]; exact h2) (by rw [hS1, keep _ _ _ X.hT.2.2.2]; exact h4)
    (by rw [hS1, keep _ _ _ hOa]; exact ha) (by rw [hS1, keep _ _ _ hOb]; exact hb)
    (by rw [hS1, keep _ _ _ hOt]; exact ht)
  rw [hS1, upd_upd_O, Function.update_self] at r2
  set S2 := Function.update S W.O (EntryUnaryCompare.verdict true true false lr T ::
    EntryUnaryCompare.verdict true true false cost T :: S W.O) with hS2
  obtain ⟨u3, hu3, w3, r3⟩ := blk2_run W X.lc X.T X.hlc X.hT true true false S2 lc T
    (by rw [hS2, keep _ _ _ X.hlc.2.2.2]; exact h3) (by rw [hS2, keep _ _ _ X.hT.2.2.2]; exact h4)
    (by rw [hS2, keep _ _ _ hOa]; exact ha) (by rw [hS2, keep _ _ _ hOb]; exact hb)
    (by rw [hS2, keep _ _ _ hOt]; exact ht)
  rw [hS2, upd_upd_O, Function.update_self] at r3
  set S3 := Function.update S W.O (EntryUnaryCompare.verdict true true false lc T ::
    EntryUnaryCompare.verdict true true false lr T ::
    EntryUnaryCompare.verdict true true false cost T :: S W.O) with hS3
  obtain ⟨u4, hu4, w4, r4⟩ := blk1_run W X.rows X.hrows false false true S3 rows
    (by rw [hS3, keep _ _ _ X.hrows.2.2.2]; exact h5)
    (by rw [hS3, keep _ _ _ hOa]; exact ha) (by rw [hS3, keep _ _ _ hOb]; exact hb)
    (by rw [hS3, keep _ _ _ hOt]; exact ht)
  rw [hS3, upd_upd_O, Function.update_self] at r4
  set S4 := Function.update S W.O (EntryUnaryCompare.verdict false false true rows 1 ::
    EntryUnaryCompare.verdict true true false lc T ::
    EntryUnaryCompare.verdict true true false lr T ::
    EntryUnaryCompare.verdict true true false cost T :: S W.O) with hS4
  obtain ⟨u5, hu5, w5, r5⟩ := blk1_run W X.cols X.hcols false false true S4 cols
    (by rw [hS4, keep _ _ _ X.hcols.2.2.2]; exact h6)
    (by rw [hS4, keep _ _ _ hOa]; exact ha) (by rw [hS4, keep _ _ _ hOb]; exact hb)
    (by rw [hS4, keep _ _ _ hOt]; exact ht)
  rw [hS4, upd_upd_O, Function.update_self] at r5
  obtain ⟨v4, hv4, q4⟩ := BitMachineRawSequence.runs _ _ _ _ c1 _ c1 _ _ _ _ _ _ r4 r5
  obtain ⟨v3, hv3, q3⟩ := BitMachineRawSequence.runs _ _ _ _ c2 _ (c1, c1) _ _ _ _ _ _ r3 q4
  obtain ⟨v2, hv2, q2⟩ := BitMachineRawSequence.runs _ _ _ _ c2 _ (c2, (c1, c1)) _ _ _ _ _ _ r2 q3
  obtain ⟨v1, hv1, q1⟩ := BitMachineRawSequence.runs _ _ _ _ c2 _ (c2, (c2, (c1, c1))) _ _ _ _ _ _
    r1 q2
  refine ⟨v1, ?_, (none, ((), w5)), q1⟩
  have m1 : max cost T ≤ cost + T := by omega
  have m2 : max lr T ≤ lr + T := by omega
  have m3 : max lc T ≤ lc + T := by omega
  have m4 : max rows 1 ≤ rows + 1 := by omega
  have m5 : max cols 1 ≤ cols + 1 := by omega
  omega

/-- The two verdict shapes. -/
theorem verdict_le (m n : ℕ) : EntryUnaryCompare.verdict true true false m n = true ↔ m ≤ n := by
  unfold EntryUnaryCompare.verdict
  split_ifs <;> simp <;> omega

theorem verdict_two_le (m : ℕ) : EntryUnaryCompare.verdict false false true m 1 = true ↔ 2 ≤ m := by
  unfold EntryUnaryCompare.verdict
  split_ifs <;> simp <;> omega

/-- The five pushed bits are all `true` iff the five comparisons hold. -/
theorem bits_true_iff (cost lr lc T rows cols : ℕ) :
    (EntryUnaryCompare.verdict false false true cols 1 = true ∧
      EntryUnaryCompare.verdict false false true rows 1 = true ∧
      EntryUnaryCompare.verdict true true false lc T = true ∧
      EntryUnaryCompare.verdict true true false lr T = true ∧
      EntryUnaryCompare.verdict true true false cost T = true) ↔
    (cost ≤ T ∧ lr ≤ T ∧ lc ≤ T ∧ 2 ≤ rows ∧ 2 ≤ cols) := by
  simp only [verdict_le, verdict_two_le]
  tauto

/-- At a level of the physical run, with the level's words and the threshold word, the five bits are
all `true` iff that level passes the level-dependent part of `Accepted`. -/
theorem level_bits_iff {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (c b : ℕ)
    (initial : Iteration.State) (j : ℕ) (hE : 1 ≤ Fintype.card E) :
    Parameters.Accepted (EffectiveIteration.runParameters G c b initial j) ↔
      (G5fAccepted.Good b c (Fintype.card E) 0 ∧ 2 ^ 24 ≤ G5fAccepted.Sstar b c (Fintype.card E) ∧
        c ≤ 2 ^ G5fAccepted.Sstar b c (Fintype.card E) ∧
        b ≤ 2 ^ G5fAccepted.Sstar b c (Fintype.card E) ∧
        Nat.clog 2 (Fintype.card E + 2) ≤ 2 ^ G5fAccepted.Sstar b c (Fintype.card E)) ∧
      (EntryUnaryCompare.verdict false false true (Iteration.run G c b initial j).matrix.columns 1 = true ∧
        EntryUnaryCompare.verdict false false true (Iteration.run G c b initial j).matrix.rows 1 = true ∧
        EntryUnaryCompare.verdict true true false
          (Nat.clog 2 (Iteration.run G c b initial j).matrix.columns)
          (2 ^ G5fAccepted.Sstar b c (Fintype.card E)) = true ∧
        EntryUnaryCompare.verdict true true false
          (Nat.clog 2 (Iteration.run G c b initial j).matrix.rows)
          (2 ^ G5fAccepted.Sstar b c (Fintype.card E)) = true ∧
        EntryUnaryCompare.verdict true true false ((Iteration.run G c b initial j).budget + j)
          (2 ^ G5fAccepted.Sstar b c (Fintype.card E)) = true) := by
  rw [G5fAccepted.accepted_run_iff_threshold G c b initial j hE, bits_true_iff]
  tauto

#print axioms oneP_run
#print axioms final_eq
#print axioms blk2_run
#print axioms blk1_run
#print axioms test_run
#print axioms bits_true_iff
#print axioms level_bits_iff

end EthInapproximability.CurrentPaper.G5fLevelTest
