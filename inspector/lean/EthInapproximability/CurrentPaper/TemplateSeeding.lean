import EthInapproximability.CurrentPaper.EntryLayout
import EthInapproximability.CurrentPaper.CopyFill
import EthInapproximability.CurrentPaper.MoveFill
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-!
# Segment 2 (template branch): the physical per-address seeding program

Lane owner:b-stage4-entry-program-4 (Paper B, unit 2, map item 3).

ONE fixed five-phase controller (four charged handoffs) from the per-address
start bank `EntryLayout.start w x y ans` (common words, unary row index `x`,
unary column index `y`, answer cell `ans`, every region blank) to the bank
whose template region is EXACTLY the checked template seed
`TemplateSeed.seed y (binB^(s-1-x/L)) (x % L) …` and whose every other cell
equals the start bank:

1. seventeen source-preserving charged copies (`CopyFill`): `x`, `L` into
   the division region, `y` (column code) into `columnSlot 0`, `binBase`
   and `s` into the stride region, and the fourteen common words into their
   admitted template cells;
2. the admitted `MatrixUnaryDivision.program` (`division_total_run`) on the
   division region: `x % L`, `x / L`;
3. three charged moves: `x % L` into `entrySlot 0` (`ell`), `x / L` into the
   stride `p` cell, clear of the divisor copy;
4. the checked `EntryStride.program` (`stride_run`) on the stride region:
   `binBase^(s-1-x/L)`;
5. four charged moves: the stride word into `columnSlot 2`, clears of the
   three stride operands.

The address words are produced from `x`, `y` only; nothing is inserted.
-/

set_option maxRecDepth 16384

namespace EthInapproximability.CurrentPaper.TemplateSeeding

open Turing BitMachineEncoding BitMachineStackEmbedding EntryLayout CopyFill

/-! ## Template cells (the admitted `TemplateSeed.seed` addresses) -/

def cc (i : MatrixStage4ColumnMachine.Stack) : TS := .inl (.inl (.inl (.inl (.inl (.inl (.inl i))))))
def ce (i : Fin 5) : TS := .inl (.inl (.inl (.inl (.inl (.inl (.inr i))))))
def tq1 : TS := .inl (.inl (.inl (.inl (.inl (.inr 0)))))
def tft : TS := .inl (.inl (.inl (.inl (.inr 0))))
def tq2 : TS := .inl (.inl (.inl (.inl (.inr 2))))
def tx (i : Fin 24) : TS := .inl (.inl (.inr i))
def trx1 : TS := .inl (.inr (.inl (.inl (.inr 0))))
def trt : TS := .inl (.inr (.inl (.inr 0)))
def trx2 : TS := .inl (.inr (.inl (.inr 2)))
def tl (i : Fin 8) : TS := .inr i

/-! ## Stage banks -/

def bankT (w : Words) (x y : ℕ) (ans : List Bool) (T : TS → List Bool)
    (D : Fin 6 → List Bool) (Sk : EntryStride.SK → List Bool) : ES → List Bool :=
  Sum.elim (common w) (Sum.elim ![rep x, rep y, ans]
    (Sum.elim T (Sum.elim (fun _ => []) (Sum.elim D (Sum.elim Sk (fun _ => []))))))

def seedT (w : Words) (y stride ell : ℕ) : TS → List Bool :=
  TemplateSeed.seed y stride ell w.binPowS w.binB w.wordB w.q w.qOne w.firstTable
    w.cy w.firstExp w.cyPowF w.rx w.rowTable w.Rtable

def blank6 : Fin 6 → List Bool := fun _ => []
def blankS : EntryStride.SK → List Bool := fun _ => []

/-- Final bank: the template region holds the exact seed. -/
def seeded (w : Words) (x y : ℕ) (ans : List Bool) : ES → List Bool :=
  Sum.elim (common w) (Sum.elim ![rep x, rep y, ans]
    (Sum.elim (seedT w y (w.binB ^ (w.s - 1 - x / w.L)) (x % w.L)) (fun _ => [])))

theorem start_eq (w : Words) (x y : ℕ) (ans : List Bool) :
    start w x y ans = bankT w x y ans (fun _ => []) blank6 blankS := by
  funext k
  rcases k with k | k | k | k | k | k | k <;> rfl

theorem seeded_eq (w : Words) (x y : ℕ) (ans : List Bool) :
    bankT w x y ans (seedT w y (w.binB ^ (w.s - 1 - x / w.L)) (x % w.L)) blank6 blankS =
      seeded w x y ans := by
  funext k
  rcases k with k | k | k | k | k | k | k <;> rfl

/-! ## Phase 1: seventeen charged copies -/

def jobs1 : List (ES × List ES) :=
  [(xc, [dc 0]), (cw 18, [dc 1]), (yc, [tc (cc 0)]),
   (cw 0, [tc (cc 3), sc (EntryStride.w 0)]), (cw 13, [sc (EntryStride.w 1)]),
   (cw 2, [tc (cc 1)]), (cw 1, [tc (cc 4)]), (cw 3, [tc (ce 1)]),
   (cw 4, [tc tq1, tc tq2]), (cw 5, [tc tft]), (cw 6, [tc (tx 0), tc (tx 12)]),
   (cw 7, [tc (tx 1), tc (tx 11), tc (tl 0)]), (cw 8, [tc (tx 6)]), (cw 9, [tc (tx 10)]),
   (cw 10, [tc trx1, tc trx2]), (cw 11, [tc trt]), (cw 12, [tc (tl 4)])]

def P1 := MultiMove.program (jobs1.map toJob) temp

def D1 (w : Words) (x : ℕ) : Fin 6 → List Bool := ![rep x, rep w.L, [], [], [], []]

theorem good1 : Good temp jobs1 where
  src_not_dst := by
    simp [jobs1, cw, dc, sc, tc, xc, yc, cc, ce, tq1, tq2, tft, tx, trx1, trx2, trt, tl,
      EntryStride.w]
  dst_nodup := by
    simp [jobs1, dc, sc, tc, cc, ce, tq1, tq2, tft, tx, trx1, trx2, trt, tl, EntryStride.w]
  src_temp := by
    simp [jobs1, cw, xc, yc, temp, scr]
  temp_dst := by
    simp [jobs1, dc, sc, tc, temp, scr]

theorem blank1 (w : Words) (x y : ℕ) (ans : List Bool) :
    ∀ j ∈ jobs1, ∀ d ∈ j.2, start w x y ans d = [] := by
  simp [jobs1, dc, sc, tc, start]

theorem fill1 (w : Words) (x y : ℕ) (ans : List Bool) :
    fill jobs1 (start w x y ans) =
      bankT w x y ans (seedT w y 0 0) (D1 w x) (EntryStride.S0 w.binB w.s 0) := by
  funext k
  rcases k with k | k | k | k | k | k | k
  · fin_cases k <;> rfl
  · fin_cases k <;> rfl
  · fin_cases k <;> rfl
  · rfl
  · fin_cases k <;> rfl
  · rcases k with k | k
    · fin_cases k <;> rfl
    · rfl
  · rfl

def cost1 (w : Words) (x y : ℕ) : ℕ :=
  (2 * x + 2) + (2 * w.L + 2) + (2 * y + 2) + (2 * w.binB + 2) + (2 * w.s + 2) +
  (2 * w.binPowS + 2) + (2 * w.wordB + 2) + (2 * w.q + 2) + (2 * w.qOne + 2) +
  (2 * w.firstTable.length + 2) + (2 * 1 + 2) + (2 * w.cy + 2) + (2 * w.firstExp + 2) +
  (2 * w.cyPowF + 2) + (2 * w.rx + 2) + (2 * w.rowTable.length + 2) +
  (2 * w.Rtable.length + 2)

theorem cost1_eq (w : Words) (x y : ℕ) (ans : List Bool) :
    fillCost jobs1 (start w x y ans) = cost1 w x y := by
  simp [fillCost, jobs1, start, common, cw, xc, yc, rep, cost1]
  omega

theorem phase1 (w : Words) (x y : ℕ) (ans : List Bool) :
    ((advance P1)^[cost1 w x y + 1])
      (⟨some (MultiMove.startLabel (jobs1.map toJob)), MultiMove.initial, start w x y ans⟩ :
        TM2.Cfg (fun _ : ES => Bool) _ _) =
      ⟨none, MultiMove.initial,
        bankT w x y ans (seedT w y 0 0) (D1 w x) (EntryStride.S0 w.binB w.s 0)⟩ := by
  have h := CopyFill.run temp jobs1 good1 (start w x y ans) rfl (blank1 w x y ans)
  rw [fill1, cost1_eq] at h
  exact h

#print axioms phase1

/-! ## Phase 2: the admitted unary division on the division region -/

def dEmb : Fin 6 ↪ ES := ⟨dc, fun a b h => by simpa [dc] using h⟩

def P2 := fun l => stackStmt dEmb (MatrixUnaryDivision.program l)

def D2 (w : Words) (x : ℕ) : Fin 6 → List Bool :=
  ![[], rep w.L, [], rep (x % w.L), rep (x / w.L), []]

theorem bank_D (w : Words) (x y : ℕ) (ans : List Bool) (T : TS → List Bool)
    (D : Fin 6 → List Bool) (Sk : EntryStride.SK → List Bool) (D' : Fin 6 → List Bool) :
    bank dEmb (bankT w x y ans T D Sk) D' = bankT w x y ans T D' Sk := by
  funext j
  rcases j with j | j | j | j | j | j | j
  · rw [bank_outside]; · rfl
    · rintro ⟨k, hk⟩; simp [dEmb, dc] at hk
  · rw [bank_outside]; · rfl
    · rintro ⟨k, hk⟩; simp [dEmb, dc] at hk
  · rw [bank_outside]; · rfl
    · rintro ⟨k, hk⟩; simp [dEmb, dc] at hk
  · rw [bank_outside]; · rfl
    · rintro ⟨k, hk⟩; simp [dEmb, dc] at hk
  · exact bank_at dEmb _ D' j
  · rw [bank_outside]; · rfl
    · rintro ⟨k, hk⟩; simp [dEmb, dc] at hk
  · rw [bank_outside]; · rfl
    · rintro ⟨k, hk⟩; simp [dEmb, dc] at hk

theorem phase2 (w : Words) (x y : ℕ) (ans : List Bool) (T : TS → List Bool)
    (Sk : EntryStride.SK → List Bool) :
    ((advance P2)^[MatrixUnaryDivision.totalTime x w.L])
      (⟨some MatrixUnaryDivision.Label.start, false, bankT w x y ans T (D1 w x) Sk⟩ :
        TM2.Cfg (fun _ : ES => Bool) _ _) =
      ⟨none, false, bankT w x y ans T (D2 w x) Sk⟩ := by
  have h := BitMachineStackRun.run dEmb (bankT w x y ans T (D1 w x) Sk)
    MatrixUnaryDivision.program
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate x true)
      (List.replicate w.L true) [] [] [] []) (MatrixUnaryDivision.totalTime x w.L)
  have h2 := MatrixUnaryDivision.division_total_run x w.L
  unfold MatrixUnaryDivision.run at h2
  rw [h2] at h
  have e1 := bank_D w x y ans T (D1 w x) Sk
    ![List.replicate x true, List.replicate w.L true, [], [], [], []]
  have e2 := bank_D w x y ans T (D1 w x) Sk
    ![[], List.replicate w.L true, [], List.replicate (x % w.L) true,
      List.replicate (x / w.L) true, []]
  simp only [stackCfg, MatrixUnaryDivision.cfg] at h
  rw [e1, e2] at h
  exact h

/-! ## Phase 3: three charged moves -/

def mv3 : List (ES × List ES) :=
  [(dc ⟨3, by decide⟩, [tc (ce 0)]), (dc ⟨4, by decide⟩, [sc (EntryStride.w 2)]), (dc 1, [])]

def P3 := MultiMove.program (mv3.map MoveFill.toJob) temp

def B2 (w : Words) (x y : ℕ) (ans : List Bool) : ES → List Bool :=
  bankT w x y ans (seedT w y 0 0) (D2 w x) (EntryStride.S0 w.binB w.s 0)

theorem good3 : MoveFill.Good temp mv3 where
  src_nodup := by simp [mv3, dc]
  src_not_dst := by simp [mv3, dc, tc, sc]
  dst_nodup := by simp [mv3, tc, sc]
  src_temp := by simp [mv3, dc, temp, scr]
  temp_dst := by simp [mv3, tc, sc, temp, scr]

theorem blank3 (w : Words) (x y : ℕ) (ans : List Bool) :
    ∀ j ∈ mv3, ∀ d ∈ j.2, B2 w x y ans d = [] := by
  intro j hj d hd
  simp only [mv3, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd <;> (subst hd; rfl)

def D2g (w : Words) (r q : ℕ) : Fin 6 → List Bool := ![[], rep w.L, [], rep r, rep q, []]

/-- Generalized over the quotient/remainder values (keeps `%`, `/` out of
definitional unification). -/
theorem mfill3g (w : Words) (x y : ℕ) (ans : List Bool) (r q : ℕ) :
    MoveFill.mfill mv3 (bankT w x y ans (seedT w y 0 0) (D2g w r q) (EntryStride.S0 w.binB w.s 0)) =
      bankT w x y ans (seedT w y 0 r) blank6 (EntryStride.S0 w.binB w.s q) := by
  funext k
  rcases k with k | k | k | k | k | k | k
  · fin_cases k <;> ((conv_lhs => whnf); (conv_rhs => whnf))
  · fin_cases k <;> ((conv_lhs => whnf); (conv_rhs => whnf))
  · fin_cases k <;> ((conv_lhs => whnf); (conv_rhs => whnf))
  · ((conv_lhs => whnf); (conv_rhs => whnf))
  · fin_cases k <;> ((conv_lhs => whnf); (conv_rhs => whnf))
  · rcases k with k | k
    · fin_cases k <;> ((conv_lhs => whnf); (conv_rhs => whnf))
    · ((conv_lhs => whnf); (conv_rhs => whnf))
  · ((conv_lhs => whnf); (conv_rhs => whnf))

def cost3 (w : Words) (x : ℕ) : ℕ :=
  (2 * (x % w.L) + 2) + (2 * (x / w.L) + 2) + (2 * w.L + 2)

theorem cost3_eq (w : Words) (x y : ℕ) (ans : List Bool) :
    MoveFill.mfillCost mv3 (B2 w x y ans) = cost3 w x := by
  have e : MoveFill.mfillCost mv3 (B2 w x y ans) =
      (2 * (rep (x % w.L)).length + 2) + ((2 * (rep (x / w.L)).length + 2) +
        ((2 * (rep w.L).length + 2) + 0)) := rfl
  rw [e]
  simp only [rep, List.length_replicate, cost3]
  omega

theorem phase3 (w : Words) (x y : ℕ) (ans : List Bool) :
    ((advance P3)^[cost3 w x + 1])
      (⟨some (MultiMove.startLabel (mv3.map MoveFill.toJob)), MultiMove.initial,
        B2 w x y ans⟩ : TM2.Cfg (fun _ : ES => Bool) _ _) =
      ⟨none, MultiMove.initial, bankT w x y ans (seedT w y 0 (x % w.L)) blank6
        (EntryStride.S0 w.binB w.s (x / w.L))⟩ := by
  have h := MoveFill.run temp mv3 good3 (B2 w x y ans) rfl (blank3 w x y ans)
  have e : MoveFill.mfill mv3 (B2 w x y ans) = bankT w x y ans (seedT w y 0 (x % w.L)) blank6
      (EntryStride.S0 w.binB w.s (x / w.L)) := mfill3g w x y ans (x % w.L) (x / w.L)
  rw [e, cost3_eq] at h
  exact h

/-! ## Phase 4: the checked stride program on the stride region -/

def sEmb : EntryStride.SK ↪ ES := ⟨sc, fun a b h => by simpa [sc] using h⟩

def P4 := fun l => stackStmt sEmb (EntryStride.program l)

theorem bank_S (w : Words) (x y : ℕ) (ans : List Bool) (T : TS → List Bool)
    (D : Fin 6 → List Bool) (Sk Sk' : EntryStride.SK → List Bool) :
    bank sEmb (bankT w x y ans T D Sk) Sk' = bankT w x y ans T D Sk' := by
  funext j
  rcases j with j | j | j | j | j | j | j
  · rw [bank_outside]; · rfl
    · rintro ⟨k, hk⟩; simp [sEmb, sc] at hk
  · rw [bank_outside]; · rfl
    · rintro ⟨k, hk⟩; simp [sEmb, sc] at hk
  · rw [bank_outside]; · rfl
    · rintro ⟨k, hk⟩; simp [sEmb, sc] at hk
  · rw [bank_outside]; · rfl
    · rintro ⟨k, hk⟩; simp [sEmb, sc] at hk
  · rw [bank_outside]; · rfl
    · rintro ⟨k, hk⟩; simp [sEmb, sc] at hk
  · exact bank_at sEmb _ Sk' j
  · rw [bank_outside]; · rfl
    · rintro ⟨k, hk⟩; simp [sEmb, sc] at hk

theorem phase4 (w : Words) (x y : ℕ) (ans : List Bool) (T : TS → List Bool)
    (D : Fin 6 → List Bool) (p : ℕ) :
    ∃ t ≤ EntryStride.strideBound w.binB w.s p, ∃ v,
      ((advance P4)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), EntryStride.initial,
          bankT w x y ans T D (EntryStride.S0 w.binB w.s p)⟩ :
          TM2.Cfg (fun _ : ES => Bool) _ _) =
        ⟨none, v, bankT w x y ans T D (EntryStride.exitBank w.binB w.s p)⟩ := by
  obtain ⟨t, ht, v, hr⟩ := EntryStride.stride_run w.binB w.s p
  refine ⟨t, ht, v, ?_⟩
  have h := BitMachineStackRun.run sEmb (bankT w x y ans T D (EntryStride.S0 w.binB w.s p))
    EntryStride.program
    ⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), EntryStride.initial,
      EntryStride.S0 w.binB w.s p⟩ t
  rw [hr] at h
  simp only [stackCfg] at h
  rw [bank_S, bank_S] at h
  exact h

/-! ## Phase 5: the stride word into `columnSlot 2`, charged clears -/

def mv5 : List (ES × List ES) :=
  [(sc (EntryStride.pw 0), [tc (cc 2)]), (sc (EntryStride.w 0), []),
   (sc (EntryStride.w 1), []), (sc (EntryStride.w 2), [])]

def P5 := MultiMove.program (mv5.map MoveFill.toJob) temp

def B4 (w : Words) (x y : ℕ) (ans : List Bool) (p : ℕ) : ES → List Bool :=
  bankT w x y ans (seedT w y 0 (x % w.L)) blank6 (EntryStride.exitBank w.binB w.s p)

theorem good5 : MoveFill.Good temp mv5 where
  src_nodup := by simp [mv5, sc, EntryStride.w, EntryStride.pw]
  src_not_dst := by simp [mv5, tc, sc]
  dst_nodup := by simp [mv5]
  src_temp := by simp [mv5, sc, temp, scr]
  temp_dst := by simp [mv5, tc, temp, scr]

theorem blank5 (w : Words) (x y : ℕ) (ans : List Bool) (p : ℕ) :
    ∀ j ∈ mv5, ∀ d ∈ j.2, B4 w x y ans p d = [] := by
  intro j hj d hd
  simp only [mv5, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd <;> (subst hd; rfl)

/-- Generalized over the stride value and the remainder. -/
theorem mfill5g (w : Words) (x y : ℕ) (ans : List Bool) (p r st : ℕ) :
    MoveFill.mfill mv5 (bankT w x y ans (seedT w y 0 r) blank6
      (Function.update (EntryStride.S0 w.binB w.s p) (EntryStride.pw 0) (rep st))) =
      bankT w x y ans (seedT w y st r) blank6 blankS := by
  funext k
  rcases k with k | k | k | k | k | k | k
  · fin_cases k <;> ((conv_lhs => whnf); (conv_rhs => whnf))
  · fin_cases k <;> ((conv_lhs => whnf); (conv_rhs => whnf))
  · fin_cases k <;> ((conv_lhs => whnf); (conv_rhs => whnf))
  · ((conv_lhs => whnf); (conv_rhs => whnf))
  · fin_cases k <;> ((conv_lhs => whnf); (conv_rhs => whnf))
  · rcases k with k | k | k
    · fin_cases k <;> ((conv_lhs => whnf); (conv_rhs => whnf))
    · fin_cases k <;> ((conv_lhs => whnf); (conv_rhs => whnf))
    · fin_cases k <;> ((conv_lhs => whnf); (conv_rhs => whnf))
  · ((conv_lhs => whnf); (conv_rhs => whnf))

def cost5 (w : Words) (p : ℕ) : ℕ :=
  (2 * w.binB ^ (w.s - 1 - p) + 2) + (2 * w.binB + 2) + (2 * w.s + 2) + (2 * p + 2)

theorem cost5_eq (w : Words) (x y : ℕ) (ans : List Bool) (p : ℕ) :
    MoveFill.mfillCost mv5 (B4 w x y ans p) = cost5 w p := by
  have e : MoveFill.mfillCost mv5 (B4 w x y ans p) =
      (2 * (rep (w.binB ^ (w.s - 1 - p))).length + 2) + ((2 * (rep w.binB).length + 2) +
        ((2 * (rep w.s).length + 2) + ((2 * (rep p).length + 2) + 0))) := rfl
  rw [e]
  simp only [rep, List.length_replicate, cost5]
  omega

theorem phase5 (w : Words) (x y : ℕ) (ans : List Bool) (p : ℕ) :
    ((advance P5)^[cost5 w p + 1])
      (⟨some (MultiMove.startLabel (mv5.map MoveFill.toJob)), MultiMove.initial,
        B4 w x y ans p⟩ : TM2.Cfg (fun _ : ES => Bool) _ _) =
      ⟨none, MultiMove.initial,
        bankT w x y ans (seedT w y (w.binB ^ (w.s - 1 - p)) (x % w.L)) blank6 blankS⟩ := by
  have h := MoveFill.run temp mv5 good5 (B4 w x y ans p) rfl (blank5 w x y ans p)
  have e : MoveFill.mfill mv5 (B4 w x y ans p) =
      bankT w x y ans (seedT w y (w.binB ^ (w.s - 1 - p)) (x % w.L)) blank6 blankS :=
    mfill5g w x y ans p (x % w.L) (w.binB ^ (w.s - 1 - p))
  rw [e, cost5_eq] at h
  exact h

/-! ## The single fixed five-phase controller -/

def q4 := BitMachineRawSequence.program P4 P5 (MultiMove.startLabel (mv5.map MoveFill.toJob))
  EntryStride.initial MultiMove.initial
def q3 := BitMachineRawSequence.program P3 q4
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
  MultiMove.initial (EntryStride.initial, MultiMove.initial)
def q2 := BitMachineRawSequence.program P2 q3
  (BitMachineRawSequence.leftLabel (MultiMove.startLabel (mv3.map MoveFill.toJob))) false
  (MultiMove.initial, (EntryStride.initial, MultiMove.initial))
/-- ONE fixed template seeding controller. -/
def program := BitMachineRawSequence.program P1 q2
  (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start) MultiMove.initial
  (false, (MultiMove.initial, (EntryStride.initial, MultiMove.initial)))
def initial := (MultiMove.initial, (false, (MultiMove.initial, (EntryStride.initial,
  MultiMove.initial))))

/-- Public per-address bound (explicit in the unary words). -/
def templateCost (w : Words) (x y : ℕ) : ℕ :=
  (cost1 w x y + 1) + MatrixUnaryDivision.totalTime x w.L + (cost3 w x + 1) +
    EntryStride.strideBound w.binB w.s (x / w.L) + (cost5 w (x / w.L) + 1) + 4

/-- The template seeding run: one fixed controller, exact exit bank (only the
template region changes, to the exact admitted seed), exact final control. -/
theorem template_seeding (w : Words) (x y : ℕ) (ans : List Bool) :
    ∃ t ≤ templateCost w x y,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobs1.map toJob))),
          initial, start w x y ans⟩ : TM2.Cfg (fun _ : ES => Bool) _ _) =
        ⟨none, initial, seeded w x y ans⟩ := by
  obtain ⟨t4, ht4, v4, h4⟩ := phase4 w x y ans (seedT w y 0 (x % w.L)) blank6 (x / w.L)
  have h5 := phase5 w x y ans (x / w.L)
  obtain ⟨u4, hu4, r4⟩ := BitMachineRawSequence.runs P4 P5 _ _ _ _ _ _ _
    (B4 w x y ans (x / w.L)) _ _ _ h4 h5
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs P3 q4 _ _ _ _ _ _ _ _ _ _ _
    (phase3 w x y ans) r4
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs P2 q3 _ _ _ _ _ _ _
    (B2 w x y ans) _ _ _ (phase2 w x y ans (seedT w y 0 0) (EntryStride.S0 w.binB w.s 0)) r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs P1 q2 _ _ _ _ _ _ _ _ _ _ _
    (phase1 w x y ans) r2
  refine ⟨u1, ?_, ?_⟩
  · unfold templateCost
    omega
  · rw [← seeded_eq]
    exact r1

#print axioms template_seeding

#print axioms phase2
#print axioms phase3
#print axioms phase4
#print axioms phase5

end EthInapproximability.CurrentPaper.TemplateSeeding
