import Paper2.SeedBitEntry
import Paper2.LIdent
import Paper2.FrontClockA
import EthInapproximability.CurrentPaper.MatrixTableWriter
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
# WP-SEED: one fixed bit machine printing the full `cl:seed` truth table from unary `n`

Lane `owner:a-seed-t45-1` (private, 26 September 2026). Lock v12 `cl:seed` (IA:677-692):
"If L = ⌈log n⌉ for an integer n ≥ 4, both input sets and the full truth table can be constructed
in polynomial time in n."

ONE fixed program on the bank `J = MatrixTableWriter.Stack KB` (`KB = card LK + 3`), four parts
joined by three charged `BitMachineRawSequence` handoffs:

1. the admitted producer `LProducer.lProg` (embedded in the first `card LK` bank cells): from unary
   `n` it produces unary `p = LookupSeed.width (clog₂ n)` (`LProducer.l_run`, `LProducer.p_eq`);
2. the admitted unary power `MatrixStage4ScalarPreparationOps.unaryPowerProgram`: unary `2^p`
   into the writer's row-count stack;
3. the admitted copy `MatrixStage4ScalarPreparationOps.copyProgram`: unary `p` into the writer's
   column-count stack;
4. the admitted row-major writer `MatrixTableWriter.program` with the private entry program
   `SeedBitEntry` (bit `j` of the unary row index `k`) on three blank bank cells.

Row `k < 2^p` is the Boolean word `seedRow p k = (j ↦ testBit k j)`; `seedRow p` is a bijection
`Fin (2^p) ≃ (Fin p → Bool)` (`seedRow_bijective`), so the rows are exactly the row input set
`{0,1}^p`, and the printed word is `MatrixMaterialization.rowMajor` of the actual
`LookupSeed.matrix p`. Every step is charged; the only inputs are the unary `n` on the input stack.
-/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384

namespace SeedT45.SeedTable

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

abbrev LK := Paper2.LProducer.LK

abbrev KB : ℕ := Fintype.card LK + 3

abbrev J := MatrixTableWriter.Stack KB

def eL : LK ≃ Fin (Fintype.card LK) := Fintype.equivFin LK

def ιLf (k : LK) : J := .inl (.inl (Fin.castAdd 3 (eL k)))

theorem ιLf_injective : Function.Injective ιLf := by
  intro a b h
  simp only [ιLf, Sum.inl.injEq] at h
  exact eL.injective (Fin.castAdd_injective _ _ h)

def ιL : LK ↪ J := ⟨ιLf, ιLf_injective⟩

theorem ιL_apply (k : LK) : ιL k = .inl (.inl (Fin.castAdd 3 (eL k))) := rfl

/-- The three scratch cells of the entry program. -/
def scr (i : Fin 3) : Fin KB := Fin.natAdd (Fintype.card LK) i

theorem not_ιL_scr (i : Fin 3) : ¬ ∃ k, ιL k = (.inl (.inl (scr i)) : J) := by
  rintro ⟨k, hk⟩
  simp only [ιL_apply, scr, Sum.inl.injEq] at hk
  have h2 := congrArg Fin.val hk
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
  have := (eL k).isLt
  omega

theorem not_ιL_cell (i : Fin 3) : ¬ ∃ k, ιL k = (.inl (.inr i) : J) := by
  rintro ⟨k, hk⟩
  simp [ιL_apply] at hk

theorem not_ιL_extra (e : MatrixTableWriter.Extra) : ¬ ∃ k, ιL k = (.inr e : J) := by
  rintro ⟨k, hk⟩
  simp [ιL_apply] at hk

/-! ## The entry program on the writer's cell bank -/

abbrev CS := MatrixTableWriter.CellStack KB

def ιEf : Fin 6 → CS :=
  ![.inr 0, .inr 1, .inr 2, .inl (scr 0), .inl (scr 1), .inl (scr 2)]

theorem ιEf_injective : Function.Injective ιEf := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; revert h; simp [ιEf, scr, Fin.ext_iff])

def ιE : Fin 6 ↪ CS := ⟨ιEf, ιEf_injective⟩

def Pent : BitEntry.Label → TM2.Stmt (fun _ : CS => Bool) BitEntry.Label BitEntry.Ctl :=
  fun l => stackStmt ιE (BitEntry.program l)

theorem entryTime_mono {x y r c : ℕ} (hx : x ≤ r) (hy : y ≤ c) :
    BitEntry.entryTime x y ≤ BitEntry.entryTime r c := by
  unfold BitEntry.entryTime
  have : y * (2 * x + 3) ≤ c * (2 * r + 3) := Nat.mul_le_mul hy (by omega)
  omega

theorem entry_runs (bank : Fin KB → List Bool) (hb : ∀ i, bank (scr i) = []) (r c : ℕ) :
    MatrixTableWriter.EntryRuns Pent .cpx (none, false) bank r c (BitEntry.entryTime r c)
      (fun x y => Nat.testBit x y) := by
  intro x hx y hy
  obtain ⟨t, ht, v, hr⟩ := BitEntry.entry_run x y
  let foreign : CS → List Bool :=
    Sum.elim bank (![List.replicate x true, List.replicate y true, []] : Fin 3 → List Bool)
  have hs := BitMachineStackRun.run ιE foreign BitEntry.program
    (BitEntry.cfg (some .cpx) (none, false) (BitEntry.u x) (BitEntry.u y) [] [] [] []) t
  change _ = stackCfg ιE foreign (BitEntry.run t _) at hs
  rw [hr] at hs
  have hstart : stackCfg ιE foreign
      (BitEntry.cfg (some .cpx) (none, false) (BitEntry.u x) (BitEntry.u y) [] [] [] []) =
      MatrixTableWriter.cellCfg (some .cpx) (none, false) bank x y [] := by
    simp only [stackCfg, BitEntry.cfg, MatrixTableWriter.cellCfg]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [foreign, ιE, ιEf, BitEntry.u, hb]
  have hend : stackCfg ιE foreign
      (BitEntry.cfg none v (BitEntry.u x) (BitEntry.u y) [Nat.testBit x y] [] [] []) =
      MatrixTableWriter.cellCfg none v bank x y [Nat.testBit x y] := by
    simp only [stackCfg, BitEntry.cfg, MatrixTableWriter.cellCfg]
    congr 1
    funext j
    by_cases h : ∃ k, ιE k = j
    · obtain ⟨k, rfl⟩ := h
      rw [bank_at]
      fin_cases k <;> simp [ιE, ιEf, BitEntry.u, hb]
    · rw [bank_outside _ _ _ _ h]
      rcases j with i | i
      · rfl
      · exfalso
        fin_cases i
        · exact h ⟨0, rfl⟩
        · exact h ⟨1, rfl⟩
        · exact h ⟨2, rfl⟩
  rw [hstart, hend] at hs
  exact ⟨t, ht.trans (entryTime_mono hx.le hy.le), v, hs⟩

/-! ## The four parts and the one fixed program -/

theorem ιL_eq_iff (a b : LK) : ιL a = ιL b ↔ a = b := ιL.injective.eq_iff

theorem ιL_ne_inr (k : LK) (e : MatrixTableWriter.Extra) : ιL k ≠ (.inr e : J) :=
  fun h => not_ιL_extra e ⟨k, h⟩

abbrev rowsC : J := .inr .rows
abbrev colsC : J := .inr .cols
abbrev outC : J := .inr .output

def S1 := fun l => stackStmt ιL (Paper2.LProducer.lProg l)

def ιPf : MatrixUnaryPower.Stack → J
  | .inl 0 => rowsC
  | .inl 1 => ιL Paper2.LProducer.x1
  | .inl _ => ιL Paper2.LProducer.x2
  | .inr () => ιL Paper2.LProducer.pC

theorem ιPf_injective : Function.Injective ιPf := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · fin_cases a <;> fin_cases b <;>
      first | rfl | (exfalso; revert h; simp [ιPf, rowsC, ιL_eq_iff, ιL_ne_inr,
        (ιL_ne_inr _ _).symm, Paper2.LProducer.c])
  · cases b; fin_cases a <;> (exfalso; revert h; simp [ιPf, rowsC, ιL_eq_iff, ιL_ne_inr,
        (ιL_ne_inr _ _).symm, Paper2.LProducer.c])
  · cases a; fin_cases b <;> (exfalso; revert h; simp [ιPf, rowsC, ιL_eq_iff, ιL_ne_inr,
        (ιL_ne_inr _ _).symm, Paper2.LProducer.c])
  · cases a; cases b; rfl

def ιP : MatrixUnaryPower.Stack ↪ J := ⟨ιPf, ιPf_injective⟩

def S2 := MatrixStage4ScalarPreparationOps.unaryPowerProgram ιP

def ιCf : Fin 3 → J := ![ιL Paper2.LProducer.pC, colsC, ιL Paper2.LProducer.z]

theorem ιCf_injective : Function.Injective ιCf := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    first | rfl | (exfalso; revert h; simp [ιCf, colsC, ιL_eq_iff, ιL_ne_inr,
      (ιL_ne_inr _ _).symm, Paper2.LProducer.c])

def ιC : Fin 3 ↪ J := ⟨ιCf, ιCf_injective⟩

def S3 := MatrixStage4ScalarPreparationOps.copyProgram ιC

def S4 := MatrixTableWriter.program Pent BitEntry.Label.cpx ((none, false) : BitEntry.Ctl)

def Q12 := BitMachineRawSequence.program S1 S2 (.inr false) Paper2.LProducer.lCtl
  Paper2.LProducer.powCtl

def Q123 := BitMachineRawSequence.program Q12 S3 BitMachineCopy.Label.scan
  (Paper2.LProducer.lCtl, Paper2.LProducer.powCtl) (none : Option Bool)

/-- THE fixed program. -/
def Q := BitMachineRawSequence.program Q123 S4 (.inr (.copy .rows))
  ((Paper2.LProducer.lCtl, Paper2.LProducer.powCtl), (none : Option Bool))
  (((none, false) : BitEntry.Ctl), (none : Option Bool))

def qStart := Paper2.LProducer.labelOfP Q (leftLabel (leftLabel (leftLabel Paper2.LProducer.lStart)))

def qInit := (((Paper2.LProducer.lCtl, Paper2.LProducer.powCtl), (none : Option Bool)),
  (((none, false) : BitEntry.Ctl), (none : Option Bool)))

/-- The input stack is the bank cell holding `LProducer.nC`; the output stack is the writer's
output stack. -/
def seedMachine : BitMachine.Machine :=
  BitMachineEncoding.ofFinite (ιL Paper2.LProducer.nC) outC qStart qInit Q

/-! ## The seed table -/

/-- Row `k` of the enumeration: the little-endian binary word of `k`. -/
def seedRow (p : ℕ) (k : Fin (2 ^ p)) : Fin p → Bool := fun j => Nat.testBit k.val j.val

/-- The enumeration is a bijection onto the row input set `{0,1}^p` of `cl:seed`. -/
theorem seedRow_bijective (p : ℕ) : Function.Bijective (seedRow p) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < p
  · exact congrFun h ⟨i, hi⟩
  · have ha : a.val < 2 ^ i := lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hb : b.val < 2 ^ i := lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt ha, Nat.testBit_eq_false_of_lt hb]

/-- The actual `cl:seed` matrix `R_0(γ,j) = γ_j` on the enumerated rows. -/
def seedTable (p : ℕ) : Fin (2 ^ p) → Fin p → Bool :=
  fun k j => Paper2.LookupSeed.matrix p (seedRow p k) j

def G0 (n : ℕ) : J → List Bool :=
  fun k => if k = ιL Paper2.LProducer.nC then List.replicate n true else []

theorem G0_outside (n : ℕ) (j : J) (h : ¬ ∃ k, ιL k = j) : G0 n j = [] := by
  unfold G0
  rw [if_neg]
  intro he
  exact h ⟨_, he.symm⟩

/-- Stage 1: the admitted producer, embedded. -/
theorem stage1 (n : ℕ) :
    ∃ t ≤ Paper2.LProducer.lBd n, ∃ vc, ∃ F : LK → List Bool,
      ((advance S1)^[t]) (⟨some Paper2.LProducer.lStart, Paper2.LProducer.lCtl, G0 n⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) = ⟨none, vc, bank ιL (G0 n) F⟩ ∧
      F Paper2.LProducer.pC = List.replicate (Paper2.LookupSeed.width (Nat.clog 2 n)) true ∧
      F Paper2.LProducer.x1 = [] ∧ F Paper2.LProducer.x2 = [] ∧ F Paper2.LProducer.z = [] := by
  obtain ⟨t, ht, vc, F, hr, -, -, -, -, -, -, -, hp, -, -, -, -, hz, hx1, hx2, -, -⟩ :=
    Paper2.LProducer.l_run n
  have hs := BitMachineStackRun.run ιL (G0 n) Paper2.LProducer.lProg
    (⟨some Paper2.LProducer.lStart, Paper2.LProducer.lCtl, Paper2.LProducer.L0 n⟩ :
      TM2.Cfg (fun _ : LK => Bool) _ _) t
  rw [hr] at hs
  have hb : bank ιL (G0 n) (Paper2.LProducer.L0 n) = G0 n := by
    apply bank_eq_self
    intro k
    simp only [Paper2.LProducer.L0, Function.update_apply, G0, ιL_eq_iff, Paper2.LProducer.u]
  refine ⟨t, ht, vc, F, ?_, ?_, hx1, hx2, hz⟩
  · simpa only [stackCfg, hb] using hs
  · rw [hp, Paper2.LProducer.p_eq]; rfl

theorem rawInit_eq (n : ℕ) :
    rawInit (ιL Paper2.LProducer.nC) qStart qInit (List.replicate n true) =
      (⟨some qStart, qInit, G0 n⟩ : TM2.Cfg (fun _ : J => Bool) _ _) := rfl

theorem qStart_eq : qStart = leftLabel (leftLabel (leftLabel Paper2.LProducer.lStart)) := rfl

theorem ready_out (bank : Fin KB → List Bool) (r c : ℕ) (out : List Bool) :
    (MatrixTableWriter.ready bank r c 0 0 0 0 [] out).contents outC = out := rfl

theorem ready_cols (bank : Fin KB → List Bool) (r c : ℕ) (out : List Bool) :
    (MatrixTableWriter.ready bank r c 0 0 0 0 [] out).contents colsC = List.replicate c true := rfl

theorem ready_rows (bank : Fin KB → List Bool) (r c : ℕ) (out : List Bool) :
    (MatrixTableWriter.ready bank r c 0 0 0 0 [] out).contents rowsC = List.replicate r true := rfl

/-- The explicit clock of the whole run. -/
def seedBound (n : ℕ) : ℕ :=
  Paper2.LProducer.lBd n +
    (4 * 2 ^ Paper2.LookupSeed.width (Nat.clog 2 n) + 5 * Paper2.LookupSeed.width (Nat.clog 2 n) + 7) +
    (2 * Paper2.LookupSeed.width (Nat.clog 2 n) + 2) +
    MatrixTableWriter.writerBound (2 ^ Paper2.LookupSeed.width (Nat.clog 2 n))
      (Paper2.LookupSeed.width (Nat.clog 2 n))
      (BitEntry.entryTime (2 ^ Paper2.LookupSeed.width (Nat.clog 2 n))
        (Paper2.LookupSeed.width (Nat.clog 2 n))) + 3

/-- **The raw run of the one fixed program from unary `n`.** It halts within `seedBound n`
steps with the row-major truth table of `cl:seed`'s `R_0 = LookupSeed.matrix p` (rows enumerated by
`seedRow p`) on the output stack, unary `p` (the column set `[p]`) on the writer's column-count
stack and unary `2^p` (the number of rows) on its row-count stack. -/
theorem seed_raw_run (n : ℕ) :
    ∃ t ≤ seedBound n,
      (((advance Q)^[t]) (rawInit (ιL Paper2.LProducer.nC) qStart qInit
          (List.replicate n true))).l = none ∧
      (((advance Q)^[t]) (rawInit (ιL Paper2.LProducer.nC) qStart qInit
          (List.replicate n true))).stk outC =
        MatrixMaterialization.rowMajor (seedTable (Paper2.LookupSeed.width (Nat.clog 2 n))) ∧
      (((advance Q)^[t]) (rawInit (ιL Paper2.LProducer.nC) qStart qInit
          (List.replicate n true))).stk colsC =
        List.replicate (Paper2.LookupSeed.width (Nat.clog 2 n)) true ∧
      (((advance Q)^[t]) (rawInit (ιL Paper2.LProducer.nC) qStart qInit
          (List.replicate n true))).stk rowsC =
        List.replicate (2 ^ Paper2.LookupSeed.width (Nat.clog 2 n)) true := by
  set p := Paper2.LookupSeed.width (Nat.clog 2 n) with hpdef
  obtain ⟨t1, ht1, vc, F, h1, hp, hx1, hx2, hz⟩ := stage1 n
  -- stage 2
  set G1 := bank ιL (G0 n) F with hG1
  have hG1rows : G1 rowsC = [] := by
    rw [hG1, bank_outside _ _ _ _ (not_ιL_extra _), G0_outside n _ (not_ιL_extra _)]
  have hG1cols : G1 colsC = [] := by
    rw [hG1, bank_outside _ _ _ _ (not_ιL_extra _), G0_outside n _ (not_ιL_extra _)]
  obtain ⟨t2, ht2, h2⟩ := MatrixStage4ScalarPreparationOps.unary_power_run ιP G1 p
    (by show G1 (ιL Paper2.LProducer.pC) = _; rw [hG1, bank_at]; exact hp)
    (by show G1 rowsC = []; exact hG1rows)
    (by show G1 (ιL Paper2.LProducer.x1) = []; rw [hG1, bank_at]; exact hx1)
    (by show G1 (ιL Paper2.LProducer.x2) = []; rw [hG1, bank_at]; exact hx2)
  set G2 := Function.update G1 rowsC (List.replicate (2 ^ p) true) with hG2
  have h2' : ((advance S2)^[t2]) (⟨some (.inr false), Paper2.LProducer.powCtl, G1⟩ :
      TM2.Cfg (fun _ : J => Bool) _ _) = ⟨none, Paper2.LProducer.powCtl, G2⟩ := h2
  -- stage 3
  have hG2z : G2 (ιC 2) = [] := by
    show G2 (ιL Paper2.LProducer.z) = []
    rw [hG2, Function.update_of_ne (ιL_ne_inr _ _), hG1, bank_at]; exact hz
  have h3 := MatrixStage4ScalarPreparationOps.copy_run ιC G2 hG2z
  have hG2p : G2 (ιC 0) = List.replicate p true := by
    show G2 (ιL Paper2.LProducer.pC) = _
    rw [hG2, Function.update_of_ne (ιL_ne_inr _ _), hG1, bank_at]; exact hp
  have hG2c : G2 (ιC 1) = [] := by
    show G2 colsC = []
    rw [hG2, Function.update_of_ne (by simp [colsC, rowsC])]; exact hG1cols
  rw [hG2p, hG2c, List.length_replicate, List.append_nil] at h3
  set G3 := Function.update G2 colsC (List.replicate p true) with hG3
  have h3' : ((advance S3)^[2 * p + 2]) (⟨some BitMachineCopy.Label.scan, (none : Option Bool), G2⟩ :
      TM2.Cfg (fun _ : J => Bool) _ _) = ⟨none, none, G3⟩ := h3
  -- stage 4: the writer's entry bank
  let bankF : Fin KB → List Bool := fun i => G3 (.inl (.inl i))
  have hG3out : ∀ j : J, j ≠ colsC → j ≠ rowsC → (¬ ∃ k, ιL k = j) → G3 j = [] := by
    intro j hc hr hk
    rw [hG3, Function.update_of_ne hc, hG2, Function.update_of_ne hr, hG1,
      bank_outside _ _ _ _ hk, G0_outside n _ hk]
  have hbF : ∀ i, bankF (scr i) = [] := by
    intro i
    exact hG3out _ (by simp [colsC]) (by simp [rowsC]) (not_ιL_scr i)
  have hready : G3 = (MatrixTableWriter.ready bankF (2 ^ p) p 0 0 0 0 [] []).contents := by
    funext j
    rcases j with (i | i) | e
    · rfl
    · rw [hG3out _ (by simp [colsC]) (by simp [rowsC]) (not_ιL_cell i)]
      fin_cases i <;> rfl
    · cases e
      · show G3 rowsC = _
        rw [hG3, Function.update_of_ne (show rowsC ≠ colsC by simp),
          hG2, Function.update_self]
        rfl
      · show G3 colsC = _
        rw [hG3, Function.update_self]
        rfl
      all_goals
        (rw [hG3out _ (by simp [colsC]) (by simp [rowsC]) (not_ιL_extra _)]; rfl)
  obtain ⟨t4, ht4, v4, h4⟩ := MatrixTableWriter.write_rowMajor Pent BitEntry.Label.cpx
    ((none, false) : BitEntry.Ctl) bankF (2 ^ p) p (BitEntry.entryTime (2 ^ p) p)
    (fun x y => Nat.testBit x y) (seedTable p) (fun x y => rfl)
    (entry_runs bankF hbF (2 ^ p) p) []
  rw [List.append_nil] at h4
  have h4' : ((advance S4)^[t4]) (⟨some (.inr (.copy .rows)), (((none, false) : BitEntry.Ctl),
      (none : Option Bool)), G3⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
      ⟨none, v4, (MatrixTableWriter.ready bankF (2 ^ p) p 0 0 0 0 []
        (MatrixMaterialization.rowMajor (seedTable p))).contents⟩ := by
    rw [hready]; exact h4
  -- composition
  obtain ⟨ta, hta, ha⟩ := BitMachineRawSequence.runs S1 S2 Paper2.LProducer.lStart (.inr false)
    Paper2.LProducer.lCtl vc Paper2.LProducer.powCtl Paper2.LProducer.powCtl (G0 n) G1 G2 t1 t2
    h1 h2'
  obtain ⟨tb, htb, hb⟩ := BitMachineRawSequence.runs Q12 S3 (leftLabel Paper2.LProducer.lStart)
    BitMachineCopy.Label.scan (Paper2.LProducer.lCtl, Paper2.LProducer.powCtl)
    (Paper2.LProducer.lCtl, Paper2.LProducer.powCtl) (none : Option Bool) none (G0 n) G2 G3
    ta (2 * p + 2) ha h3'
  obtain ⟨tc, htc, hc⟩ := BitMachineRawSequence.runs Q123 S4
    (leftLabel (leftLabel Paper2.LProducer.lStart)) (.inr (.copy .rows))
    ((Paper2.LProducer.lCtl, Paper2.LProducer.powCtl), (none : Option Bool))
    ((Paper2.LProducer.lCtl, Paper2.LProducer.powCtl), (none : Option Bool))
    (((none, false) : BitEntry.Ctl), (none : Option Bool)) v4 (G0 n) G3 _ tb t4 hb h4'
  refine ⟨tc, ?_, ?_⟩
  · have hw : t4 ≤ MatrixTableWriter.writerBound (2 ^ p) p (BitEntry.entryTime (2 ^ p) p) := ht4
    unfold seedBound
    rw [← hpdef]
    omega
  · rw [rawInit_eq, qStart_eq]
    unfold qInit Q
    rw [hc]
    exact ⟨rfl, ready_out bankF (2 ^ p) p (MatrixMaterialization.rowMajor (seedTable p)),
      ready_cols bankF (2 ^ p) p (MatrixMaterialization.rowMajor (seedTable p)),
      ready_rows bankF (2 ^ p) p (MatrixMaterialization.rowMajor (seedTable p))⟩

end

end SeedT45.SeedTable

#print axioms SeedT45.SeedTable.entry_runs
#print axioms SeedT45.SeedTable.stage1
#print axioms SeedT45.SeedTable.seedRow_bijective
#print axioms SeedT45.SeedTable.seed_raw_run
