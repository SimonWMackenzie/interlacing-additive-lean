import Paper2.YaoMaterialization
import EthInapproximability.CurrentPaper.MatrixUnaryDivision
import EthInapproximability.CurrentPaper.ExactParameterBranchInstall
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Unit 5 segment Y4 (lane a-yao-owner-1): the physical index decoder.

Consumer: the one-entry callback Y5 (writer cells `x,y` of
`MatrixTableWriter.EntryRuns`).  One fixed program (no parameters at all)
on 14 named cells placed by an arbitrary embedding `ι : Fin 14 ↪ J` into an
ambient bank.  Charged inputs: unary `x`, `y` (writer row/column), and the
unary divisors `sel = selectorCount`, `pay = payloadCount`, `pow = 2^b`
(Y6's prelude produces them).  Five stages, sequenced by the admitted
`BitMachineRawSequence.program` with four charged handoffs:
copy `x`; divide by `sel` (admitted `MatrixUnaryDivision`); copy `y`;
divide by `pay`; divide the quotient by `pow`.
Exit bank (exact, `Function.update` chain on the whole ambient bank): the
five unary outputs `vertex = x/sel`, `z = x%sel`, `g = (y/pay)/pow`,
`a = (y/pay)%pow`, `l = y%pay`; `x,y` and the divisors preserved; the four
scratch cells empty again; every other ambient cell untouched.
Value bridges: `rowIndex_val`, `columnIndex_val` (admitted). -/

namespace Paper2.YaoIndexDecoder

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoMaterialization
open Paper2.YaoLowerBound

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-! ## One embedded division stage -/

noncomputable def divProgram {K : Type*} [DecidableEq K] (ι : Fin 6 ↪ K)
    (l : MatrixUnaryDivision.Label) :
    TM2.Stmt (fun _ : K => Bool) MatrixUnaryDivision.Label Bool :=
  BitMachineStackEmbedding.stmt ι id id id none (MatrixUnaryDivision.program l)

/-- The admitted division on six selected ambient cells; the dividend cell is
consumed, the divisor preserved, the remainder and quotient written to cells
that start empty, and the two work cells end empty.  Exact whole bank. -/
theorem div_run {K : Type*} [DecidableEq K] (ι : Fin 6 ↪ K)
    (S : K → List Bool) (n m : ℕ)
    (h0 : S (ι 0) = List.replicate n true) (h1 : S (ι 1) = List.replicate m true)
    (h2 : S (ι 2) = []) (h3 : S (ι 3) = []) (h4 : S (ι 4) = []) (h5 : S (ι 5) = []) :
    ∃ t ≤ 8 * n + 3 * m + 4,
      ((advance (divProgram ι))^[t])
        (⟨some .start, false, S⟩ :
          TM2.Cfg (fun _ : K => Bool) MatrixUnaryDivision.Label Bool) =
        ⟨none, false,
          Function.update (Function.update (Function.update S (ι 0) [])
            (ι 3) (List.replicate (n % m) true)) (ι 4) (List.replicate (n / m) true)⟩ := by
  classical
  let c := MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
    (List.replicate m true) [] [] [] []
  have hbank : BitMachineStackEmbedding.bank ι S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;> simp [c, MatrixUnaryDivision.cfg, h0, h1, h2, h3, h4, h5]
  have hrun := MatrixUnaryDivision.division_total_run n m
  have hhalt : (((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime n m])
      c).l = none := by
    change (MatrixUnaryDivision.run _ c).l = none
    rw [hrun]
    rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs ι S id id id (fun _ => rfl) none
    MatrixUnaryDivision.program (divProgram ι) (by intro l; rfl) c _ hhalt
  have hlocal : ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime n m]) c =
      MatrixUnaryDivision.cfg none false [] (List.replicate m true) []
        (List.replicate (n % m) true) (List.replicate (n / m) true) [] := hrun
  rw [hlocal] at he
  change ((advance (divProgram ι))^[t])
      ⟨some .start, false, BitMachineStackEmbedding.bank ι S c.stk⟩ =
      ⟨none, false, BitMachineStackEmbedding.bank ι S
        (MatrixUnaryDivision.cfg none false [] (List.replicate m true) []
          (List.replicate (n % m) true) (List.replicate (n / m) true) []).stk⟩ at he
  have hupdate : (MatrixUnaryDivision.cfg none false [] (List.replicate m true) []
      (List.replicate (n % m) true) (List.replicate (n / m) true) []).stk =
      Function.update (Function.update (Function.update c.stk 0 []) 3
        (List.replicate (n % m) true)) 4 (List.replicate (n / m) true) := by
    funext k
    fin_cases k <;> simp [c, MatrixUnaryDivision.cfg, h0, h1]
  rw [hbank, hupdate, BitMachineStackEmbedding.bank_update,
    BitMachineStackEmbedding.bank_update, BitMachineStackEmbedding.bank_update, hbank] at he
  exact ⟨t, ht.trans (MatrixUnaryDivision.totalTime_bound n m), he⟩

/-! ## Cell layout and the fixed five-stage program -/

/-- Cells: 0 `x`, 1 `y`, 2 `sel`, 3 `pay`, 4 `pow`, 5 work, 6 count/copy
scratch, 7 division saved, 8 `vertex`, 9 `z`, 10 `g`, 11 `a`, 12 `l`,
13 intermediate column quotient. -/
abbrev Cell := Fin 14

def sel3 (p q r : Fin 14) (h : Function.Injective ![p, q, r]) : Fin 3 ↪ Fin 14 :=
  ⟨![p, q, r], h⟩

def sel6 (p q r s u w : Fin 14) (h : Function.Injective ![p, q, r, s, u, w]) :
    Fin 6 ↪ Fin 14 :=
  ⟨![p, q, r, s, u, w], h⟩

def copyXSel : Fin 3 ↪ Fin 14 := sel3 0 5 6 (by decide)
def divXSel : Fin 6 ↪ Fin 14 := sel6 5 2 6 9 8 7 (by decide)
def copyYSel : Fin 3 ↪ Fin 14 := sel3 1 5 6 (by decide)
def divYSel : Fin 6 ↪ Fin 14 := sel6 5 3 6 12 13 7 (by decide)
def divQSel : Fin 6 ↪ Fin 14 := sel6 13 4 6 11 10 7 (by decide)

variable {J : Type*} [DecidableEq J]

noncomputable def stageQ (ι : Fin 14 ↪ J) := divProgram (divQSel.trans ι)

noncomputable def stageYQ (ι : Fin 14 ↪ J) :=
  BitMachineRawSequence.program (divProgram (divYSel.trans ι)) (stageQ ι)
    MatrixUnaryDivision.Label.start false false

noncomputable def stageCYQ (ι : Fin 14 ↪ J) :=
  BitMachineRawSequence.program
    (ExactParameterBranchInstall.copyProgram (copyYSel.trans ι)) (stageYQ ι)
    (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start) none (false, false)

noncomputable def stageXCYQ (ι : Fin 14 ↪ J) :=
  BitMachineRawSequence.program (divProgram (divXSel.trans ι)) (stageCYQ ι)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) false (none, (false, false))

/-- The fixed index-decoder program (depends only on the placement `ι`). -/
noncomputable def program (ι : Fin 14 ↪ J) :=
  BitMachineRawSequence.program
    (ExactParameterBranchInstall.copyProgram (copyXSel.trans ι)) (stageXCYQ ι)
    (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start) none
    (false, (none, (false, false)))

/-- Start label and control of `program`. -/
def startLabel :=
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan :
    BitMachineRawSequence.Label BitMachineCopy.Label
      (BitMachineRawSequence.Label MatrixUnaryDivision.Label
        (BitMachineRawSequence.Label BitMachineCopy.Label
          (BitMachineRawSequence.Label MatrixUnaryDivision.Label
            MatrixUnaryDivision.Label))))

def startControl : Option Bool × (Bool × (Option Bool × (Bool × Bool))) :=
  (none, (false, (none, (false, false))))

/-- The exact exit bank: only the five output cells change. -/
def outBank (ι : Fin 14 ↪ J) (S : J → List Bool) (x y sel pay pow : ℕ) :
    J → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update S (ι 8) (List.replicate (x / sel) true))
      (ι 9) (List.replicate (x % sel) true))
      (ι 10) (List.replicate (y / pay / pow) true))
      (ι 11) (List.replicate (y / pay % pow) true))
      (ι 12) (List.replicate (y % pay) true)

/-- Y4 main theorem: one physical run of the fixed program from the charged
unary inputs to the exact exit bank, within an explicit clock. -/
theorem physical_index_decode (ι : Fin 14 ↪ J) (S : J → List Bool)
    (x y sel pay pow : ℕ)
    (hx : S (ι 0) = List.replicate x true) (hy : S (ι 1) = List.replicate y true)
    (hsel : S (ι 2) = List.replicate sel true) (hpay : S (ι 3) = List.replicate pay true)
    (hpow : S (ι 4) = List.replicate pow true)
    (h5 : S (ι 5) = []) (h6 : S (ι 6) = []) (h7 : S (ι 7) = []) (h8 : S (ι 8) = [])
    (h9 : S (ι 9) = []) (h10 : S (ι 10) = []) (h11 : S (ι 11) = [])
    (h12 : S (ι 12) = []) (h13 : S (ι 13) = []) :
    ∃ total ≤ (2 * x + 2) + (8 * x + 3 * sel + 4) + (2 * y + 2) +
        (8 * y + 3 * pay + 4) + (8 * (y / pay) + 3 * pow + 4) + 4,
      ((advance (program ι))^[total])
        (⟨some startLabel, startControl, S⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, startControl, outBank ι S x y sel pay pow⟩ := by
  classical
  have hinj := ι.injective
  -- stage 1: copy x into the work cell
  obtain ⟨t1, ht1, hr1⟩ := ExactParameterBranchInstall.copy_run (copyXSel.trans ι) S
    (List.replicate x true) (by simp [copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13]) (by simp [copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13])
    (by simp [copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13])
  set S1 := Function.update S ((copyXSel.trans ι) 1) (List.replicate x true) with hS1
  -- stage 2: divide by sel
  obtain ⟨t2, ht2, hr2⟩ := div_run (divXSel.trans ι) S1 x sel
    (by simp [hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13]) (by simp [hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13]) (by simp [hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13])
    (by simp [hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13]) (by simp [hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13]) (by simp [hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13])
  set S2 := Function.update (Function.update (Function.update S1 ((divXSel.trans ι) 0) [])
    ((divXSel.trans ι) 3) (List.replicate (x % sel) true)) ((divXSel.trans ι) 4)
    (List.replicate (x / sel) true) with hS2
  -- stage 3: copy y into the work cell
  obtain ⟨t3, ht3, hr3⟩ := ExactParameterBranchInstall.copy_run (copyYSel.trans ι) S2
    (List.replicate y true) (by simp [hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13]) (by simp [hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13])
    (by simp [hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13])
  set S3 := Function.update S2 ((copyYSel.trans ι) 1) (List.replicate y true) with hS3
  -- stage 4: divide by pay
  obtain ⟨t4, ht4, hr4⟩ := div_run (divYSel.trans ι) S3 y pay
    (by simp [hS3, hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13]) (by simp [hS3, hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13])
    (by simp [hS3, hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13]) (by simp [hS3, hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13])
    (by simp [hS3, hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13]) (by simp [hS3, hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13])
  set S4 := Function.update (Function.update (Function.update S3 ((divYSel.trans ι) 0) [])
    ((divYSel.trans ι) 3) (List.replicate (y % pay) true)) ((divYSel.trans ι) 4)
    (List.replicate (y / pay) true) with hS4
  -- stage 5: divide the column quotient by pow
  obtain ⟨t5, ht5, hr5⟩ := div_run (divQSel.trans ι) S4 (y / pay) pow
    (by simp [hS4, hS3, hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13]) (by simp [hS4, hS3, hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13])
    (by simp [hS4, hS3, hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13]) (by simp [hS4, hS3, hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13])
    (by simp [hS4, hS3, hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13]) (by simp [hS4, hS3, hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel, sel3, sel6, Function.update_apply, hinj.eq_iff, hx, hy, hsel, hpay, hpow, h5, h6, h7, h8, h9, h10, h11, h12, h13])
  -- the final bank is exactly `outBank`
  have hfinal : Function.update (Function.update (Function.update S4
      ((divQSel.trans ι) 0) []) ((divQSel.trans ι) 3) (List.replicate (y / pay % pow) true))
      ((divQSel.trans ι) 4) (List.replicate (y / pay / pow) true) =
      outBank ι S x y sel pay pow := by
    funext j
    by_cases hj : ∃ k, ι k = j
    · obtain ⟨k, rfl⟩ := hj
      fin_cases k <;>
        simp [outBank, hS4, hS3, hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel,
          sel3, sel6, Function.update_apply, hinj.eq_iff, h5, h13]
    · have hne : ∀ k, j ≠ ι k := fun k hk => hj ⟨k, hk.symm⟩
      simp [outBank, hS4, hS3, hS2, hS1, copyXSel, divXSel, copyYSel, divYSel, divQSel,
        sel3, sel6, Function.update_apply, hne]
  rw [hfinal] at hr5
  -- sequencing with four charged handoffs
  obtain ⟨u4, hu4, hrun4⟩ := BitMachineRawSequence.runs (divProgram (divYSel.trans ι))
    (stageQ ι) MatrixUnaryDivision.Label.start MatrixUnaryDivision.Label.start
    false false false false S3 S4 _ t4 t5 hr4 hr5
  obtain ⟨u3, hu3, hrun3⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (copyYSel.trans ι)) (stageYQ ι)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start)
    none none (false, false) (false, false) S2 S3 _ t3 u4 hr3 hrun4
  obtain ⟨u2, hu2, hrun2⟩ := BitMachineRawSequence.runs (divProgram (divXSel.trans ι))
    (stageCYQ ι) MatrixUnaryDivision.Label.start
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    false false (none, (false, false)) (none, (false, false)) S1 S2 _ t2 u3 hr2 hrun3
  obtain ⟨u1, hu1, hrun1⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (copyXSel.trans ι)) (stageXCYQ ι)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start)
    none none (false, (none, (false, false))) (false, (none, (false, false)))
    S S1 _ t1 u2 hr1 hrun2
  refine ⟨u1, ?_, hrun1⟩
  simp only [List.length_replicate] at ht1 ht3
  omega

/-! ## Value bridges to the materialized row/column numbering -/

theorem row_decode (vertexCount t b lambda : ℕ)
    (x : Fin (rowCount vertexCount t b lambda)) :
    x.val / selectorCount t b lambda = ((rowIndex vertexCount t b lambda).symm x).1.val ∧
      x.val % selectorCount t b lambda = ((rowIndex vertexCount t b lambda).symm x).2.val := by
  set c := (rowIndex vertexCount t b lambda).symm x with hc
  have h := rowIndex_val vertexCount t b lambda c.1 c.2
  have hcx : rowIndex vertexCount t b lambda (c.1, c.2) = x :=
    (rowIndex vertexCount t b lambda).apply_symm_apply x
  rw [hcx] at h
  have hz := c.2.isLt
  rw [h]
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hz, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]

theorem column_decode (t b lambda : ℕ) (y : Fin (columnCount t b lambda)) :
    y.val % payloadCount t b lambda = ((columnIndex t b lambda).symm y).2.2.val ∧
      y.val / payloadCount t b lambda % 2 ^ b = ((columnIndex t b lambda).symm y).2.1.val ∧
      y.val / payloadCount t b lambda / 2 ^ b = ((columnIndex t b lambda).symm y).1.val := by
  set c := (columnIndex t b lambda).symm y with hc
  have h := columnIndex_val t b lambda c.1 c.2.1 c.2.2
  have hcy : columnIndex t b lambda (c.1, c.2.1, c.2.2) = y :=
    (columnIndex t b lambda).apply_symm_apply y
  rw [hcy] at h
  have hl := c.2.2.isLt
  have ha := c.2.1.isLt
  have hq : y.val / payloadCount t b lambda = c.1.val * 2 ^ b + c.2.1.val := by
    rw [h, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hl,
      Nat.zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [h, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
  · rw [hq, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  · rw [hq, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt ha,
      Nat.zero_add]

#print axioms div_run
#print axioms physical_index_decode
#print axioms row_decode
#print axioms column_decode

end Paper2.YaoIndexDecoder
