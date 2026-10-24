import Paper2.YaoPrelude
import Paper2.YaoMaterialization

/-! Unit 5 segment Y6, addendum (lane a-yao-owner-2): the writer dimensions.

Consumer: Y7 (`MatrixTableWriter.ready bank r c 0 0 0 0 [] []` needs unary
`r = rowCount v t b lambda` and `c = columnCount t b lambda`).  One fixed program
per `t`, placed by `δ : Fin 11 ↪ J`.  Cells: 0 unary `v`, 1 `sel`, 2 `pow`, 3 `pay`
(all preserved), 4 output `r`, 5 output `c`, 6..10 scratch (empty at entry and exit).
Eight stages, seven charged handoffs: copy `v`; copy `sel`; admitted multiplication
(`v*sel`); admitted fixed write `2^(t-1)`; copy `pow`; multiplication; copy `pay`;
multiplication.  Value bridges to the admitted `rowCount`/`columnCount`. -/

noncomputable section

namespace Paper2.YaoPrelude

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoLowerBound
open Paper2.YaoLookup

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def d3 (p q r : Fin 11) (h : Function.Injective ![p, q, r]) : Fin 3 ↪ Fin 11 := ⟨![p, q, r], h⟩

def cpV : Fin 3 ↪ Fin 11 := d3 0 7 10 (by decide)
def cpSel : Fin 3 ↪ Fin 11 := d3 1 8 10 (by decide)
def mulR : Fin 4 ↪ Fin 11 := ⟨![8, 7, 4, 10], by decide⟩
def cpPw : Fin 3 ↪ Fin 11 := d3 2 7 10 (by decide)
def mulQ : Fin 4 ↪ Fin 11 := ⟨![6, 7, 9, 10], by decide⟩
def cpPay : Fin 3 ↪ Fin 11 := d3 3 8 10 (by decide)
def mulC : Fin 4 ↪ Fin 11 := ⟨![8, 9, 5, 10], by decide⟩

variable {J : Type*} [DecidableEq J]

def dm78 (δ : Fin 11 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (cpPay.trans δ))
    (Paper2.YaoPositionFull.mulProgram (mulC.trans δ)) MatrixUnaryArithmetic.Label.outer
    none false
def dm678 (δ : Fin 11 ↪ J) :=
  BitMachineRawSequence.program (Paper2.YaoPositionFull.mulProgram (mulQ.trans δ)) (dm78 δ)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) false (none, false)
def dm5678 (δ : Fin 11 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (cpPw.trans δ))
    (dm678 δ) (BitMachineRawSequence.leftLabel MatrixUnaryArithmetic.Label.outer) none
    (false, (none, false))
def dm45678 (t : ℕ) (δ : Fin 11 ↪ J) :=
  BitMachineRawSequence.program (SourceClauseFixedUnary.program (δ 6) (2 ^ (t - 1))) (dm5678 δ)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) () (none, (false, (none, false)))
def dm345678 (t : ℕ) (δ : Fin 11 ↪ J) :=
  BitMachineRawSequence.program (Paper2.YaoPositionFull.mulProgram (mulR.trans δ)) (dm45678 t δ)
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label (2 ^ (t - 1)))) false
    ((), (none, (false, (none, false))))
def dm2345678 (t : ℕ) (δ : Fin 11 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (cpSel.trans δ))
    (dm345678 t δ) (BitMachineRawSequence.leftLabel MatrixUnaryArithmetic.Label.outer) none
    (false, ((), (none, (false, (none, false)))))
/-- The fixed writer-dimension program. -/
def dimsProgram (t : ℕ) (δ : Fin 11 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (cpV.trans δ))
    (dm2345678 t δ) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none
    (none, (false, ((), (none, (false, (none, false))))))

def dimsControl : Option Bool × (Option Bool × (Bool × (Unit × (Option Bool × (Bool ×
    (Option Bool × Bool)))))) :=
  (none, (none, (false, ((), (none, (false, (none, false)))))))

def dimsClock (t v sel pow pay : ℕ) : ℕ :=
  (2 * v + 2) + (2 * sel + 2) + (v * (2 * sel + 3) + 1 + (sel + 1)) + (2 ^ (t - 1) + 1) +
    (2 * pow + 2) + (pow * (2 * 2 ^ (t - 1) + 3) + 1 + (2 ^ (t - 1) + 1)) + (2 * pay + 2) +
    (pow * 2 ^ (t - 1) * (2 * pay + 3) + 1 + (pay + 1)) + 7

theorem physical_dims (t : ℕ) (δ : Fin 11 ↪ J) (S : J → List Bool) (v sel pow pay : ℕ)
    (h0 : S (δ 0) = List.replicate v true) (h1 : S (δ 1) = List.replicate sel true)
    (h2 : S (δ 2) = List.replicate pow true) (h3 : S (δ 3) = List.replicate pay true)
    (hs : ∀ k : Fin 11, 4 ≤ k.val → S (δ k) = []) :
    ∃ total ≤ dimsClock t v sel pow pay, ∃ c',
      ((advance (dimsProgram t δ))^[total])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), dimsControl, S⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, c', Function.update (Function.update S (δ 4) (List.replicate (v * sel) true))
          (δ 5) (List.replicate (pow * 2 ^ (t - 1) * pay) true)⟩ := by
  classical
  have hinj := δ.injective
  have e := hs
  -- D1: copy v into cell 7
  obtain ⟨t1, ht1, hr1⟩ := ExactParameterBranchInstall.copy_run (cpV.trans δ) S
    (List.replicate v true) (by simp [cpV, d3, h0]) (by simp [cpV, d3, e 7 (by decide)])
    (by simp [cpV, d3, e 10 (by decide)])
  change _ = (⟨none, none, Function.update S (δ 7) (List.replicate v true)⟩ :
    TM2.Cfg (fun _ : J => Bool) BitMachineCopy.Label (Option Bool)) at hr1
  set S1 := Function.update S (δ 7) (List.replicate v true) with hS1
  -- D2: copy sel into cell 8
  obtain ⟨t2, ht2, hr2⟩ := ExactParameterBranchInstall.copy_run (cpSel.trans δ) S1
    (List.replicate sel true) (by simp [hS1, cpSel, d3, hinj.eq_iff, h1])
    (by simp [hS1, cpSel, d3, hinj.eq_iff, e 8 (by decide)])
    (by simp [hS1, cpSel, d3, hinj.eq_iff, e 10 (by decide)])
  change _ = (⟨none, none, Function.update S1 (δ 8) (List.replicate sel true)⟩ :
    TM2.Cfg (fun _ : J => Bool) BitMachineCopy.Label (Option Bool)) at hr2
  set S2 := Function.update S1 (δ 8) (List.replicate sel true) with hS2
  -- D3: r = v * sel
  obtain ⟨t3, ht3, hr3⟩ := Paper2.YaoPositionFull.mul_run (mulR.trans δ) S2 v sel
    (by simp [hS2, mulR]) (by simp [hS2, hS1, mulR, hinj.eq_iff])
    (by simp [hS2, hS1, mulR, hinj.eq_iff, e 4 (by decide)])
    (by simp [hS2, hS1, mulR, hinj.eq_iff, e 10 (by decide)])
  change _ = (⟨none, false, Function.update (Function.update (Function.update S2 (δ 8) [])
      (δ 7) []) (δ 4) (List.replicate (v * sel) true)⟩ :
    TM2.Cfg (fun _ : J => Bool) MatrixUnaryArithmetic.Label Bool) at hr3
  have hS3e : Function.update (Function.update (Function.update S2 (δ 8) [])
      (δ 7) []) (δ 4) (List.replicate (v * sel) true) =
      Function.update S (δ 4) (List.replicate (v * sel) true) := by
    funext j
    simp only [hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all [hinj.eq_iff, e 7 (by decide), e 8 (by decide)]
  rw [hS3e] at hr3
  set S3 := Function.update S (δ 4) (List.replicate (v * sel) true) with hS3
  -- D4: write Q = 2^(t-1) into cell 6
  have hr4 := push_const_run (δ 6) S3 (2 ^ (t - 1)) []
    (by simp [hS3, hinj.eq_iff, e 6 (by decide)])
  rw [List.append_nil] at hr4
  set S4 := Function.update S3 (δ 6) (List.replicate (2 ^ (t - 1)) true) with hS4
  -- D5: copy pow into cell 7
  obtain ⟨t5, ht5, hr5⟩ := ExactParameterBranchInstall.copy_run (cpPw.trans δ) S4
    (List.replicate pow true) (by simp [hS4, hS3, cpPw, d3, hinj.eq_iff, h2])
    (by simp [hS4, hS3, cpPw, d3, hinj.eq_iff, e 7 (by decide)])
    (by simp [hS4, hS3, cpPw, d3, hinj.eq_iff, e 10 (by decide)])
  change _ = (⟨none, none, Function.update S4 (δ 7) (List.replicate pow true)⟩ :
    TM2.Cfg (fun _ : J => Bool) BitMachineCopy.Label (Option Bool)) at hr5
  set S5 := Function.update S4 (δ 7) (List.replicate pow true) with hS5
  -- D6: pow * Q into cell 9
  obtain ⟨t6, ht6, hr6⟩ := Paper2.YaoPositionFull.mul_run (mulQ.trans δ) S5 pow (2 ^ (t - 1))
    (by simp [hS5, hS4, mulQ, hinj.eq_iff]) (by simp [hS5, mulQ])
    (by simp [hS5, hS4, hS3, mulQ, hinj.eq_iff, e 9 (by decide)])
    (by simp [hS5, hS4, hS3, mulQ, hinj.eq_iff, e 10 (by decide)])
  change _ = (⟨none, false, Function.update (Function.update (Function.update S5 (δ 6) [])
      (δ 7) []) (δ 9) (List.replicate (pow * 2 ^ (t - 1)) true)⟩ :
    TM2.Cfg (fun _ : J => Bool) MatrixUnaryArithmetic.Label Bool) at hr6
  have hS6e : Function.update (Function.update (Function.update S5 (δ 6) [])
      (δ 7) []) (δ 9) (List.replicate (pow * 2 ^ (t - 1)) true) =
      Function.update S3 (δ 9) (List.replicate (pow * 2 ^ (t - 1)) true) := by
    funext j
    simp only [hS5, hS4, hS3, Function.update_apply]
    split_ifs <;> simp_all [hinj.eq_iff, e 6 (by decide), e 7 (by decide)]
  rw [hS6e] at hr6
  set S6 := Function.update S3 (δ 9) (List.replicate (pow * 2 ^ (t - 1)) true) with hS6
  -- D7: copy pay into cell 8
  obtain ⟨t7, ht7, hr7⟩ := ExactParameterBranchInstall.copy_run (cpPay.trans δ) S6
    (List.replicate pay true) (by simp [hS6, hS3, cpPay, d3, hinj.eq_iff, h3])
    (by simp [hS6, hS3, cpPay, d3, hinj.eq_iff, e 8 (by decide)])
    (by simp [hS6, hS3, cpPay, d3, hinj.eq_iff, e 10 (by decide)])
  change _ = (⟨none, none, Function.update S6 (δ 8) (List.replicate pay true)⟩ :
    TM2.Cfg (fun _ : J => Bool) BitMachineCopy.Label (Option Bool)) at hr7
  set S7 := Function.update S6 (δ 8) (List.replicate pay true) with hS7
  -- D8: c = (pow * Q) * pay into cell 5
  obtain ⟨t8, ht8, hr8⟩ := Paper2.YaoPositionFull.mul_run (mulC.trans δ) S7
    (pow * 2 ^ (t - 1)) pay (by simp [hS7, mulC]) (by simp [hS7, hS6, mulC, hinj.eq_iff])
    (by simp [hS7, hS6, hS3, mulC, hinj.eq_iff, e 5 (by decide)])
    (by simp [hS7, hS6, hS3, mulC, hinj.eq_iff, e 10 (by decide)])
  change _ = (⟨none, false, Function.update (Function.update (Function.update S7 (δ 8) [])
      (δ 9) []) (δ 5) (List.replicate (pow * 2 ^ (t - 1) * pay) true)⟩ :
    TM2.Cfg (fun _ : J => Bool) MatrixUnaryArithmetic.Label Bool) at hr8
  have hS8e : Function.update (Function.update (Function.update S7 (δ 8) [])
      (δ 9) []) (δ 5) (List.replicate (pow * 2 ^ (t - 1) * pay) true) =
      Function.update (Function.update S (δ 4) (List.replicate (v * sel) true))
        (δ 5) (List.replicate (pow * 2 ^ (t - 1) * pay) true) := by
    funext j
    simp only [hS7, hS6, hS3, Function.update_apply]
    split_ifs <;> simp_all [hinj.eq_iff, e 8 (by decide), e 9 (by decide)]
  rw [hS8e] at hr8
  -- sequencing
  obtain ⟨u7, hu7, hrun7⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (cpPay.trans δ))
    (Paper2.YaoPositionFull.mulProgram (mulC.trans δ))
    BitMachineCopy.Label.scan MatrixUnaryArithmetic.Label.outer
    none none false false S6 S7 _ t7 t8 hr7 hr8
  obtain ⟨u6, hu6, hrun6⟩ := BitMachineRawSequence.runs
    (Paper2.YaoPositionFull.mulProgram (mulQ.trans δ)) (dm78 δ)
    MatrixUnaryArithmetic.Label.outer (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    false false (none, false) (none, false) S5 S6 _ t6 u7 hr6 hrun7
  obtain ⟨u5, hu5, hrun5⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (cpPw.trans δ)) (dm678 δ)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel MatrixUnaryArithmetic.Label.outer)
    none none (false, (none, false)) (false, (none, false)) S4 S5 _ t5 u6 hr5 hrun6
  obtain ⟨u4, hu4, hrun4⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (δ 6) (2 ^ (t - 1))) (dm5678 δ)
    (0 : SourceClauseFixedUnary.Label (2 ^ (t - 1)))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    () () (none, (false, (none, false))) (none, (false, (none, false))) S3 S4 _
    (2 ^ (t - 1) + 1) u5 hr4 hrun5
  obtain ⟨u3, hu3, hrun3⟩ := BitMachineRawSequence.runs
    (Paper2.YaoPositionFull.mulProgram (mulR.trans δ)) (dm45678 t δ)
    MatrixUnaryArithmetic.Label.outer
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label (2 ^ (t - 1))))
    false false ((), (none, (false, (none, false)))) ((), (none, (false, (none, false))))
    S2 S3 _ t3 u4 hr3 hrun4
  obtain ⟨u2, hu2, hrun2⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (cpSel.trans δ)) (dm345678 t δ)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel MatrixUnaryArithmetic.Label.outer)
    none none (false, ((), (none, (false, (none, false)))))
    (false, ((), (none, (false, (none, false))))) S1 S2 _ t2 u3 hr2 hrun3
  obtain ⟨u1, hu1, hrun1⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (cpV.trans δ)) (dm2345678 t δ)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, (false, ((), (none, (false, (none, false))))))
    (none, (false, ((), (none, (false, (none, false)))))) S S1 _ t1 u2 hr1 hrun2
  refine ⟨u1, ?_, _, hrun1⟩
  simp only [List.length_replicate] at ht1 ht2 ht5 ht7
  unfold dimsClock
  omega

/-- Value bridge: the two products are the admitted writer dimensions. -/
theorem dims_eq (v t b lambda : ℕ) :
    v * selectorCount t b lambda = Paper2.YaoMaterialization.rowCount v t b lambda ∧
      2 ^ b * 2 ^ (t - 1) * payloadCount t b lambda =
        Paper2.YaoMaterialization.columnCount t b lambda := by
  refine ⟨rfl, ?_⟩
  unfold Paper2.YaoMaterialization.columnCount
  ring

#print axioms physical_dims
#print axioms dims_eq

/-! ## The full prelude: counts, `K`, and the writer dimensions -/

/-- Dimension-stage names inside the prelude cells: `v` (0), `sel` (4), `pow` (3),
`pay` (5), outputs `r` (7), `c` (8), scratch 9..13. -/
def dims11 : Fin 11 ↪ Fin 22 := ⟨![0, 4, 3, 5, 7, 8, 9, 10, 11, 12, 13], by decide⟩

def dimsPlace {t lambda : ℕ} (θ : PCell t lambda ↪ J) : Fin 11 ↪ J :=
  (dims11.trans Function.Embedding.inr).trans θ

/-- The fixed full prelude program. -/
def preludeFull (t lambda : ℕ) (θ : PCell t lambda ↪ J) :=
  BitMachineRawSequence.program (prelude t lambda θ) (dimsProgram t (dimsPlace θ))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (preludeControl t lambda) dimsControl

def preludeFullOut {t lambda : ℕ} (θ : PCell t lambda ↪ J) (W : J → List Bool) (v e : ℕ) :
    J → List Bool :=
  Function.update (Function.update (preludeOut θ W e)
    (θ (.inr 7)) (List.replicate
      (Paper2.YaoMaterialization.rowCount v t (paddedEdgeBits e) lambda) true))
    (θ (.inr 8)) (List.replicate
      (Paper2.YaoMaterialization.columnCount t (paddedEdgeBits e) lambda) true)

def preludeFullClock (t lambda v e : ℕ) : ℕ :=
  preludeClock t lambda e +
    dimsClock t v (selectorCount t (paddedEdgeBits e) lambda) (Paper2.YaoLookup.paddedEdgeCount e)
      (payloadCount t (paddedEdgeBits e) lambda) + 1

/-- Y6 full main theorem: from charged unary `v` and `e`, one physical run of the
fixed full prelude writes `b`, `pow`, `sel`, `pay`, `K` and the writer dimensions
`r = rowCount v t b lambda`, `c = columnCount t b lambda`; exact exit bank. -/
theorem physical_prelude_full (t lambda : ℕ) (ht : 1 ≤ t) (θ : PCell t lambda ↪ J)
    (W : J → List Bool) (v e : ℕ)
    (hv : W (θ (.inr 0)) = List.replicate v true)
    (he : W (θ (.inr 1)) = List.replicate e true)
    (hs : ∀ i : Fin 22, 2 ≤ i.val → W (θ (.inr i)) = [])
    (hreg : ∀ k, W (θ (.inl k)) = []) :
    ∃ total ≤ preludeFullClock t lambda v e, ∃ c',
      ((advance (preludeFull t lambda θ))^[total])
        (⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
          (preludeControl t lambda, dimsControl), W⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, c', preludeFullOut θ W v e⟩ := by
  classical
  have hinj := θ.injective
  obtain ⟨t1, ht1, c1, hr1⟩ := physical_prelude t lambda ht θ W e he hs hreg
  have hd : ∀ k : Fin 11, 4 ≤ k.val → preludeOut θ W e (dimsPlace θ k) = [] := by
    intro k hk
    have hk' : 7 ≤ (dims11 k).val := by fin_cases k <;> simp_all [dims11]
    simp only [preludeOut, dimsPlace, Function.Embedding.trans_apply,
      Function.Embedding.inr_apply]
    rw [Function.update_of_ne (by simp [hinj.eq_iff]; omega),
      Function.update_of_ne (by simp [hinj.eq_iff]; omega),
      Function.update_of_ne (by simp [hinj.eq_iff]; omega),
      Function.update_of_ne (by simp [hinj.eq_iff]; omega),
      Function.update_of_ne (by simp [hinj.eq_iff]; omega)]
    exact hs _ (by omega)
  obtain ⟨t2, ht2, c2, hr2⟩ := physical_dims t (dimsPlace θ) (preludeOut θ W e) v
    (selectorCount t (paddedEdgeBits e) lambda) (Paper2.YaoLookup.paddedEdgeCount e)
    (payloadCount t (paddedEdgeBits e) lambda)
    (by simp [preludeOut, dimsPlace, dims11, hinj.eq_iff, hv])
    (by simp [preludeOut, dimsPlace, dims11, hinj.eq_iff])
    (by simp [preludeOut, dimsPlace, dims11, hinj.eq_iff])
    (by simp [preludeOut, dimsPlace, dims11, hinj.eq_iff]) hd
  have hout : Function.update (Function.update (preludeOut θ W e) (dimsPlace θ 4)
      (List.replicate (v * selectorCount t (paddedEdgeBits e) lambda) true))
      (dimsPlace θ 5) (List.replicate (Paper2.YaoLookup.paddedEdgeCount e * 2 ^ (t - 1) *
        payloadCount t (paddedEdgeBits e) lambda) true) = preludeFullOut θ W v e := by
    rw [(dims_eq v t (paddedEdgeBits e) lambda).1, Paper2.YaoLookup.paddedEdgeCount,
      (dims_eq v t (paddedEdgeBits e) lambda).2]
    rfl
  rw [hout] at hr2
  obtain ⟨u, hu, hrun⟩ := BitMachineRawSequence.runs (prelude t lambda θ)
    (dimsProgram t (dimsPlace θ))
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (preludeControl t lambda) c1 dimsControl c2 W (preludeOut θ W e) _ t1 t2 hr1 hr2
  exact ⟨u, by unfold preludeFullClock; omega, _, hrun⟩

#print axioms physical_prelude_full

end Paper2.YaoPrelude

end
