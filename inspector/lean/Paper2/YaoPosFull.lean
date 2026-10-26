import Paper2.YaoPosPlace
import EthInapproximability.CurrentPaper.MatrixUnaryArithmetic
import EthInapproximability.CurrentPaper.ExactParameterBranchInstall
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Unit 5 segment Y3, full (lane a-yao-owner-1): the position machine with its
input producers charged.

Consumer: the one-entry callback Y5.  One fixed program `program ι`
(placement `ι : Fin 13 ↪ J` only).  Preserved inputs: 0 the exact body stream
(Y2 work cell when the code cell holds the code alone, R-Y2), 1 unary `a`
(Y4 output), 2 unary `K` (the Yao scalar loader's constant / Y6),
3 unary `vertex` (Y4 output).  Six stages with five charged handoffs
(`BitMachineRawSequence.runs`): copy body; copy `a`; copy `K`; unary
multiplication `a*K` (admitted `MatrixUnaryArithmetic` outer+clear phases);
copy `K`; the placed Y3 lookup.  Exit bank exact: only cell 9 changes, to
unary `(positionEval (paddedEdgesEval edges) a vertex).val`; every scratch
cell returns to `[]`. -/

namespace Paper2.YaoPositionFull

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.UnaryFieldListParserScratch
open Paper2.YaoSourceCodec
open Paper2.YaoLookup

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## Embedded multiplication (outer + clear phases) -/

noncomputable def mulProgram {K : Type*} [DecidableEq K] (ι : Fin 4 ↪ K)
    (l : MatrixUnaryArithmetic.Label) :
    TM2.Stmt (fun _ : K => Bool) MatrixUnaryArithmetic.Label Bool :=
  BitMachineStackEmbedding.stmt ι id id id none (MatrixUnaryArithmetic.program l)

theorem mul_run {K : Type*} [DecidableEq K] (ι : Fin 4 ↪ K) (S : K → List Bool) (n m : ℕ)
    (h0 : S (ι 0) = List.replicate m true) (h1 : S (ι 1) = List.replicate n true)
    (h2 : S (ι 2) = []) (h3 : S (ι 3) = []) :
    ∃ t ≤ n * (2 * m + 3) + 1 + (m + 1),
      ((advance (mulProgram ι))^[t])
        (⟨some .outer, false, S⟩ :
          TM2.Cfg (fun _ : K => Bool) MatrixUnaryArithmetic.Label Bool) =
        ⟨none, false, Function.update (Function.update (Function.update S (ι 0) [])
          (ι 1) []) (ι 2) (List.replicate (n * m) true)⟩ := by
  classical
  let c := MatrixUnaryArithmetic.cfg (some .outer) false (List.replicate m true)
    (List.replicate n true) [] []
  have hbank : BitMachineStackEmbedding.bank ι S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;> simp [c, MatrixUnaryArithmetic.cfg, MatrixUnaryArithmetic.stackContents,
      h0, h1, h2, h3]
  have ho := MatrixUnaryArithmetic.outer_correct n m 0 false
  have hc := MatrixUnaryArithmetic.clear_correct (List.replicate m true)
    (List.replicate (n * m) true) false
  simp only [List.replicate_zero, Nat.add_zero, List.length_replicate] at ho hc
  have hrun : ((advance MatrixUnaryArithmetic.program)^[(m + 1) + (n * (2 * m + 3) + 1)]) c =
      MatrixUnaryArithmetic.cfg none false [] [] (List.replicate (n * m) true) [] := by
    rw [Function.iterate_add_apply]
    change MatrixUnaryArithmetic.run (m + 1) (MatrixUnaryArithmetic.run _ c) = _
    rw [ho, hc]
  have hhalt : (((advance MatrixUnaryArithmetic.program)^[(m + 1) + (n * (2 * m + 3) + 1)])
      c).l = none := by rw [hrun]; rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs ι S id id id (fun _ => rfl) none
    MatrixUnaryArithmetic.program (mulProgram ι) (by intro l; rfl) c _ hhalt
  rw [hrun] at he
  change ((advance (mulProgram ι))^[t])
      ⟨some .outer, false, BitMachineStackEmbedding.bank ι S c.stk⟩ =
      ⟨none, false, BitMachineStackEmbedding.bank ι S
        (MatrixUnaryArithmetic.cfg none false [] [] (List.replicate (n * m) true) []).stk⟩ at he
  have hupdate : (MatrixUnaryArithmetic.cfg none false [] [] (List.replicate (n * m) true)
      []).stk = Function.update (Function.update (Function.update c.stk 0 []) 1 []) 2
        (List.replicate (n * m) true) := by
    funext k
    fin_cases k <;> simp [c, MatrixUnaryArithmetic.cfg, MatrixUnaryArithmetic.stackContents]
  rw [hbank, hupdate, BitMachineStackEmbedding.bank_update,
    BitMachineStackEmbedding.bank_update, BitMachineStackEmbedding.bank_update, hbank] at he
  exact ⟨t, by omega, he⟩

/-! ## Cells and the fixed six-stage program -/

/-- Cells: 0 body (preserved), 1 `a` (preserved), 2 `K` (preserved),
3 `vertex` (preserved), 4 body copy, 5 `a*K`, 6 `K` copy (lookup counter),
7 restore scratch, 8 flag, 9 output, 10 copy/multiply scratch,
11 `a` copy (multiply counter), 12 `K` copy (multiply operand). -/
def c3 (p q r : Fin 13) (h : Function.Injective ![p, q, r]) : Fin 3 ↪ Fin 13 := ⟨![p, q, r], h⟩

def copyBody : Fin 3 ↪ Fin 13 := c3 0 4 10 (by decide)
def copyA : Fin 3 ↪ Fin 13 := c3 1 11 10 (by decide)
def copyK1 : Fin 3 ↪ Fin 13 := c3 2 12 10 (by decide)
def mulSel : Fin 4 ↪ Fin 13 := ⟨![12, 11, 5, 10], by decide⟩
def copyK2 : Fin 3 ↪ Fin 13 := c3 2 6 10 (by decide)
def lookSel : Fin 7 ↪ Fin 13 := ⟨![4, 5, 6, 3, 7, 8, 9], by decide⟩

variable {J : Type*} [DecidableEq J]

noncomputable def st6 (ι : Fin 13 ↪ J) := Paper2.YaoPositionLookup.placedProgram (lookSel.trans ι)

noncomputable def st56 (ι : Fin 13 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (copyK2.trans ι))
    (st6 ι) Paper2.YaoPositionLookup.Label.skipLoop none none

noncomputable def st456 (ι : Fin 13 ↪ J) :=
  BitMachineRawSequence.program (mulProgram (mulSel.trans ι)) (st56 ι)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) false (none, none)

noncomputable def st3456 (ι : Fin 13 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (copyK1.trans ι))
    (st456 ι) (BitMachineRawSequence.leftLabel MatrixUnaryArithmetic.Label.outer) none
    (false, (none, none))

noncomputable def st23456 (ι : Fin 13 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (copyA.trans ι))
    (st3456 ι) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none
    (none, (false, (none, none)))

/-- The fixed Y3 program (placement only). -/
noncomputable def program (ι : Fin 13 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (copyBody.trans ι))
    (st23456 ι) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none
    (none, (none, (false, (none, none))))

def startControl : Option Bool × (Option Bool × (Option Bool × (Bool × (Option Bool ×
    Option Bool)))) :=
  (none, (none, (none, (false, (none, none)))))

/-- Y3 main theorem (full): the fixed program computes unary `positionEval`
from the preserved body, `a`, `K`, `vertex` cells, with every producer charged. -/
theorem physical_position (ι : Fin 13 ↪ J) (W : J → List Bool) {t v e : ℕ}
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (a : Fin (paddedEdgeCount e)) (vertex : Fin v)
    (h0 : W (ι 0) = tokens (List.ofFn (flatten edges)))
    (h1 : W (ι 1) = List.replicate a.val true)
    (h2 : W (ι 2) = List.replicate (arity t) true)
    (h3 : W (ι 3) = List.replicate vertex.val true)
    (h4 : W (ι 4) = []) (h5 : W (ι 5) = []) (h6 : W (ι 6) = []) (h7 : W (ι 7) = [])
    (h8 : W (ι 8) = []) (h9 : W (ι 9) = []) (h10 : W (ι 10) = []) (h11 : W (ι 11) = [])
    (h12 : W (ι 12) = []) :
    ∃ total ≤ (2 * (tokens (List.ofFn (flatten edges))).length + 2) + (2 * a.val + 2) +
        (2 * arity t + 2) + (a.val * (2 * arity t + 3) + 1 + (arity t + 1)) +
        (2 * arity t + 2) +
        (2 * (a.val * arity t) + 5 * (tokens (List.ofFn (flatten edges))).length +
          arity t * (3 * vertex.val + 6) + arity t + 6) + 5,
      ∃ c',
      ((advance (program ι))^[total])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), startControl, W⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, c', Function.update W (ι 9)
          (List.replicate (positionEval (paddedEdgesEval edges) a vertex).val true)⟩ := by
  classical
  have hinj := ι.injective
  set body := tokens (List.ofFn (flatten edges)) with hbody
  -- stage 1: copy the body
  obtain ⟨t1, ht1, hr1⟩ := ExactParameterBranchInstall.copy_run (copyBody.trans ι) W body
    (by simp [copyBody, c3, h0]) (by simp [copyBody, c3, h4]) (by simp [copyBody, c3, h10])
  set W1 := Function.update W ((copyBody.trans ι) 1) body with hW1
  -- stage 2: copy a
  obtain ⟨t2, ht2, hr2⟩ := ExactParameterBranchInstall.copy_run (copyA.trans ι) W1
    (List.replicate a.val true)
    (by simp [hW1, copyBody, copyA, c3, Function.update_apply, hinj.eq_iff, h1])
    (by simp [hW1, copyBody, copyA, c3, Function.update_apply, hinj.eq_iff, h11])
    (by simp [hW1, copyBody, copyA, c3, Function.update_apply, hinj.eq_iff, h10])
  set W2 := Function.update W1 ((copyA.trans ι) 1) (List.replicate a.val true) with hW2
  -- stage 3: copy K (multiply operand)
  obtain ⟨t3, ht3, hr3⟩ := ExactParameterBranchInstall.copy_run (copyK1.trans ι) W2
    (List.replicate (arity t) true)
    (by simp [hW2, hW1, copyBody, copyA, copyK1, c3, Function.update_apply, hinj.eq_iff, h2])
    (by simp [hW2, hW1, copyBody, copyA, copyK1, c3, Function.update_apply, hinj.eq_iff, h12])
    (by simp [hW2, hW1, copyBody, copyA, copyK1, c3, Function.update_apply, hinj.eq_iff, h10])
  set W3 := Function.update W2 ((copyK1.trans ι) 1) (List.replicate (arity t) true) with hW3
  -- stage 4: multiply a*K
  obtain ⟨t4, ht4, hr4⟩ := mul_run (mulSel.trans ι) W3 a.val (arity t)
    (by simp [hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, c3, Function.update_apply,
      hinj.eq_iff])
    (by simp [hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, c3, Function.update_apply,
      hinj.eq_iff])
    (by simp [hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, c3, Function.update_apply,
      hinj.eq_iff, h5])
    (by simp [hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, c3, Function.update_apply,
      hinj.eq_iff, h10])
  set W4 := Function.update (Function.update (Function.update W3 ((mulSel.trans ι) 0) [])
    ((mulSel.trans ι) 1) []) ((mulSel.trans ι) 2) (List.replicate (a.val * arity t) true)
    with hW4
  -- stage 5: copy K (lookup counter)
  obtain ⟨t5, ht5, hr5⟩ := ExactParameterBranchInstall.copy_run (copyK2.trans ι) W4
    (List.replicate (arity t) true)
    (by simp [hW4, hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, copyK2, c3,
      Function.update_apply, hinj.eq_iff, h2])
    (by simp [hW4, hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, copyK2, c3,
      Function.update_apply, hinj.eq_iff, h6])
    (by simp [hW4, hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, copyK2, c3,
      Function.update_apply, hinj.eq_iff, h10])
  set W5 := Function.update W4 ((copyK2.trans ι) 1) (List.replicate (arity t) true) with hW5
  -- stage 6: the placed lookup
  obtain ⟨t6, ht6, hr6⟩ := Paper2.YaoPositionLookup.placed_position_lookup (lookSel.trans ι) W5
    edges a vertex
    (by simp [hW5, hW4, hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, copyK2, lookSel, c3,
      Function.update_apply, hinj.eq_iff, hbody])
    (by simp [hW5, hW4, hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, copyK2, lookSel, c3,
      Function.update_apply, hinj.eq_iff])
    (by simp [hW5, hW4, hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, copyK2, lookSel, c3,
      Function.update_apply, hinj.eq_iff])
    (by simp [hW5, hW4, hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, copyK2, lookSel, c3,
      Function.update_apply, hinj.eq_iff, h3])
    (by simp [hW5, hW4, hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, copyK2, lookSel, c3,
      Function.update_apply, hinj.eq_iff, h7])
    (by simp [hW5, hW4, hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, copyK2, lookSel, c3,
      Function.update_apply, hinj.eq_iff, h8])
    (by simp [hW5, hW4, hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, copyK2, lookSel, c3,
      Function.update_apply, hinj.eq_iff, h9])
  have hfinal : Function.update (Function.update (Function.update (Function.update W5
      ((lookSel.trans ι) 0) []) ((lookSel.trans ι) 1) []) ((lookSel.trans ι) 2) [])
      ((lookSel.trans ι) 6)
        (List.replicate (positionEval (paddedEdgesEval edges) a vertex).val true) =
      Function.update W (ι 9)
        (List.replicate (positionEval (paddedEdgesEval edges) a vertex).val true) := by
    funext j
    by_cases hj : ∃ k, ι k = j
    · obtain ⟨k, rfl⟩ := hj
      fin_cases k <;>
        simp [hW5, hW4, hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, copyK2, lookSel, c3,
          Function.update_apply, hinj.eq_iff, h4, h5, h6, h10, h11, h12]
    · have hne : ∀ k, j ≠ ι k := fun k hk => hj ⟨k, hk.symm⟩
      simp [hW5, hW4, hW3, hW2, hW1, copyBody, copyA, copyK1, mulSel, copyK2, lookSel, c3,
        Function.update_apply, hne]
  rw [hfinal] at hr6
  obtain ⟨u5, hu5, hrun5⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (copyK2.trans ι)) (st6 ι)
    BitMachineCopy.Label.scan Paper2.YaoPositionLookup.Label.skipLoop none none none none
    W4 W5 _ t5 t6 hr5 hr6
  obtain ⟨u4, hu4, hrun4⟩ := BitMachineRawSequence.runs (mulProgram (mulSel.trans ι)) (st56 ι)
    MatrixUnaryArithmetic.Label.outer (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    false false (none, none) (none, none) W3 W4 _ t4 u5 hr4 hrun5
  obtain ⟨u3, hu3, hrun3⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (copyK1.trans ι)) (st456 ι)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel MatrixUnaryArithmetic.Label.outer)
    none none (false, (none, none)) (false, (none, none)) W2 W3 _ t3 u4 hr3 hrun4
  obtain ⟨u2, hu2, hrun2⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (copyA.trans ι)) (st3456 ι)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, (false, (none, none))) (none, (false, (none, none))) W1 W2 _ t2 u3 hr2 hrun3
  obtain ⟨u1, hu1, hrun1⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (copyBody.trans ι)) (st23456 ι)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, (none, (false, (none, none)))) (none, (none, (false, (none, none))))
    W W1 _ t1 u2 hr1 hrun2
  refine ⟨u1, ?_, _, hrun1⟩
  simp only [List.length_replicate] at ht2 ht3 ht5
  rw [← hbody] at ht6
  omega

#print axioms mul_run
#print axioms physical_position

end Paper2.YaoPositionFull
