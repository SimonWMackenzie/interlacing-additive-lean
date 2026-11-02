import Paper2.YaoWriterPhase
import Paper2.YaoPrelDims
import Paper2.YaoHdrParse

/-! Unit 5 segment Y9, machine (lane a-yao-owner-2): ONE fixed program per
`(t, lambda)`, `1 ≤ t`, from the encoded Yao source `encode x` (Option B codec,
valid upstream code, R-Y2) and the raw tape `bits.val` to the printed table
`(materialize t lambda x.2.2 bits).bits` in the writer's output cell.

Stack type: the admitted writer's `MatrixTableWriter.Stack (YK t lambda)`, foreign bank
`Fin (YK t lambda)`, `YK t lambda = Fintype.card (Cells t lambda)`,
`Cells t lambda = InputStack t lambda ⊕ (CStack t lambda ⊕ Fin 40)`.
Named static cells `sN i`: 0 code, 1 body stream, 2 header scratch, 3..24 the prelude's
`Fin 22` cells (3 `v`, 4 `e`, 5 `b`, 6 `pow`, 7 `sel`, 8 `pay`, 9 `K`, 10 `r`, 11 `c`,
12..24 scratch), 25..38 the callback's scratch, 39 copy scratch.

Stages (four charged handoffs): Y2 `physical_header`; Y6 `physical_prelude_full`;
two charged copies `r → rows`, `c → cols`; the admitted writer (`write_rowMajor`) with the
Y5 callback `entryProgram` (`entry_runs_gen`).  Exit bank exact. -/

noncomputable section

namespace Paper2.YaoMachine

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoLookup
open Paper2.YaoEntryControllerJoin
open Paper2.YaoCtrlBlock
open Paper2.YaoMaterialization
open Paper2.UnaryFieldListParserScratch
open Paper2.YaoSourceCodec
open Paper2.YaoOneEntry
open Paper2.YaoPrelude
open Paper2.YaoHeaderParser

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384
set_option linter.unusedSimpArgs false

abbrev Cells (t lambda : ℕ) := InputStack t lambda ⊕ (CStack t lambda ⊕ Fin 40)
abbrev YK (t lambda : ℕ) : ℕ := Fintype.card (Cells t lambda)
abbrev WStack (t lambda : ℕ) := MatrixTableWriter.Stack (YK t lambda)

def cellOf {t lambda : ℕ} (c : Cells t lambda) : Fin (YK t lambda) :=
  Fintype.equivFin (Cells t lambda) c

def st {t lambda : ℕ} (c : Cells t lambda) : WStack t lambda := .inl (.inl (cellOf c))
def sN {t lambda : ℕ} (i : Fin 40) : WStack t lambda := st (.inr (.inr i))

theorem st_injective {t lambda : ℕ} : Function.Injective (st (t := t) (lambda := lambda)) := by
  intro a b h
  simp only [st, Sum.inl.injEq] at h
  exact (Fintype.equivFin _).injective h

/-! ## Placements -/

/-- Callback names 3..22 inside the forty static names. -/
def omap : Fin 23 → Fin 40 :=
  ![0, 0, 0, 7, 8, 6, 9, 4, 1, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]

theorem omap_inj : ∀ i j : Fin 23, 3 ≤ i.val → 3 ≤ j.val → omap i = omap j → i = j := by
  decide

def omegaFun (t lambda : ℕ) :
    InputStack t lambda ⊕ Fin 23 → MatrixTableWriter.CellStack (YK t lambda)
  | .inl k => .inl (cellOf (.inl k))
  | .inr i => if h : i.val < 3 then .inr ⟨i.val, h⟩ else .inl (cellOf (.inr (.inr (omap i))))

theorem omegaFun_injective (t lambda : ℕ) : Function.Injective (omegaFun t lambda) := by
  have hq := (Fintype.equivFin (Cells t lambda)).injective
  intro a b h
  rcases a with k | i <;> rcases b with k' | j <;> simp only [omegaFun] at h
  · simp only [Sum.inl.injEq, cellOf] at h
    exact congrArg Sum.inl (Sum.inl_injective (hq h))
  · by_cases hj : j.val < 3
    · rw [dif_pos hj] at h; exact absurd h (by simp)
    · rw [dif_neg hj] at h
      simp only [Sum.inl.injEq, cellOf] at h
      exact absurd (hq h) (by simp)
  · by_cases hi : i.val < 3
    · rw [dif_pos hi] at h; exact absurd h (by simp)
    · rw [dif_neg hi] at h
      simp only [Sum.inl.injEq, cellOf] at h
      exact absurd (hq h) (by simp)
  · by_cases hi : i.val < 3 <;> by_cases hj : j.val < 3
    · rw [dif_pos hi, dif_pos hj] at h
      simp only [Sum.inr.injEq, Fin.mk.injEq] at h
      exact congrArg Sum.inr (Fin.ext h)
    · rw [dif_pos hi, dif_neg hj] at h; exact absurd h (by simp)
    · rw [dif_neg hi, dif_pos hj] at h; exact absurd h (by simp)
    · rw [dif_neg hi, dif_neg hj] at h
      simp only [Sum.inl.injEq, cellOf] at h
      have h2 := hq h
      simp only [Sum.inr.injEq] at h2
      exact congrArg Sum.inr (omap_inj i j (by omega) (by omega) h2)

/-- The callback placement in the writer's cell stacks. -/
def omegaPlace (t lambda : ℕ) :
    InputStack t lambda ⊕ Fin 23 ↪ MatrixTableWriter.CellStack (YK t lambda) :=
  ⟨omegaFun t lambda, omegaFun_injective t lambda⟩

/-- The prelude's twenty-two names inside the forty static names. -/
def thetaIdx : Fin 22 → Fin 40 :=
  ![3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]

theorem thetaIdx_injective : Function.Injective thetaIdx := by decide

def thetaFun (t lambda : ℕ) : PCell t lambda → WStack t lambda
  | .inl k => st (.inr (.inl k))
  | .inr i => sN (thetaIdx i)

theorem thetaFun_injective (t lambda : ℕ) : Function.Injective (thetaFun t lambda) := by
  intro a b h
  rcases a with k | i <;> rcases b with k' | j <;> simp only [thetaFun, sN] at h <;>
    have h' := st_injective h <;> simp only [Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at h'
  · exact congrArg Sum.inl h'
  · exact congrArg Sum.inr (thetaIdx_injective h')

/-- The prelude placement. -/
def thetaPlace (t lambda : ℕ) : PCell t lambda ↪ WStack t lambda :=
  ⟨thetaFun t lambda, thetaFun_injective t lambda⟩

def s5 (t lambda : ℕ) : Fin 5 ↪ WStack t lambda :=
  ⟨fun i => sN ⟨i.val, by omega⟩, by
    intro i j h
    have := st_injective h
    simp only [Sum.inr.injEq, Fin.mk.injEq] at this
    exact Fin.ext this⟩

def cpRows (t lambda : ℕ) : Fin 3 ↪ WStack t lambda :=
  ⟨![sN 10, .inr .rows, sN 39], by
    intro i j h; fin_cases i <;> fin_cases j <;>
      simp_all [sN, st, cellOf, (Fintype.equivFin (Cells t lambda)).injective.eq_iff]⟩
def cpCols (t lambda : ℕ) : Fin 3 ↪ WStack t lambda :=
  ⟨![sN 11, .inr .cols, sN 39], by
    intro i j h; fin_cases i <;> fin_cases j <;>
      simp_all [sN, st, cellOf, (Fintype.equivFin (Cells t lambda)).injective.eq_iff]⟩

/-! ## The generalized callback instance -/

/-- `EntryRuns` for every static bank holding the callback's inputs. -/
theorem entry_runs_gen {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda) (bank : Fin (YK t lambda) → List Bool)
    (hsel : bank (cellOf (.inr (.inr 7))) =
      List.replicate (selectorCount t (paddedEdgeBits e) lambda) true)
    (hpay : bank (cellOf (.inr (.inr 8))) =
      List.replicate (payloadCount t (paddedEdgeBits e) lambda) true)
    (hpow : bank (cellOf (.inr (.inr 6))) = List.replicate (paddedEdgeCount e) true)
    (hK : bank (cellOf (.inr (.inr 9))) = List.replicate (arity t) true)
    (he : bank (cellOf (.inr (.inr 4))) = List.replicate e true)
    (hbody : bank (cellOf (.inr (.inr 1))) = tokens (List.ofFn (flatten edges)))
    (hs : ∀ i : Fin 40, 25 ≤ i.val → i.val ≤ 38 → bank (cellOf (.inr (.inr i))) = [])
    (hreg : ∀ k, bank (cellOf (.inl k)) = tapeOnly bits.val k) :
    MatrixTableWriter.EntryRuns (entryProgram (omegaPlace t lambda))
      (BitMachineRawSequence.leftLabel Paper2.YaoIndexDecoder.startLabel)
      (entryControl t lambda) bank
      (rowCount v t (paddedEdgeBits e) lambda) (columnCount t (paddedEdgeBits e) lambda)
      (Paper2.YaoEntryRuns.yaoT t lambda edges) (Paper2.YaoEntryRuns.yaoEntry t lambda edges bits) := by
  classical
  intro x hx y hy
  set B : MatrixTableWriter.CellStack (YK t lambda) → List Bool :=
    Sum.elim bank (![List.replicate x true, List.replicate y true, []] : Fin 3 → List Bool) with hB
  obtain ⟨n, hn, c', hr⟩ := physical_one_entry t lambda edges bits (omegaPlace t lambda) B x y
    hx hy (by simp [hB, omegaPlace, omegaFun]) (by simp [hB, omegaPlace, omegaFun])
    (by simp [hB, omegaPlace, omegaFun])
    (by simpa [hB, omegaPlace, omegaFun, omap] using hsel)
    (by simpa [hB, omegaPlace, omegaFun, omap] using hpay)
    (by simpa [hB, omegaPlace, omegaFun, omap] using hpow)
    (by simpa [hB, omegaPlace, omegaFun, omap] using hK)
    (by simpa [hB, omegaPlace, omegaFun, omap] using he)
    (by simpa [hB, omegaPlace, omegaFun, omap] using hbody)
    (by
      intro i hi
      have h3 : ¬ i.val < 3 := by omega
      have hr1 : 25 ≤ (omap i).val := by revert hi; revert i; decide
      have hr2 : (omap i).val ≤ 38 := by revert hi; revert i; decide
      simpa [hB, omegaPlace, omegaFun, h3] using hs (omap i) hr1 hr2)
    (by intro k; simpa [hB, omegaPlace, omegaFun] using hreg k)
  refine ⟨n, hn.trans (entryClock_mono _ _ _ _ hx.le hy.le), c', ?_⟩
  refine hr.trans ?_
  unfold MatrixTableWriter.cellCfg
  congr 1
  have hent : Paper2.YaoEntryRuns.yaoEntry t lambda edges bits x y =
      (materialize t lambda edges bits).matrix ⟨x, hx⟩ ⟨y, hy⟩ := by
    simp [Paper2.YaoEntryRuns.yaoEntry, hx, hy]
  rw [hent]
  funext j
  rcases j with n' | i
  · simp [hB, omegaPlace, omegaFun]
  · fin_cases i <;> simp [hB, omegaPlace, omegaFun]

#print axioms omegaFun_injective
#print axioms thetaFun_injective
#print axioms entry_runs_gen

end Paper2.YaoMachine

end
