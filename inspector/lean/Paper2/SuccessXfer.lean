import Paper2.SuccessHeader
import Paper2.CopyAll

/-! Unit 3, segment (5): the charged transfer of the success bank into the writer bank.

Joint bank `JT = SuccessOrient.Stack ⊕ (HeaderJoin.JH WEntry.Kw ⊕ Fin 1)`: the success bank
left by the admitted `SuccessOrient.program` (`SuccessFetchJoin.post`), beside the owner-8
writer-then-header bank and one blank scratch cell.

`xfer` is ONE fixed program: owner-7 `CopyAll.prog` (a fixed family of the production
`MatrixStage4ScalarPreparationOps.copyProgram`, every handoff charged) with six copies

* success word (`fwCell`) -> writer sample-word cell (`fwA`),
* serialized level-`K` column code (`colCodeCell`) -> writer cell `cR 3`,
* serialized level-`K` row code (`rowCodeCell`) -> writer cell `cR 2`,
* unary `mY` (`colsCell`) -> writer cell `myA`, and again -> the writer's `cols` cell,
* unary `mX` (the fallback writer's retained `rows` cell) -> the writer's `rows` cell.

`xfer_run`: from the success bank beside the writer/header bank whose six destination cells
are BLANK (`preJH`), the run ends with the success bank unchanged beside exactly the owner-8
writer/header entry bank `hjIn (ready (bankW …) mX mY 0 0 0 0 [] output).contents thr`
(`finJH`), within `6 * (2 * xLmax + 3) + 1` steps. The other writer/header cells (master
region, unary `K`, the entry cells, the output prefix, the unary threshold) are untouched and
stay supplied. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.SuccessXfer

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries
open Paper2.HeaderJoin (JH hjIn hjProg wOut thrM scrH)

abbrev OS := SuccessOrient.Stack
abbrev JT := OS ⊕ (JH WEntry.Kw ⊕ Fin 1)

/-- The fallback writer's retained unary row count inside the success bank. -/
def rowsCell : OS := .inl (.inl CodeFallbackDimensionLoader.rows)

theorem fallbackBank_rows (n p s q₁ q₂ w Q k mX mY : Nat) (word : List Bool)
    (B R : Nat) (d : CodeTableFallback.Config)
    (G : SamplerParameterBank.Private → List Bool) (a : CodeFullPadding.Config)
    (hd : d.stk = Sum.elim a.stk (CodeTableFallback.writerData mX mY).contents) :
    SuccessOrient.fallbackBank n p s q₁ q₂ w Q k mX mY word B R d G rowsCell =
      List.replicate mX true := by
  change CodeFallbackSourceResult.finalBank n p s q₁ q₂ w Q k mX mY word B R d
    (CodeFallbackEntryBank.fallbackSlots (.inr (.inr .rows))) = _
  unfold CodeFallbackSourceResult.finalBank
  rw [bank_at, hd]
  rfl

/-- Writer cells inside the header-join bank. -/
def wAux (a : WEntry.Aux) : JH WEntry.Kw := .inl (.inl (.inl (WEntry.eqv a)))
def wRows : JH WEntry.Kw := .inl (.inr .rows)
def wCols : JH WEntry.Kw := .inl (.inr .cols)

def auxFw : WEntry.Aux := .inr (.inr (.inr 0))
def auxMy : WEntry.Aux := .inr (.inr (.inr 1))
def auxRc : WEntry.Aux := .inr (.inl 2)
def auxCc : WEntry.Aux := .inr (.inl 3)

def srcs : Fin 6 → OS := ![SuccessFetchJoin.fwCell, SuccessFetchJoin.colCodeCell,
  SuccessFetchJoin.rowCodeCell, SuccessFetchJoin.colsCell, SuccessFetchJoin.colsCell, rowsCell]
def dsts : Fin 6 → JH WEntry.Kw :=
  ![wAux auxFw, wAux auxCc, wAux auxRc, wAux auxMy, wCols, wRows]
def scrT : JT := .inr (.inr 0)

theorem dsts_inj : ∀ i j, dsts i = dsts j → i = j := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [dsts, wAux, wRows, wCols, auxFw, auxMy, auxRc, auxCc]

def cpf (i : Fin 6) : Fin 3 → JT := ![.inl (srcs i), .inr (.inl (dsts i)), scrT]

theorem cpf_inj (i : Fin 6) : Function.Injective (cpf i) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [cpf, scrT]

def cps (i : Fin 6) : Fin 3 ↪ JT := ⟨cpf i, cpf_inj i⟩

theorem cps_src (i : Fin 6) : cps i 0 = .inl (srcs i) := rfl
theorem cps_dst (i : Fin 6) : cps i 1 = .inr (.inl (dsts i)) := rfl
theorem cps_scr (i : Fin 6) : cps i 2 = scrT := rfl

/-- The fixed transfer program. -/
def xfer := CopyAll.prog cps

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The owner-8 writer/header entry bank. -/
def finJH (g : EncodedGraph.Graph) (r K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) (thr : ℕ) (output : List Bool) : JH WEntry.Kw → List Bool :=
  hjIn (MatrixTableWriter.ready (WEntry.bankW g r K mX mY xs ys) mX mY 0 0 0 0 []
    output).contents thr

/-- The same bank with the six transfer destinations blank. -/
def blank (W : JH WEntry.Kw → List Bool) : JH WEntry.Kw → List Bool :=
  fun a => if ∃ i, dsts i = a then [] else W a

theorem blank_dst (W : JH WEntry.Kw → List Bool) (i : Fin 6) : blank W (dsts i) = [] := by
  unfold blank
  rw [if_pos ⟨i, rfl⟩]

theorem blank_off (W : JH WEntry.Kw → List Bool) (a : JH WEntry.Kw)
    (h : ¬ ∃ i, dsts i = a) : blank W a = W a := by
  unfold blank
  rw [if_neg h]

/-- A bound on every transferred word. -/
def xLmax (g : EncodedGraph.Graph) (K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) : ℕ :=
  ((WEntry.colWords g K mY ys).flatten ++ (WEntry.rowWords g K mX xs).flatten).length +
    (encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q K).2).length +
    (encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q K).1).length + mY + mX

theorem finJH_dst (g : EncodedGraph.Graph) (r K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) (thr : ℕ) (output : List Bool) :
    finJH g r K mX mY xs ys thr output (dsts 0) =
        (WEntry.colWords g K mY ys).flatten ++ (WEntry.rowWords g K mX xs).flatten ∧
      finJH g r K mX mY xs ys thr output (dsts 1) =
        encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q K).2 ∧
      finJH g r K mX mY xs ys thr output (dsts 2) =
        encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q K).1 ∧
      finJH g r K mX mY xs ys thr output (dsts 3) = List.replicate mY true ∧
      finJH g r K mX mY xs ys thr output (dsts 4) = List.replicate mY true ∧
      finJH g r K mX mY xs ys thr output (dsts 5) = List.replicate mX true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [finJH, dsts, hjIn, wAux, wRows, wCols, MatrixTableWriter.Data.contents,
      MatrixTableWriter.Data.cell, MatrixTableWriter.ready,
      WEntry.bankW, Equiv.symm_apply_apply, Sum.elim_inl, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val] <;> rfl

theorem xfer_run (g : EncodedGraph.Graph) (r K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) (thr : ℕ) (output : List Bool) (P : OS → List Bool)
    (hfw : P SuccessFetchJoin.fwCell =
      (WEntry.colWords g K mY ys).flatten ++ (WEntry.rowWords g K mX xs).flatten)
    (hcc : P SuccessFetchJoin.colCodeCell =
      encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q K).2)
    (hrc : P SuccessFetchJoin.rowCodeCell =
      encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q K).1)
    (hcols : P SuccessFetchJoin.colsCell = List.replicate mY true)
    (hrows : P rowsCell = List.replicate mX true) :
    ∃ t ≤ 6 * (2 * xLmax g K mX mY xs ys + 3) + 1, ∃ v',
      ((advance xfer)^[t])
          (⟨some (.inl ⟨0, by omega⟩), (none : Option Bool),
            Sum.elim P (Sum.elim (blank (finJH g r K mX mY xs ys thr output)) (fun _ => []))⟩ :
            TM2.Cfg (fun _ : JT => Bool) _ _) =
        ⟨none, v', Sum.elim P (Sum.elim (finJH g r K mX mY xs ys thr output) (fun _ => []))⟩ := by
  let T : JT → List Bool :=
    Sum.elim P (Sum.elim (blank (finJH g r K mX mY xs ys thr output)) (fun _ => []))
  have hsd : ∀ i j, cps i 0 ≠ cps j 1 := by
    intro i j h
    rw [cps_src, cps_dst] at h
    cases h
  have hzd : ∀ i j, cps i 2 ≠ cps j 1 := by
    intro i j h
    rw [cps_scr, cps_dst] at h
    cases h
  have hdd : ∀ i j, cps i 1 = cps j 1 → i = j := by
    intro i j h
    rw [cps_dst, cps_dst] at h
    exact dsts_inj i j (Sum.inl_injective (Sum.inr_injective h))
  have hz : ∀ i, T (cps i 2) = [] := fun i => rfl
  have hv := finJH_dst g r K mX mY xs ys thr output
  have hL : ∀ i, (T (cps i 0)).length ≤ xLmax g K mX mY xs ys := by
    intro i
    rw [cps_src]
    change (P (srcs i)).length ≤ _
    unfold xLmax
    fin_cases i
    · change (P SuccessFetchJoin.fwCell).length ≤ _
      rw [hfw]; omega
    · change (P SuccessFetchJoin.colCodeCell).length ≤ _
      rw [hcc]; omega
    · change (P SuccessFetchJoin.rowCodeCell).length ≤ _
      rw [hrc]; omega
    · change (P SuccessFetchJoin.colsCell).length ≤ _
      rw [hcols, List.length_replicate]; omega
    · change (P SuccessFetchJoin.colsCell).length ≤ _
      rw [hcols, List.length_replicate]; omega
    · change (P rowsCell).length ≤ _
      rw [hrows, List.length_replicate]; omega
  obtain ⟨t, ht, v', hr⟩ := CopyAll.all_run cps hsd hzd hdd T hz
    (xLmax g K mX mY xs ys) hL none
  have hdone : CopyAll.done cps 6 T =
      Sum.elim P (Sum.elim (finJH g r K mX mY xs ys thr output) (fun _ => [])) := by
    funext x
    by_cases hx : ∃ j, cps j 1 = x
    · obtain ⟨j, rfl⟩ := hx
      rw [CopyAll.done_dst cps hdd T j, cps_src, cps_dst]
      change P (srcs j) ++ blank (finJH g r K mX mY xs ys thr output) (dsts j) =
        finJH g r K mX mY xs ys thr output (dsts j)
      rw [blank_dst, List.append_nil]
      fin_cases j
      · change P SuccessFetchJoin.fwCell = _
        rw [hfw]; exact hv.1.symm
      · change P SuccessFetchJoin.colCodeCell = _
        rw [hcc]; exact hv.2.1.symm
      · change P SuccessFetchJoin.rowCodeCell = _
        rw [hrc]; exact hv.2.2.1.symm
      · change P SuccessFetchJoin.colsCell = _
        rw [hcols]; exact hv.2.2.2.1.symm
      · change P SuccessFetchJoin.colsCell = _
        rw [hcols]; exact hv.2.2.2.2.1.symm
      · change P rowsCell = _
        rw [hrows]; exact hv.2.2.2.2.2.symm
    · rw [CopyAll.done_off cps T x (fun j h => hx ⟨j, h⟩)]
      rcases x with x | x | x
      · rfl
      · change blank (finJH g r K mX mY xs ys thr output) x = _
        apply blank_off
        rintro ⟨i, hi⟩
        exact hx ⟨i, by rw [cps_dst, hi]⟩
      · rfl
  refine ⟨t, ht, v', ?_⟩
  rw [← hdone]
  exact hr

end

#print axioms fallbackBank_rows
#print axioms dsts_inj
#print axioms finJH_dst
#print axioms xfer_run

end Paper2.SuccessXfer
