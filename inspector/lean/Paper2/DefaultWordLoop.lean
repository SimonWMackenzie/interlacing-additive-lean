import Paper2.DefaultColumnRound
import Paper2.CountedLoop
import Paper2.CanonicalDefaultRowRun

/-! Unit 3, segment (3) remainder item 1 / segment (5) "default tails":
the canonical default-word level loop. ONE fixed body program performs one
level of `CanonicalDefaultWordScratch.words`:
row round (production `RowMachine.program`, `row_run`) on the current column
word, column round (`DefaultColumnRound.program`) on the current row word,
then clears the consumed/junk cells and moves the two new words into the
level cells (source-preserving copies, charged clears). `CountedLoop.loop`
runs it `j` times from the seed `words 0`; the exit bank holds exactly
`words j` (row and column/tail word). -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.DefaultWordLoop

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)
open Paper2.CanonicalDefaultWordScratch (repeatWord words successor_words)

abbrev RMS := CanonicalDefaultWordScratch.RowMachine.Stack
abbrev CRK := DefaultColumnRound.K
abbrev LB := RMS ⊕ (CRK ⊕ Fin 2)

def bk (a : RMS → List Bool) (b : CRK → List Bool) (d : Fin 2 → List Bool) : LB → List Bool :=
  Sum.elim a (Sum.elim b d)

def iRM : RMS ↪ LB := ⟨Sum.inl, Sum.inl_injective⟩
def iCR : CRK ↪ LB := ⟨fun x => .inr (.inl x), fun a b h => by simpa using h⟩

theorem bank_RM (a : RMS → List Bool) (b : CRK → List Bool) (d : Fin 2 → List Bool)
    (T : RMS → List Bool) : bank iRM (bk a b d) T = bk T b d := by
  funext j
  rcases j with j | j
  · exact bank_at iRM _ _ j
  · exact bank_outside iRM _ _ _ (by rintro ⟨k, hk⟩; exact Sum.inl_ne_inr hk)

theorem bank_CR (a : RMS → List Bool) (b : CRK → List Bool) (d : Fin 2 → List Bool)
    (T : CRK → List Bool) : bank iCR (bk a b d) T = bk a T d := by
  funext j
  rcases j with j | j | j
  · exact bank_outside iCR _ _ _ (by rintro ⟨k, hk⟩; exact Sum.inr_ne_inl hk)
  · exact bank_at iCR _ _ j
  · exact bank_outside iCR _ _ _ (by
      rintro ⟨k, hk⟩
      exact Sum.inl_ne_inr (Sum.inr_injective hk))

theorem upd_RM (a : RMS → List Bool) (b : CRK → List Bool) (d : Fin 2 → List Bool)
    (i : RMS) (x : List Bool) :
    Function.update (bk a b d) (.inl i) x = bk (Function.update a i x) b d := by
  rw [bk, Sum.update_elim_inl]; rfl

theorem upd_CR (a : RMS → List Bool) (b : CRK → List Bool) (d : Fin 2 → List Bool)
    (i : CRK) (x : List Bool) :
    Function.update (bk a b d) (.inr (.inl i)) x = bk a (Function.update b i x) d := by
  rw [bk, Sum.update_elim_inr, Sum.update_elim_inl]; rfl

theorem upd_D (a : RMS → List Bool) (b : CRK → List Bool) (d : Fin 2 → List Bool)
    (i : Fin 2) (x : List Bool) :
    Function.update (bk a b d) (.inr (.inr i)) x = bk a b (Function.update d i x) := by
  rw [bk, Sum.update_elim_inr, Sum.update_elim_inr]; rfl

theorem lift {Kk L V : Type*} [DecidableEq Kk] (ι : Kk ↪ LB)
    (P : L → TM2.Stmt (fun _ : Kk => Bool) L V)
    (W : LB → List Bool) (S T : Kk → List Bool) (hS : ∀ k, S k = W (ι k)) (l : L) (v v' : V)
    (t : ℕ)
    (hrun : ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) =
      ⟨none, v', T⟩) :
    ((advance (fun l => stackStmt ι (P l)))^[t])
        (⟨some l, v, W⟩ : TM2.Cfg (fun _ : LB => Bool) L V) =
      ⟨none, v', bank ι W T⟩ := by
  have hs := BitMachineStackRun.run ι W P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) t
  rw [hrun] at hs
  simp only [stackCfg] at hs
  rwa [bank_eq_self ι W S hS] at hs

/-- Clear one cell. -/
def clr (k : LB) : Unit → TM2.Stmt (fun _ : LB => Bool) Unit (Option Bool) :=
  fun _ => pop k (fun _ b => b) (branch Option.isSome (goto (fun _ => ())) halt)

theorem clr_run (k : LB) : ∀ (xs : List Bool) (S : LB → List Bool)
    (v : Option Bool), S k = xs →
    ((advance (clr k))^[xs.length + 1]) (⟨some (), v, S⟩ :
        TM2.Cfg (fun _ : LB => Bool) Unit (Option Bool)) =
      ⟨none, none, Function.update S k []⟩
  | [], S, v, hS => by
      have hS' : Function.update S k [] = S := by rw [← hS]; exact Function.update_eq_self _ _
      simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, clr, hS, hS']
  | b :: xs, S, v, hS => by
      rw [show (b :: xs).length + 1 = (xs.length + 1) + 1 by simp, Function.iterate_add_apply]
      have e : ((advance (clr k))^[1]) (⟨some (), v, S⟩ :
          TM2.Cfg (fun _ : LB => Bool) Unit (Option Bool)) =
          ⟨some (), some b, Function.update S k xs⟩ := by
        simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, clr, hS]
      rw [e, clr_run k xs (Function.update S k xs) (some b) (by simp)]
      simp

def crR : LB := .inr (.inl (.inr 0))
def crJ : LB := .inr (.inl (.inl 0))
def crOut : LB := .inr (.inl (.inl 3))
def ctrC : LB := .inr (.inr 0)
def scr : LB := .inr (.inr 1)

def rowSlots : Fin 3 ↪ LB := ⟨![.inl 7, crR, scr], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [crR, scr]⟩
def colSlots : Fin 3 ↪ LB := ⟨![crOut, .inl 3, scr], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [crOut, scr]⟩

def rmP := fun l => stackStmt iRM (CanonicalDefaultWordScratch.RowMachine.program l)
def crP := fun l => stackStmt iCR (DefaultColumnRound.program l)
def cpRow := MatrixStage4ScalarPreparationOps.copyProgram rowSlots
def cpCol := MatrixStage4ScalarPreparationOps.copyProgram colSlots

abbrev oc := (none : Option Bool)
def labelOf {L σ Kk : Type*} (_P : L → TM2.Stmt (fun _ : Kk => Bool) L σ) (l : L) : L := l
def crStart := labelOf DefaultColumnRound.program
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
    (leftLabel BitMachineCopy.Label.scan)))))))

def k1 := (oc, DefaultColumnRound.startCtl)
def k2 := (k1, oc)
def k3 := (k2, oc)
def k4 := (k3, oc)
def k5 := (k4, oc)
def k6 := (k5, oc)
def k7 := (k6, oc)
def k8 := (k7, oc)

def b1 := BitMachineRawSequence.program rmP crP crStart oc DefaultColumnRound.startCtl
def b2 := BitMachineRawSequence.program b1 (clr (.inl 3)) () k1 oc
def b3 := BitMachineRawSequence.program b2 (clr (.inl 6)) () k2 oc
def b4 := BitMachineRawSequence.program b3 (clr crR) () k3 oc
def b5 := BitMachineRawSequence.program b4 (clr crJ) () k4 oc
def b6 := BitMachineRawSequence.program b5 cpRow .scan k5 oc
def b7 := BitMachineRawSequence.program b6 (clr (.inl 7)) () k6 oc
def b8 := BitMachineRawSequence.program b7 cpCol .scan k7 oc
/-- The level body: ONE fixed program. -/
def body := BitMachineRawSequence.program b8 (clr crOut) () k8 oc
def bodyCtl := (k8, oc)

/-- Level bank: unary `q₁, s, Q` and the column word in the row machine's
cells, the row word and unary `w` in the column round's cells, the loop
counter. -/
def S (q₁ s Q w : ℕ) (R C ctr : List Bool) : LB → List Bool :=
  bk (CanonicalDefaultWordScratch.RowMachine.B (List.replicate q₁ true) (List.replicate s true)
      (List.replicate Q true) C [] [] [] [] [] [])
    (DefaultColumnRound.B [] [] [] [] [] R (List.replicate w true) []) ![ctr, []]

end

end Paper2.DefaultWordLoop
