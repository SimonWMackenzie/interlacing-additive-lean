import EthInapproximability.CurrentPaper.MatrixWeightedColumnController

/-!
# One finite controller for four protected row supports

This fixed program preserves the original writer row coordinate on slot 20,
copies it through a quotient-by-one run to work slot 23, performs three unary
support-boundary cuts, and divides by the selected support's copy count.
The terminal finite control records which of the four support groups was
selected.  Translation of vertex/auxiliary labels through `ItemOrder` into
the raw Stage--4 row ordinal is a separate physical lookup obligation.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedRowController

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := MatrixWeightedColumnController.Stack

inductive Label where
  | copyInit | copy (l : MatrixIndexQuotient.Label) | cut1Init
  | cut1 (l : MatrixUnaryCut.Label) | dispatch1
  | cut2Init | cut2 (l : MatrixUnaryCut.Label) | dispatch2
  | cut3Init | cut3 (l : MatrixUnaryCut.Label) | dispatch3
  | groupInit (g : Fin 4) | group (g : Fin 4) (l : MatrixIndexQuotient.Label)
  | groupDone (g : Fin 4)
  deriving DecidableEq, Fintype

inductive State where
  | quotient (v : MatrixIndexQuotient.Control)
  | cut (v : MatrixUnaryCut.Control)
  | chosen (g : Fin 4)
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label State

def initial : State := .quotient MatrixIndexQuotient.initial
def getQuotient : State → MatrixIndexQuotient.Control
  | .quotient v => v
  | _ => MatrixIndexQuotient.initial
def getCut : State → MatrixUnaryCut.Control
  | .cut v => v
  | _ => (false,true)
def cutFlag : State → Bool
  | .cut v => v.1
  | _ => false

def copySlots : Fin 8 ↪ Stack where
  toFun := ![20,63,55,56,57,58,23,59]
  inj' := by decide

def cutSlots (i : Fin 3) : Fin 4 ↪ Stack where
  toFun := ![23, (![47,48,49] : Fin 3 → Stack) i,61,62]
  inj' := by fin_cases i <;> decide

def groupDivisor (g : Fin 4) : Stack := ![50,51,52,53] g

def groupSlots (g : Fin 4) : Fin 8 ↪ Stack where
  toFun := ![23,groupDivisor g,55,56,57,58,54,59]
  inj' := by fin_cases g <;> decide

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label State
  | .copyInit => push 63 (fun _ => true)
      (goto (fun _ => .copy MatrixIndexQuotient.start))
  | .copy l => stmt copySlots Label.copy State.quotient getQuotient
      (some .cut1Init) (MatrixIndexQuotient.program l)
  | .cut1Init => load (fun _ => .cut (false,true))
      (goto (fun _ => .cut1 .scan))
  | .cut1 l => stmt (cutSlots 0) Label.cut1 State.cut getCut
      (some .dispatch1) (MatrixUnaryCut.program l)
  | .dispatch1 => branch cutFlag
      (goto (fun _ => .cut2Init)) (goto (fun _ => .groupInit 0))
  | .cut2Init => load (fun _ => .cut (false,true))
      (goto (fun _ => .cut2 .scan))
  | .cut2 l => stmt (cutSlots 1) Label.cut2 State.cut getCut
      (some .dispatch2) (MatrixUnaryCut.program l)
  | .dispatch2 => branch cutFlag
      (goto (fun _ => .cut3Init)) (goto (fun _ => .groupInit 1))
  | .cut3Init => load (fun _ => .cut (false,true))
      (goto (fun _ => .cut3 .scan))
  | .cut3 l => stmt (cutSlots 2) Label.cut3 State.cut getCut
      (some .dispatch3) (MatrixUnaryCut.program l)
  | .dispatch3 => branch cutFlag
      (goto (fun _ => .groupInit 3)) (goto (fun _ => .groupInit 2))
  | .groupInit g => load (fun _ => .quotient MatrixIndexQuotient.initial)
      (goto (fun _ => .group g MatrixIndexQuotient.start))
  | .group g l => stmt (groupSlots g) (Label.group g) State.quotient getQuotient
      (some (.groupDone g)) (MatrixIndexQuotient.program l)
  | .groupDone g => load (fun _ => .chosen g) halt

def start : Label := .copyInit
def cfg (l : Option Label) (v : State) (S : Stack → List Bool) : Config := ⟨l,v,S⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

/-- The row index and seven metadata words are physical unary inputs.  Every
private work bank of this controller begins empty. -/
def seed (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ) : Stack → List Bool :=
  fun k =>
    if k = 20 then List.replicate row true
    else if k = 47 then List.replicate b₁ true
    else if k = 48 then List.replicate b₂ true
    else if k = 49 then List.replicate b₃ true
    else if k = 50 then List.replicate c₀ true
    else if k = 51 then List.replicate c₁ true
    else if k = 52 then List.replicate c₂ true
    else if k = 53 then List.replicate c₃ true
    else if k = 23 ∨ k = 54 ∨ k = 55 ∨ k = 56 ∨ k = 57 ∨
      k = 58 ∨ k = 59 ∨ k = 61 ∨ k = 62 ∨ k = 63 then []
    else foreign k

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem run_succ {c d : Config} (h : advance program c = d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, h]

/-- A quotient stage embedded in the row controller, with all unrelated
metadata banks untouched. -/
theorem embedded_quotient (ι : Fin 8 ↪ Stack)
    (labels : MatrixIndexQuotient.Label → Label) (next : Label)
    (hprogram : ∀ l, program (labels l) =
      stmt ι labels State.quotient getQuotient (some next)
        (MatrixIndexQuotient.program l))
    (S : Stack → List Bool) (n m : ℕ)
    (h0 : S (ι 0) = List.replicate n true)
    (h1 : S (ι 1) = List.replicate m true)
    (hrest : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 → S (ι k) = []) :
    ∃ t ≤ 11 * n + 3 * m + 7,
      run t (cfg (some (labels MatrixIndexQuotient.start))
        (.quotient MatrixIndexQuotient.initial) S) =
      cfg (some next) (.quotient MatrixIndexQuotient.initial)
        (Function.update S (ι 6) (List.replicate (n / m) true)) := by
  let lc := MatrixIndexQuotient.cfg (some MatrixIndexQuotient.start)
    MatrixIndexQuotient.initial (List.replicate n true)
    (List.replicate m true) [] [] [] [] [] []
  have hlocal (k : Fin 8) : lc.stk k = S (ι k) := by
    fin_cases k <;> simp [lc, MatrixIndexQuotient.cfg, h0, h1, hrest]
  have hstart : BitMachineStackEmbedding.cfg ι S labels State.quotient
      (some next) lc =
      cfg (some (labels MatrixIndexQuotient.start))
        (.quotient MatrixIndexQuotient.initial) S := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
      BitMachineInline.cfg cfg
    congr 1
    exact bank_eq_self ι S lc.stk hlocal
  obtain ⟨t₀, ht₀, he₀⟩ := MatrixIndexQuotient.quotient_run n m
  have hhalt : ((advance MatrixIndexQuotient.program)^[t₀] lc).l = none := by
    rw [← MatrixIndexQuotient.run, he₀]
    rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs ι S labels
    State.quotient getQuotient (by intro v; rfl) (some next)
    MatrixIndexQuotient.program program hprogram lc t₀ hhalt
  refine ⟨t, ht.trans ht₀, ?_⟩
  rw [← hstart]
  change ((advance program)^[t]) _ = _
  rw [he, ← MatrixIndexQuotient.run, he₀]
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg cfg
  congr 1
  have houtput :
      (MatrixIndexQuotient.cfg none MatrixIndexQuotient.initial
        (List.replicate n true) (List.replicate m true)
        [] [] [] [] (List.replicate (n / m) true) []).stk =
      Function.update lc.stk 6 (List.replicate (n / m) true) := by
    funext k
    fin_cases k <;> simp [lc, MatrixIndexQuotient.cfg]
  rw [houtput, bank_update]
  exact congrArg (fun f => Function.update f (ι 6)
    (List.replicate (n / m) true))
     (bank_eq_self ι S lc.stk hlocal)

theorem embedded_cut (ι : Fin 4 ↪ Stack)
    (labels : MatrixUnaryCut.Label → Label) (next : Label)
    (hprogram : ∀ l, program (labels l) =
      stmt ι labels State.cut getCut (some next) (MatrixUnaryCut.program l))
    (S : Stack → List Bool) (n threshold : ℕ)
    (h0 : S (ι 0) = List.replicate n true)
    (h1 : S (ι 1) = List.replicate threshold true)
    (hrest : ∀ k : Fin 4, k ≠ 0 → k ≠ 1 → S (ι k) = []) :
    ∃ t ≤ 3 * min n threshold + 4,
      run t (cfg (some (labels .scan)) (.cut (false,true)) S) =
      cfg (some next) (.cut (decide (threshold ≤ n), false))
        (Function.update S (ι 0)
          (List.replicate (if n < threshold then n else n - threshold) true)) := by
  let lc := MatrixUnaryCut.cfg (some .scan) (false,true)
    (List.replicate n true) (List.replicate threshold true) [] []
  have hlocal (k : Fin 4) : lc.stk k = S (ι k) := by
    fin_cases k <;> simp [lc, MatrixUnaryCut.cfg, h0, h1, hrest]
  have hstart : BitMachineStackEmbedding.cfg ι S labels State.cut
      (some next) lc =
      cfg (some (labels .scan)) (.cut (false,true)) S := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
      BitMachineInline.cfg cfg
    congr 1
    exact bank_eq_self ι S lc.stk hlocal
  obtain ⟨t₀, ht₀, he₀⟩ := MatrixUnaryCut.cut_run n threshold
  have hhalt : ((advance MatrixUnaryCut.program)^[t₀] lc).l = none := by
    rw [← MatrixUnaryCut.run, he₀]
    rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs ι S labels
    State.cut getCut (by intro v; rfl) (some next)
    MatrixUnaryCut.program program hprogram lc t₀ hhalt
  refine ⟨t, ht.trans ht₀, ?_⟩
  rw [← hstart]
  change ((advance program)^[t]) _ = _
  rw [he, ← MatrixUnaryCut.run, he₀]
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg cfg
  congr 1
  have houtput :
      (MatrixUnaryCut.cfg none (decide (threshold ≤ n), false)
        (List.replicate (if n < threshold then n else n - threshold) true)
        (List.replicate threshold true) [] []).stk =
      Function.update lc.stk 0
        (List.replicate (if n < threshold then n else n - threshold) true) := by
    funext k
    fin_cases k <;> simp [lc, MatrixUnaryCut.cfg]
  rw [houtput, bank_update]
  exact congrArg (fun f => Function.update f (ι 0)
    (List.replicate (if n < threshold then n else n - threshold) true))
    (bank_eq_self ι S lc.stk hlocal)

def afterCopy (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ) : Stack → List Bool :=
  Function.update (Function.update
    (seed foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃) 63 [true])
    23 (List.replicate row true)

theorem copy_run (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ) :
    ∃ t ≤ 11 * row + 11,
      run t (cfg (some start) initial
        (seed foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg (some .cut1Init) (.quotient MatrixIndexQuotient.initial)
        (afterCopy foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃) := by
  let S := Function.update (seed foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃) 63 [true]
  have h0 : S (copySlots 0) = List.replicate row true := by
    simp [S, copySlots, seed]
  have h1 : S (copySlots 1) = List.replicate 1 true := by
    simp [S, copySlots]
  have hrest : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 → S (copySlots k) = [] := by
    intro k hk0 hk1
    fin_cases k <;> simp_all [S, copySlots, seed]
  obtain ⟨tq, htq, hq⟩ := embedded_quotient copySlots Label.copy .cut1Init
    (by intro l; rfl) S row 1 h0 h1 hrest
  have hstep : advance program
      (cfg (some start) initial
        (seed foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg (some (.copy MatrixIndexQuotient.start))
        (.quotient MatrixIndexQuotient.initial) S := by
    simp [advance, TM2.step, TM2.stepAux, program, start, initial, cfg, S,
      seed]
  refine ⟨tq + 1, by omega, ?_⟩
  rw [run_succ hstep tq]
  simpa [afterCopy, S] using hq

def afterCut1 (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ) : Stack → List Bool :=
  Function.update (afterCopy foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)
    23 (List.replicate (if row < b₁ then row else row - b₁) true)

theorem cut1_run (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ) :
    ∃ t ≤ 3 * min row b₁ + 5,
      run t (cfg (some .cut1Init) (.quotient MatrixIndexQuotient.initial)
        (afterCopy foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg (some .dispatch1) (.cut (decide (b₁ ≤ row), false))
        (afterCut1 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃) := by
  let S := afterCopy foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃
  have h0 : S (cutSlots 0 0) = List.replicate row true := by
    simp [S, afterCopy, cutSlots]
  have h1 : S (cutSlots 0 1) = List.replicate b₁ true := by
    simp [S, afterCopy, cutSlots, seed]
  have hrest : ∀ k : Fin 4, k ≠ 0 → k ≠ 1 → S (cutSlots 0 k) = [] := by
    intro k hk0 hk1
    fin_cases k <;> simp_all [S, afterCopy, cutSlots, seed]
  obtain ⟨tc, htc, hc⟩ := embedded_cut (cutSlots 0) Label.cut1 .dispatch1
    (by intro l; rfl) S row b₁ h0 h1 hrest
  have hstep : advance program
      (cfg (some .cut1Init) (.quotient MatrixIndexQuotient.initial) S) =
      cfg (some (.cut1 .scan)) (.cut (false,true)) S := rfl
  refine ⟨tc + 1, by omega, ?_⟩
  rw [run_succ hstep tc]
  simpa [S, afterCut1, afterCopy, cutSlots] using hc

def afterCut2 (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ) : Stack → List Bool :=
  Function.update (afterCut1 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)
    23 (List.replicate
      (if row - b₁ < b₂ then row - b₁ else row - b₁ - b₂) true)

def afterCut3 (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ) : Stack → List Bool :=
  Function.update (afterCut2 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)
    23 (List.replicate
      (if row - b₁ - b₂ < b₃ then row - b₁ - b₂
        else row - b₁ - b₂ - b₃) true)

theorem cut2_run (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ) (h₁ : b₁ ≤ row) :
    ∃ t ≤ 3 * min (row - b₁) b₂ + 6,
      run t (cfg (some .dispatch1) (.cut (true,false))
        (afterCut1 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg (some .dispatch2) (.cut (decide (b₂ ≤ row - b₁), false))
        (afterCut2 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃) := by
  let S := afterCut1 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃
  have h0 : S (cutSlots 1 0) = List.replicate (row - b₁) true := by
    simp [S, afterCut1, cutSlots, show ¬row < b₁ by omega]
  have h1 : S (cutSlots 1 1) = List.replicate b₂ true := by
    simp [S, afterCut1, afterCopy, cutSlots, seed]
  have hrest : ∀ k : Fin 4, k ≠ 0 → k ≠ 1 → S (cutSlots 1 k) = [] := by
    intro k hk0 hk1
    fin_cases k <;> simp_all [S, afterCut1, afterCopy, cutSlots, seed]
  obtain ⟨tc, htc, hc⟩ := embedded_cut (cutSlots 1) Label.cut2 .dispatch2
    (by intro l; rfl) S (row - b₁) b₂ h0 h1 hrest
  have hdispatch : advance program (cfg (some .dispatch1) (.cut (true,false)) S) =
      cfg (some .cut2Init) (.cut (true,false)) S := by
    simp [advance, TM2.step, TM2.stepAux, program, cutFlag, cfg]
  have hinit : advance program (cfg (some .cut2Init) (.cut (true,false)) S) =
      cfg (some (.cut2 .scan)) (.cut (false,true)) S := rfl
  have htwo : run 2 (cfg (some .dispatch1) (.cut (true,false)) S) =
      cfg (some (.cut2 .scan)) (.cut (false,true)) S := by
    simp only [run, Function.iterate_succ_apply, Function.iterate_zero,
      id_eq]
    rw [hdispatch, hinit]
  refine ⟨2 + tc, by omega, ?_⟩
  rw [run_add htwo]
  simpa [S, afterCut2, afterCut1, cutSlots] using hc

theorem cut3_run (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ)
    (h₁ : b₁ ≤ row) (h₂ : b₂ ≤ row - b₁) :
    ∃ t ≤ 3 * min (row - b₁ - b₂) b₃ + 6,
      run t (cfg (some .dispatch2) (.cut (true,false))
        (afterCut2 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg (some .dispatch3)
        (.cut (decide (b₃ ≤ row - b₁ - b₂), false))
        (afterCut3 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃) := by
  let S := afterCut2 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃
  have h0 : S (cutSlots 2 0) =
      List.replicate (row - b₁ - b₂) true := by
    simp [S, afterCut2, cutSlots, show ¬row - b₁ < b₂ by omega]
  have h1 : S (cutSlots 2 1) = List.replicate b₃ true := by
    simp [S, afterCut2, afterCut1, afterCopy, cutSlots, seed]
  have hrest : ∀ k : Fin 4, k ≠ 0 → k ≠ 1 → S (cutSlots 2 k) = [] := by
    intro k hk0 hk1
    fin_cases k <;> simp_all [S, afterCut2, afterCut1, afterCopy,
      cutSlots, seed]
  obtain ⟨tc, htc, hc⟩ := embedded_cut (cutSlots 2) Label.cut3 .dispatch3
    (by intro l; rfl) S (row - b₁ - b₂) b₃ h0 h1 hrest
  have hdispatch : advance program (cfg (some .dispatch2) (.cut (true,false)) S) =
      cfg (some .cut3Init) (.cut (true,false)) S := by
    simp [advance, TM2.step, TM2.stepAux, program, cutFlag, cfg]
  have hinit : advance program (cfg (some .cut3Init) (.cut (true,false)) S) =
      cfg (some (.cut3 .scan)) (.cut (false,true)) S := rfl
  have htwo : run 2 (cfg (some .dispatch2) (.cut (true,false)) S) =
      cfg (some (.cut3 .scan)) (.cut (false,true)) S := by
    simp only [run, Function.iterate_succ_apply, Function.iterate_zero,
      id_eq]
    rw [hdispatch, hinit]
  refine ⟨2 + tc, by omega, ?_⟩
  rw [run_add htwo]
  simpa [S, afterCut3, afterCut2, cutSlots] using hc

/-- The selected support's copy multiplicity is divided by a real fixed
program, and the support-label ordinal is delivered in stack 54. -/
theorem group_run (S : Stack → List Bool) (g : Fin 4) (n divisor : ℕ)
    (v : State)
    (h0 : S 23 = List.replicate n true)
    (h1 : S (groupDivisor g) = List.replicate divisor true)
    (hrest : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 → S (groupSlots g k) = []) :
    ∃ t ≤ 11 * n + 3 * divisor + 9,
      run t (cfg (some (.groupInit g)) v S) =
      cfg none (.chosen g)
        (Function.update S 54 (List.replicate (n / divisor) true)) := by
  obtain ⟨tq, htq, hq⟩ := embedded_quotient (groupSlots g)
    (Label.group g) (.groupDone g) (by intro l; rfl) S n divisor
    (by simpa [groupSlots] using h0)
    (by simpa [groupSlots] using h1) hrest
  have hinit : advance program
      (cfg (some (.groupInit g)) v S) =
      cfg (some (.group g MatrixIndexQuotient.start))
        (.quotient MatrixIndexQuotient.initial) S := rfl
  refine ⟨tq + 2, by omega, ?_⟩
  rw [show tq + 2 = 1 + tq + 1 by omega]
  rw [show 1 + tq + 1 = 1 + (tq + 1) by omega]
  rw [run_add (show run 1
    (cfg (some (.groupInit g)) v S) =
    cfg (some (.group g MatrixIndexQuotient.start))
      (.quotient MatrixIndexQuotient.initial) S from hinit) (tq + 1)]
  rw [run_add hq 1]
  simp [run, advance, TM2.step, program, cfg, groupSlots]

theorem group_after_dispatch (S : Stack → List Bool) (g : Fin 4)
    (l : Label) (v v' : State) (n divisor : ℕ)
    (hdispatch : advance program (cfg (some l) v S) =
      cfg (some (.groupInit g)) v' S)
    (h0 : S 23 = List.replicate n true)
    (h1 : S (groupDivisor g) = List.replicate divisor true)
    (hrest : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 → S (groupSlots g k) = []) :
    ∃ t ≤ 11 * n + 3 * divisor + 10,
      run t (cfg (some l) v S) =
      cfg none (.chosen g)
        (Function.update S 54 (List.replicate (n / divisor) true)) := by
  obtain ⟨tg, htg, hg⟩ := group_run S g n divisor v' h0 h1 hrest
  refine ⟨tg + 1, by omega, ?_⟩
  rw [run_succ hdispatch tg]
  exact hg

theorem full_branch_run (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ) (hfull : row < b₁) :
    ∃ t ≤ 11 * row + 3 * c₀ + 10,
      run t (cfg (some .dispatch1)
        (.cut (decide (b₁ ≤ row), false))
        (afterCut1 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg none (.chosen 0)
        (Function.update (afterCut1 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)
          54 (List.replicate (row / c₀) true)) := by
  let S := afterCut1 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃
  have hdispatch : advance program
      (cfg (some .dispatch1) (.cut (decide (b₁ ≤ row), false)) S) =
      cfg (some (.groupInit 0)) (.cut (false,false)) S := by
    simp [advance, TM2.step, TM2.stepAux, program, cutFlag,
      show decide (b₁ ≤ row) = false by simp [Nat.not_le.mpr hfull], cfg]
  have h0 : S 23 = List.replicate row true := by
    simp [S, afterCut1, hfull]
  have h1 : S (groupDivisor 0) = List.replicate c₀ true := by
    simp [S, afterCut1, afterCopy, groupDivisor, seed]
  have hrest : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 → S (groupSlots 0 k) = [] := by
    intro k hk0 hk1
    fin_cases k <;> simp_all [S, afterCut1, afterCopy,
      groupSlots, seed]
  simpa [S] using group_after_dispatch S 0 .dispatch1
    (.cut (decide (b₁ ≤ row), false)) (.cut (false,false)) row c₀
    hdispatch h0 h1 hrest

theorem template_branch_run (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ)
    (h₁ : b₁ ≤ row) (htemplate : row - b₁ < b₂) :
    ∃ t ≤ 11 * (row - b₁) + 3 * c₁ + 10,
      run t (cfg (some .dispatch2)
        (.cut (decide (b₂ ≤ row - b₁), false))
        (afterCut2 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg none (.chosen 1)
        (Function.update (afterCut2 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)
          54 (List.replicate ((row - b₁) / c₁) true)) := by
  let S := afterCut2 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃
  have hdispatch : advance program
      (cfg (some .dispatch2) (.cut (decide (b₂ ≤ row - b₁), false)) S) =
      cfg (some (.groupInit 1)) (.cut (false,false)) S := by
    simp [advance, TM2.step, TM2.stepAux, program, cutFlag,
      show decide (b₂ ≤ row - b₁) = false by
        simp [Nat.not_le.mpr htemplate], cfg]
  have h0 : S 23 = List.replicate (row - b₁) true := by
    simp [S, afterCut2, htemplate]
  have h1 : S (groupDivisor 1) = List.replicate c₁ true := by
    simp [S, afterCut2, afterCut1, afterCopy, groupDivisor, seed]
  have hrest : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 → S (groupSlots 1 k) = [] := by
    intro k hk0 hk1
    fin_cases k <;> simp_all [S, afterCut2, afterCut1, afterCopy,
      groupSlots, seed]
  simpa [S] using group_after_dispatch S 1 .dispatch2
    (.cut (decide (b₂ ≤ row - b₁), false)) (.cut (false,false))
    (row - b₁) c₁ hdispatch h0 h1 hrest

theorem vertex_branch_run (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ)
    (h₁ : b₁ ≤ row) (h₂ : b₂ ≤ row - b₁)
    (hvertex : row - b₁ - b₂ < b₃) :
    ∃ t ≤ 11 * (row - b₁ - b₂) + 3 * c₂ + 10,
      run t (cfg (some .dispatch3)
        (.cut (decide (b₃ ≤ row - b₁ - b₂), false))
        (afterCut3 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg none (.chosen 2)
        (Function.update (afterCut3 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)
          54 (List.replicate ((row - b₁ - b₂) / c₂) true)) := by
  let S := afterCut3 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃
  have hdispatch : advance program
      (cfg (some .dispatch3)
        (.cut (decide (b₃ ≤ row - b₁ - b₂), false)) S) =
      cfg (some (.groupInit 2)) (.cut (false,false)) S := by
    simp [advance, TM2.step, TM2.stepAux, program, cutFlag,
      show decide (b₃ ≤ row - b₁ - b₂) = false by
        simp [Nat.not_le.mpr hvertex], cfg]
  have h0 : S 23 = List.replicate (row - b₁ - b₂) true := by
    simp [S, afterCut3, hvertex]
  have h1 : S (groupDivisor 2) = List.replicate c₂ true := by
    simp [S, afterCut3, afterCut2, afterCut1, afterCopy, groupDivisor, seed]
  have hrest : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 → S (groupSlots 2 k) = [] := by
    intro k hk0 hk1
    fin_cases k <;> simp_all [S, afterCut3, afterCut2, afterCut1,
      afterCopy, groupSlots, seed]
  simpa [S] using group_after_dispatch S 2 .dispatch3
    (.cut (decide (b₃ ≤ row - b₁ - b₂), false)) (.cut (false,false))
    (row - b₁ - b₂) c₂ hdispatch h0 h1 hrest

theorem auxiliary_branch_run (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ)
    (h₁ : b₁ ≤ row) (h₂ : b₂ ≤ row - b₁)
    (haux : b₃ ≤ row - b₁ - b₂) :
    ∃ t ≤ 11 * (row - b₁ - b₂ - b₃) + 3 * c₃ + 10,
      run t (cfg (some .dispatch3)
        (.cut (decide (b₃ ≤ row - b₁ - b₂), false))
        (afterCut3 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg none (.chosen 3)
        (Function.update (afterCut3 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)
          54 (List.replicate ((row - b₁ - b₂ - b₃) / c₃) true)) := by
  let S := afterCut3 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃
  have hdispatch : advance program
      (cfg (some .dispatch3)
        (.cut (decide (b₃ ≤ row - b₁ - b₂), false)) S) =
      cfg (some (.groupInit 3)) (.cut (true,false)) S := by
    simp [advance, TM2.step, TM2.stepAux, program, cutFlag,
      show decide (b₃ ≤ row - b₁ - b₂) = true by simp [haux], cfg]
  have h0 : S 23 = List.replicate (row - b₁ - b₂ - b₃) true := by
    simp [S, afterCut3, show ¬row - b₁ - b₂ < b₃ by omega]
  have h1 : S (groupDivisor 3) = List.replicate c₃ true := by
    simp [S, afterCut3, afterCut2, afterCut1, afterCopy, groupDivisor, seed]
  have hrest : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 → S (groupSlots 3 k) = [] := by
    intro k hk0 hk1
    fin_cases k <;> simp_all [S, afterCut3, afterCut2, afterCut1,
      afterCopy, groupSlots, seed]
  simpa [S] using group_after_dispatch S 3 .dispatch3
    (.cut (decide (b₃ ≤ row - b₁ - b₂), false)) (.cut (true,false))
    (row - b₁ - b₂ - b₃) c₃ hdispatch h0 h1 hrest

theorem prefix1_run (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ) :
    ∃ t ≤ (11 * row + 11) + (3 * min row b₁ + 5),
      run t (cfg (some start) initial
        (seed foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg (some .dispatch1) (.cut (decide (b₁ ≤ row), false))
        (afterCut1 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃) := by
  obtain ⟨tc, htc, hc⟩ := copy_run foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃
  obtain ⟨t₁, ht₁, h₁⟩ := cut1_run foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃
  exact ⟨tc + t₁, by omega, (run_add hc t₁).trans h₁⟩

theorem prefix2_run (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ) (h₁ : b₁ ≤ row) :
    ∃ t ≤ (11 * row + 11) + (3 * min row b₁ + 5) +
      (3 * min (row - b₁) b₂ + 6),
      run t (cfg (some start) initial
        (seed foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg (some .dispatch2) (.cut (decide (b₂ ≤ row - b₁), false))
        (afterCut2 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃) := by
  obtain ⟨t₁, ht₁, he₁⟩ := prefix1_run foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃
  obtain ⟨t₂, ht₂, he₂⟩ := cut2_run foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃ h₁
  have he₁' : run t₁ (cfg (some start) initial
      (seed foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg (some .dispatch1) (.cut (true,false))
        (afterCut1 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃) := by
    simpa [h₁] using he₁
  exact ⟨t₁ + t₂, by omega, (run_add he₁' t₂).trans he₂⟩

theorem prefix3_run (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ)
    (h₁ : b₁ ≤ row) (h₂ : b₂ ≤ row - b₁) :
    ∃ t ≤ (11 * row + 11) + (3 * min row b₁ + 5) +
      (3 * min (row - b₁) b₂ + 6) +
      (3 * min (row - b₁ - b₂) b₃ + 6),
      run t (cfg (some start) initial
        (seed foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg (some .dispatch3)
        (.cut (decide (b₃ ≤ row - b₁ - b₂), false))
        (afterCut3 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃) := by
  obtain ⟨t₂, ht₂, he₂⟩ := prefix2_run foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃ h₁
  obtain ⟨t₃, ht₃, he₃⟩ := cut3_run foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃ h₁ h₂
  have he₂' : run t₂ (cfg (some start) initial
      (seed foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg (some .dispatch2) (.cut (true,false))
        (afterCut2 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃) := by
    simpa [h₂] using he₂
  exact ⟨t₂ + t₃, by omega, (run_add he₂' t₃).trans he₃⟩

theorem full_controller_run (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ) (hfull : row < b₁) :
    ∃ t ≤ (11 * row + 11) + (3 * min row b₁ + 5) +
      (11 * row + 3 * c₀ + 10),
      run t (cfg (some start) initial
        (seed foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg none (.chosen 0)
        (Function.update (afterCut1 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)
          54 (List.replicate (row / c₀) true)) := by
  obtain ⟨tp, htp, hp⟩ := prefix1_run foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃
  obtain ⟨tb, htb, hb⟩ := full_branch_run foreign row b₁ b₂ b₃
    c₀ c₁ c₂ c₃ hfull
  exact ⟨tp + tb, by omega, (run_add hp tb).trans hb⟩

theorem template_controller_run (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ)
    (h₁ : b₁ ≤ row) (htemplate : row - b₁ < b₂) :
    ∃ t ≤ (11 * row + 11) + (3 * min row b₁ + 5) +
      (3 * min (row - b₁) b₂ + 6) +
      (11 * (row - b₁) + 3 * c₁ + 10),
      run t (cfg (some start) initial
        (seed foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg none (.chosen 1)
        (Function.update (afterCut2 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)
          54 (List.replicate ((row - b₁) / c₁) true)) := by
  obtain ⟨tp, htp, hp⟩ := prefix2_run foreign row b₁ b₂ b₃
    c₀ c₁ c₂ c₃ h₁
  obtain ⟨tb, htb, hb⟩ := template_branch_run foreign row b₁ b₂ b₃
    c₀ c₁ c₂ c₃ h₁ htemplate
  exact ⟨tp + tb, by omega, (run_add hp tb).trans hb⟩

theorem vertex_controller_run (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ)
    (h₁ : b₁ ≤ row) (h₂ : b₂ ≤ row - b₁)
    (hvertex : row - b₁ - b₂ < b₃) :
    ∃ t ≤ (11 * row + 11) + (3 * min row b₁ + 5) +
      (3 * min (row - b₁) b₂ + 6) +
      (3 * min (row - b₁ - b₂) b₃ + 6) +
      (11 * (row - b₁ - b₂) + 3 * c₂ + 10),
      run t (cfg (some start) initial
        (seed foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg none (.chosen 2)
        (Function.update (afterCut3 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)
          54 (List.replicate ((row - b₁ - b₂) / c₂) true)) := by
  obtain ⟨tp, htp, hp⟩ := prefix3_run foreign row b₁ b₂ b₃
    c₀ c₁ c₂ c₃ h₁ h₂
  obtain ⟨tb, htb, hb⟩ := vertex_branch_run foreign row b₁ b₂ b₃
    c₀ c₁ c₂ c₃ h₁ h₂ hvertex
  exact ⟨tp + tb, by omega, (run_add hp tb).trans hb⟩

theorem auxiliary_controller_run (foreign : Stack → List Bool) (row : ℕ)
    (b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℕ)
    (h₁ : b₁ ≤ row) (h₂ : b₂ ≤ row - b₁)
    (haux : b₃ ≤ row - b₁ - b₂) :
    ∃ t ≤ (11 * row + 11) + (3 * min row b₁ + 5) +
      (3 * min (row - b₁) b₂ + 6) +
      (3 * min (row - b₁ - b₂) b₃ + 6) +
      (11 * (row - b₁ - b₂ - b₃) + 3 * c₃ + 10),
      run t (cfg (some start) initial
        (seed foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)) =
      cfg none (.chosen 3)
        (Function.update (afterCut3 foreign row b₁ b₂ b₃ c₀ c₁ c₂ c₃)
          54 (List.replicate
            ((row - b₁ - b₂ - b₃) / c₃) true)) := by
  obtain ⟨tp, htp, hp⟩ := prefix3_run foreign row b₁ b₂ b₃
    c₀ c₁ c₂ c₃ h₁ h₂
  obtain ⟨tb, htb, hb⟩ := auxiliary_branch_run foreign row b₁ b₂ b₃
    c₀ c₁ c₂ c₃ h₁ h₂ haux
  exact ⟨tp + tb, by omega, (run_add hp tb).trans hb⟩

end EthInapproximability.CurrentPaper.MatrixWeightedRowController
