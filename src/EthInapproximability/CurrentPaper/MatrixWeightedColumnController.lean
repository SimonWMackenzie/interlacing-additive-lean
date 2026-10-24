import EthInapproximability.CurrentPaper.MatrixWeightedRowOuterDecode
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# One finite controller for the protected column's copy-free address

The controller executes the *halting* quotient machine on the uniform-copy
digit, physically cuts at the 182-weight boundary, and executes a second
quotient with the selected 182D or 2M divisor.  Its full branch yields the raw
column ordinal directly.  Its diagonal branch yields the second-row ordinal
for the separately compiled diagonal-address subroutine.  Work stack slots
are statically assigned; no natural number is stored in finite control.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedColumnController

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := Fin 64
abbrev QuotientLabel := MatrixIndexQuotient.Label
abbrev CutLabel := MatrixUnaryCut.Label

inductive Label where
  | outer (l : QuotientLabel)
  | cutInit | cut (l : CutLabel) | dispatch
  | fullInit | full (l : QuotientLabel) | fullDone
  | diagonalInit | diagonal (l : QuotientLabel) | diagonalDone
  deriving DecidableEq, Fintype

inductive State where
  | quotient (v : MatrixIndexQuotient.Control)
  | cut (v : MatrixUnaryCut.Control)
  | terminal (diagonal : Bool)
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

def outerSlots : Fin 8 ↪ Stack where
  toFun := ![0,1,7,8,9,10,2,11]
  inj' := by decide

def cutSlots : Fin 4 ↪ Stack where
  toFun := ![2,3,12,13]
  inj' := by decide

def fullSlots : Fin 8 ↪ Stack where
  toFun := ![2,4,7,8,9,10,19,11]
  inj' := by decide

def diagonalSlots : Fin 8 ↪ Stack where
  toFun := ![2,6,7,8,9,10,5,11]
  inj' := by decide

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label State
  | .outer l => stmt outerSlots Label.outer State.quotient getQuotient
      (some .cutInit) (MatrixIndexQuotient.program l)
  | .cutInit => load (fun _ => .cut (false,true))
      (goto (fun _ => .cut .scan))
  | .cut l => stmt cutSlots Label.cut State.cut getCut
      (some .dispatch) (MatrixUnaryCut.program l)
  | .dispatch => branch cutFlag
      (goto (fun _ => .diagonalInit)) (goto (fun _ => .fullInit))
  | .fullInit => load (fun _ => .quotient MatrixIndexQuotient.initial)
      (goto (fun _ => .full MatrixIndexQuotient.start))
  | .full l => stmt fullSlots Label.full State.quotient getQuotient
      (some .fullDone) (MatrixIndexQuotient.program l)
  | .fullDone => load (fun _ => .terminal false) halt
  | .diagonalInit => load (fun _ => .quotient MatrixIndexQuotient.initial)
      (goto (fun _ => .diagonal MatrixIndexQuotient.start))
  | .diagonal l => stmt diagonalSlots Label.diagonal State.quotient getQuotient
      (some .diagonalDone) (MatrixIndexQuotient.program l)
  | .diagonalDone => load (fun _ => .terminal true) halt

def start : Label := .outer MatrixIndexQuotient.start
def cfg (l : Option Label) (v : State) (S : Stack → List Bool) : Config := ⟨l,v,S⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

/-- The caller's metadata and payload banks are at slots `20..63`; only the
displayed operand words are seeded at low slots. -/
def seed (foreign : Stack → List Bool)
    (ordinal uniform boundary fullDiv diagonalDiv : ℕ) : Stack → List Bool :=
  fun k =>
    if k = 0 then List.replicate ordinal true
    else if k = 1 then List.replicate uniform true
    else if k = 3 then List.replicate boundary true
    else if k = 4 then List.replicate fullDiv true
    else if k = 6 then List.replicate diagonalDiv true
    else if k.val < 14 ∨ k = 19 then []
    else foreign k

theorem run_succ {c d : Config} (h : advance program c = d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, h]

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

/-- Reusable inlining certificate for either quotient phase.  The ambient
bank may contain arbitrary metadata outside the eight selected slots. -/
theorem embedded_quotient (ι : Fin 8 ↪ Stack)
    (labels : QuotientLabel → Label) (next : Label)
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
    (labels : CutLabel → Label) (next : Label)
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

theorem outer_run (foreign : Stack → List Bool)
    (ordinal uniform boundary fullDiv diagonalDiv : ℕ) :
    ∃ t ≤ 11 * ordinal + 3 * uniform + 7,
      run t (cfg (some start) initial
        (seed foreign ordinal uniform boundary fullDiv diagonalDiv)) =
      cfg (some .cutInit) (.quotient MatrixIndexQuotient.initial)
        (Function.update
          (seed foreign ordinal uniform boundary fullDiv diagonalDiv)
          2 (List.replicate (ordinal / uniform) true)) := by
  apply embedded_quotient outerSlots Label.outer .cutInit
    (by intro l; rfl)
    (seed foreign ordinal uniform boundary fullDiv diagonalDiv) ordinal uniform
  · simp [seed, outerSlots]
  · simp [seed, outerSlots]
  · intro k hk0 hk1
    fin_cases k <;> simp_all [seed, outerSlots]

def afterOuter (foreign : Stack → List Bool)
    (ordinal uniform boundary fullDiv diagonalDiv : ℕ) : Stack → List Bool :=
  Function.update (seed foreign ordinal uniform boundary fullDiv diagonalDiv)
    2 (List.replicate (ordinal / uniform) true)

def afterCut (foreign : Stack → List Bool)
    (ordinal uniform boundary fullDiv diagonalDiv : ℕ) : Stack → List Bool :=
  Function.update (afterOuter foreign ordinal uniform boundary fullDiv diagonalDiv)
    2 (List.replicate
      (if ordinal / uniform < boundary then ordinal / uniform
        else ordinal / uniform - boundary) true)

theorem cut_run (foreign : Stack → List Bool)
    (ordinal uniform boundary fullDiv diagonalDiv : ℕ) :
    ∃ t ≤ 3 * min (ordinal / uniform) boundary + 5,
      run t (cfg (some .cutInit) (.quotient MatrixIndexQuotient.initial)
        (afterOuter foreign ordinal uniform boundary fullDiv diagonalDiv)) =
      cfg (some .dispatch)
        (.cut (decide (boundary ≤ ordinal / uniform), false))
        (afterCut foreign ordinal uniform boundary fullDiv diagonalDiv) := by
  let S := afterOuter foreign ordinal uniform boundary fullDiv diagonalDiv
  have h0 : S (cutSlots 0) = List.replicate (ordinal / uniform) true := by
    simp [S, afterOuter, cutSlots]
  have h1 : S (cutSlots 1) = List.replicate boundary true := by
    simp [S, afterOuter, cutSlots, seed]
  have hrest : ∀ k : Fin 4, k ≠ 0 → k ≠ 1 → S (cutSlots k) = [] := by
    intro k hk0 hk1
    fin_cases k <;> simp_all [S, afterOuter, cutSlots, seed]
  obtain ⟨tc, htc, hc⟩ := embedded_cut cutSlots Label.cut .dispatch
    (by intro l; rfl) S (ordinal / uniform) boundary h0 h1 hrest
  refine ⟨tc + 1, by omega, ?_⟩
  have hstep : advance program
      (cfg (some .cutInit) (.quotient MatrixIndexQuotient.initial) S) =
      cfg (some (.cut .scan)) (.cut (false,true)) S := rfl
  rw [run_succ hstep tc]
  simpa [S, afterCut, afterOuter, cutSlots] using hc

def afterFull (foreign : Stack → List Bool)
    (ordinal uniform boundary fullDiv diagonalDiv : ℕ) : Stack → List Bool :=
  Function.update (afterCut foreign ordinal uniform boundary fullDiv diagonalDiv)
    19 (List.replicate ((ordinal / uniform) / fullDiv) true)

theorem full_branch_run (foreign : Stack → List Bool)
    (ordinal uniform boundary fullDiv diagonalDiv : ℕ)
    (hfull : ordinal / uniform < boundary) :
    ∃ t ≤ 11 * (ordinal / uniform) + 3 * fullDiv + 10,
      run t
        (cfg (some .dispatch)
          (.cut (decide (boundary ≤ ordinal / uniform), false))
          (afterCut foreign ordinal uniform boundary fullDiv diagonalDiv)) =
      cfg none (.terminal false)
        (afterFull foreign ordinal uniform boundary fullDiv diagonalDiv) := by
  let S := afterCut foreign ordinal uniform boundary fullDiv diagonalDiv
  have h0 : S (fullSlots 0) = List.replicate (ordinal / uniform) true := by
    simp [S, afterCut, afterOuter, fullSlots, hfull]
  have h1 : S (fullSlots 1) = List.replicate fullDiv true := by
    simp [S, afterCut, afterOuter, fullSlots, seed]
  have hrest : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 → S (fullSlots k) = [] := by
    intro k hk0 hk1
    fin_cases k <;> simp_all [S, afterCut, afterOuter, fullSlots, seed]
  obtain ⟨tq, htq, hq⟩ := embedded_quotient fullSlots Label.full .fullDone
    (by intro l; rfl) S (ordinal / uniform) fullDiv h0 h1 hrest
  have hfalse : decide (boundary ≤ ordinal / uniform) = false := by
    simp [Nat.not_le.mpr hfull]
  have hdispatch : advance program
      (cfg (some .dispatch)
        (.cut (decide (boundary ≤ ordinal / uniform), false)) S) =
      cfg (some .fullInit) (.cut (false,false)) S := by
    simp [advance, TM2.step, TM2.stepAux, program, cutFlag, hfalse, cfg]
  have hinit : advance program
      (cfg (some .fullInit) (.cut (false,false)) S) =
      cfg (some (.full MatrixIndexQuotient.start))
        (.quotient MatrixIndexQuotient.initial) S := rfl
  have htwo : run 2
      (cfg (some .dispatch)
        (.cut (decide (boundary ≤ ordinal / uniform), false)) S) =
      cfg (some (.full MatrixIndexQuotient.start))
        (.quotient MatrixIndexQuotient.initial) S := by
    change advance program (advance program _) = _
    rw [hdispatch, hinit]
  refine ⟨2 + tq + 1, by omega, ?_⟩
  calc
    run (2 + tq + 1)
      (cfg (some .dispatch)
        (.cut (decide (boundary ≤ ordinal / uniform), false)) S) =
      run (tq + 1)
        (cfg (some (.full MatrixIndexQuotient.start))
          (.quotient MatrixIndexQuotient.initial) S) := by
            rw [show 2 + tq + 1 = 2 + (tq + 1) by omega]
            exact run_add htwo _
    _ = run 1 (cfg (some .fullDone)
          (.quotient MatrixIndexQuotient.initial)
          (Function.update S 19
            (List.replicate ((ordinal / uniform) / fullDiv) true))) := by
            exact run_add hq 1
    _ = cfg none (.terminal false)
          (afterFull foreign ordinal uniform boundary fullDiv diagonalDiv) := by
            simp [run, advance, TM2.step, program, cfg, afterFull, S]

def afterDiagonal (foreign : Stack → List Bool)
    (ordinal uniform boundary fullDiv diagonalDiv : ℕ) : Stack → List Bool :=
  Function.update (afterCut foreign ordinal uniform boundary fullDiv diagonalDiv)
    5 (List.replicate
      (((ordinal / uniform - boundary) / diagonalDiv)) true)

theorem diagonal_branch_run (foreign : Stack → List Bool)
    (ordinal uniform boundary fullDiv diagonalDiv : ℕ)
    (hdiagonal : boundary ≤ ordinal / uniform) :
    ∃ t ≤ 11 * ((ordinal / uniform) - boundary) + 3 * diagonalDiv + 10,
      run t
        (cfg (some .dispatch)
          (.cut (decide (boundary ≤ ordinal / uniform), false))
          (afterCut foreign ordinal uniform boundary fullDiv diagonalDiv)) =
      cfg none (.terminal true)
        (afterDiagonal foreign ordinal uniform boundary fullDiv diagonalDiv) := by
  let S := afterCut foreign ordinal uniform boundary fullDiv diagonalDiv
  have h0 : S (diagonalSlots 0) =
      List.replicate (ordinal / uniform - boundary) true := by
    simp [S, afterCut, afterOuter, diagonalSlots,
      show ¬ordinal / uniform < boundary by omega]
  have h1 : S (diagonalSlots 1) = List.replicate diagonalDiv true := by
    simp [S, afterCut, afterOuter, diagonalSlots, seed]
  have hrest : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 →
      S (diagonalSlots k) = [] := by
    intro k hk0 hk1
    fin_cases k <;> simp_all [S, afterCut, afterOuter, diagonalSlots, seed]
  obtain ⟨tq, htq, hq⟩ := embedded_quotient diagonalSlots
    Label.diagonal .diagonalDone (by intro l; rfl)
    S (ordinal / uniform - boundary) diagonalDiv h0 h1 hrest
  have htrue : decide (boundary ≤ ordinal / uniform) = true := by
    simp [hdiagonal]
  have hdispatch : advance program
      (cfg (some .dispatch)
        (.cut (decide (boundary ≤ ordinal / uniform), false)) S) =
      cfg (some .diagonalInit) (.cut (true,false)) S := by
    simp [advance, TM2.step, TM2.stepAux, program, cutFlag, htrue, cfg]
  have hinit : advance program
      (cfg (some .diagonalInit) (.cut (true,false)) S) =
      cfg (some (.diagonal MatrixIndexQuotient.start))
        (.quotient MatrixIndexQuotient.initial) S := rfl
  have htwo : run 2
      (cfg (some .dispatch)
        (.cut (decide (boundary ≤ ordinal / uniform), false)) S) =
      cfg (some (.diagonal MatrixIndexQuotient.start))
        (.quotient MatrixIndexQuotient.initial) S := by
    change advance program (advance program _) = _
    rw [hdispatch, hinit]
  refine ⟨2 + tq + 1, by omega, ?_⟩
  calc
    run (2 + tq + 1)
      (cfg (some .dispatch)
        (.cut (decide (boundary ≤ ordinal / uniform), false)) S) =
      run (tq + 1)
        (cfg (some (.diagonal MatrixIndexQuotient.start))
          (.quotient MatrixIndexQuotient.initial) S) := by
            rw [show 2 + tq + 1 = 2 + (tq + 1) by omega]
            exact run_add htwo _
    _ = run 1 (cfg (some .diagonalDone)
          (.quotient MatrixIndexQuotient.initial)
          (Function.update S 5
            (List.replicate
              (((ordinal / uniform - boundary) / diagonalDiv)) true))) := by
            exact run_add hq 1
    _ = cfg none (.terminal true)
          (afterDiagonal foreign ordinal uniform boundary fullDiv diagonalDiv) := by
            simp [run, advance, TM2.step, program, cfg, afterDiagonal, S]

/-- One uninterrupted fixed program computes the raw column ordinal on the
full-support branch.  No quotient, cut, or bank transfer is a host step. -/
theorem full_controller_run (foreign : Stack → List Bool)
    (ordinal uniform boundary fullDiv diagonalDiv : ℕ)
    (hfull : ordinal / uniform < boundary) :
    ∃ t ≤ (11 * ordinal + 3 * uniform + 7) +
      (3 * min (ordinal / uniform) boundary + 5) +
      (11 * (ordinal / uniform) + 3 * fullDiv + 10),
      run t (cfg (some start) initial
        (seed foreign ordinal uniform boundary fullDiv diagonalDiv)) =
      cfg none (.terminal false)
        (afterFull foreign ordinal uniform boundary fullDiv diagonalDiv) := by
  obtain ⟨touter, hto, ho⟩ := outer_run foreign ordinal uniform boundary fullDiv diagonalDiv
  obtain ⟨tc, htc, hc⟩ := cut_run foreign ordinal uniform boundary fullDiv diagonalDiv
  obtain ⟨tf, htf, hf⟩ := full_branch_run foreign ordinal uniform boundary
    fullDiv diagonalDiv hfull
  refine ⟨touter + tc + tf, by omega, ?_⟩
  have ho' : run touter
      (cfg (some start) initial
        (seed foreign ordinal uniform boundary fullDiv diagonalDiv)) =
      cfg (some .cutInit) (.quotient MatrixIndexQuotient.initial)
        (afterOuter foreign ordinal uniform boundary fullDiv diagonalDiv) := by
    simpa only [afterOuter] using ho
  calc
    run (touter + tc + tf)
      (cfg (some start) initial
        (seed foreign ordinal uniform boundary fullDiv diagonalDiv)) =
      run (tc + tf)
        (cfg (some .cutInit) (.quotient MatrixIndexQuotient.initial)
          (afterOuter foreign ordinal uniform boundary fullDiv diagonalDiv)) := by
            rw [show touter + tc + tf = touter + (tc + tf) by omega]
            exact run_add ho' _
    _ = run tf
        (cfg (some .dispatch)
          (.cut (decide (boundary ≤ ordinal / uniform), false))
          (afterCut foreign ordinal uniform boundary fullDiv diagonalDiv)) :=
            run_add hc _
    _ = _ := hf

/-- The same fixed program's diagonal branch yields the second-row ordinal,
ready for the separate diagonal-address machine. -/
theorem diagonal_controller_run (foreign : Stack → List Bool)
    (ordinal uniform boundary fullDiv diagonalDiv : ℕ)
    (hdiagonal : boundary ≤ ordinal / uniform) :
    ∃ t ≤ (11 * ordinal + 3 * uniform + 7) +
      (3 * min (ordinal / uniform) boundary + 5) +
      (11 * (ordinal / uniform - boundary) + 3 * diagonalDiv + 10),
      run t (cfg (some start) initial
        (seed foreign ordinal uniform boundary fullDiv diagonalDiv)) =
      cfg none (.terminal true)
        (afterDiagonal foreign ordinal uniform boundary fullDiv diagonalDiv) := by
  obtain ⟨touter, hto, ho⟩ := outer_run foreign ordinal uniform boundary fullDiv diagonalDiv
  obtain ⟨tc, htc, hc⟩ := cut_run foreign ordinal uniform boundary fullDiv diagonalDiv
  obtain ⟨td, htd, hd⟩ := diagonal_branch_run foreign ordinal uniform boundary
    fullDiv diagonalDiv hdiagonal
  refine ⟨touter + tc + td, by omega, ?_⟩
  have ho' : run touter
      (cfg (some start) initial
        (seed foreign ordinal uniform boundary fullDiv diagonalDiv)) =
      cfg (some .cutInit) (.quotient MatrixIndexQuotient.initial)
        (afterOuter foreign ordinal uniform boundary fullDiv diagonalDiv) := by
    simpa only [afterOuter] using ho
  calc
    run (touter + tc + td)
      (cfg (some start) initial
        (seed foreign ordinal uniform boundary fullDiv diagonalDiv)) =
      run (tc + td)
        (cfg (some .cutInit) (.quotient MatrixIndexQuotient.initial)
          (afterOuter foreign ordinal uniform boundary fullDiv diagonalDiv)) := by
            rw [show touter + tc + td = touter + (tc + td) by omega]
            exact run_add ho' _
    _ = run td
        (cfg (some .dispatch)
          (.cut (decide (boundary ≤ ordinal / uniform), false))
          (afterCut foreign ordinal uniform boundary fullDiv diagonalDiv)) :=
            run_add hc _
    _ = _ := hd

end EthInapproximability.CurrentPaper.MatrixWeightedColumnController
