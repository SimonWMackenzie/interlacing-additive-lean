import EthInapproximability.CurrentPaper.MatrixStage4AlignmentFromOrdinal
import EthInapproximability.CurrentPaper.MatrixStage4ActiveRankMachine

/-!
# Physical graph-tail index choice

The two Boolean control flags are the results of the charged alignment and
vector-entry computations. This fixed program selects either the computed
unary active rank or the unary inactive index `s`, consumes the selected
stack, and writes the selected index to a third stack. It does not read a
source bit or claim a complete raw-matrix callback.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4GraphChoose

open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Control := Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 3 => Bool) Unit Control

def initial (aligned active : Bool) : Control := (aligned && active,none)

def program : Unit → TM2.Stmt (fun _ : Fin 3 => Bool) Unit Control
  | () => branch Prod.fst
      (pop 0 (fun v b => (v.1,b))
        (branch (fun v => v.2.isSome)
          (push 2 (fun _ => true)
            (load (fun v => (v.1,none)) (goto (fun _ => ()))))
          (load (fun v => (v.1,none)) halt)))
      (pop 1 (fun v b => (v.1,b))
        (branch (fun v => v.2.isSome)
          (push 2 (fun _ => true)
            (load (fun v => (v.1,none)) (goto (fun _ => ()))))
          (load (fun v => (v.1,none)) halt)))

def cfg (l : Option Unit) (v : Control)
    (activeIndex inactiveIndex output : List Bool) : Config :=
  ⟨l,v,![activeIndex,inactiveIndex,output]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem step_active_true (v : Control) (rank fallback out : List Bool)
    (h : v.1 = true) :
    advance program (cfg (some ()) v (true::rank) fallback out) =
      cfg (some ()) (v.1,none) rank fallback (true::out) := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg,h]
  funext k
  fin_cases k <;> rfl

theorem step_active_end (v : Control) (fallback out : List Bool)
    (h : v.1 = true) :
    advance program (cfg (some ()) v [] fallback out) =
      cfg none (v.1,none) [] fallback out := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg,h]

theorem step_inactive_true (v : Control) (rank fallback out : List Bool)
    (h : v.1 = false) :
    advance program (cfg (some ()) v rank (true::fallback) out) =
      cfg (some ()) (v.1,none) rank fallback (true::out) := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg,h]
  funext k
  fin_cases k <;> rfl

theorem step_inactive_end (v : Control) (rank out : List Bool)
    (h : v.1 = false) :
    advance program (cfg (some ()) v rank [] out) =
      cfg none (v.1,none) rank [] out := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg,h]

theorem active_run (aligned active : Bool) (rank fallback : ℕ)
    (out : List Bool) (h : (aligned && active) = true) :
    run (rank+1) (cfg (some ()) (initial aligned active)
      (List.replicate rank true) (List.replicate fallback true) out) =
      cfg none (initial aligned active) []
        (List.replicate fallback true) (List.replicate rank true ++ out) := by
  induction rank generalizing out with
  | zero =>
    simpa [run,initial] using
      step_active_end (initial aligned active)
        (List.replicate fallback true) out h
  | succ n ih =>
    simp only [List.replicate_succ]
    change (advance program)^[n+2] _ = _
    rw [show n+2 = (n+1)+1 by omega]
    rw [Function.iterate_succ_apply]
    rw [step_active_true (initial aligned active)
      (List.replicate n true) (List.replicate fallback true) out h]
    change run (n+1) (cfg (some ()) (initial aligned active)
      (List.replicate n true) (List.replicate fallback true) (true::out)) = _
    have hlist : List.replicate n true ++ true::out =
        true :: List.replicate n true ++ out := by
      calc
        List.replicate n true ++ true::out =
            (List.replicate n true ++ [true]) ++ out := by
              simp only [List.append_assoc,List.singleton_append]
        _ = List.replicate (n+1) true ++ out := by
              rw [List.replicate_succ']
        _ = true :: List.replicate n true ++ out := by
              rw [List.replicate_succ]
    simpa only [hlist] using ih (true::out)

theorem inactive_run (aligned active : Bool) (rank fallback : ℕ)
    (out : List Bool) (h : (aligned && active) = false) :
    run (fallback+1) (cfg (some ()) (initial aligned active)
      (List.replicate rank true) (List.replicate fallback true) out) =
      cfg none (initial aligned active)
        (List.replicate rank true) [] (List.replicate fallback true ++ out) := by
  induction fallback generalizing out with
  | zero =>
    simpa [run,initial] using
      step_inactive_end (initial aligned active)
        (List.replicate rank true) out h
  | succ n ih =>
    simp only [List.replicate_succ]
    change (advance program)^[n+2] _ = _
    rw [show n+2 = (n+1)+1 by omega]
    rw [Function.iterate_succ_apply]
    rw [step_inactive_true (initial aligned active)
      (List.replicate rank true) (List.replicate n true) out h]
    change run (n+1) (cfg (some ()) (initial aligned active)
      (List.replicate rank true) (List.replicate n true) (true::out)) = _
    have hlist : List.replicate n true ++ true::out =
        true :: List.replicate n true ++ out := by
      calc
        List.replicate n true ++ true::out =
            (List.replicate n true ++ [true]) ++ out := by
              simp only [List.append_assoc,List.singleton_append]
        _ = List.replicate (n+1) true ++ out := by
              rw [List.replicate_succ']
        _ = true :: List.replicate n true ++ out := by
              rw [List.replicate_succ]
    simpa only [hlist] using ih (true::out)

theorem choose_run (aligned active : Bool) (rank s : ℕ)
    (out : List Bool) :
    ∃ t ≤ rank+s+1,
      (run t (cfg (some ()) (initial aligned active)
        (List.replicate rank true) (List.replicate s true) out)).l = none ∧
      (run t (cfg (some ()) (initial aligned active)
        (List.replicate rank true) (List.replicate s true) out)).stk 2 =
        List.replicate (if aligned && active then rank else s) true ++ out := by
  by_cases h : (aligned && active) = true
  · refine ⟨rank+1,by omega,?_,?_⟩
    · rw [active_run aligned active rank s out h]
      rfl
    · rw [active_run aligned active rank s out h]
      change List.replicate rank true ++ out =
        List.replicate (if aligned && active then rank else s) true ++ out
      simp [h]
  · have hf : (aligned && active) = false := Bool.eq_false_iff.mpr h
    refine ⟨s+1,by omega,?_,?_⟩
    · rw [inactive_run aligned active rank s out hf]
      rfl
    · rw [inactive_run aligned active rank s out hf]
      change List.replicate s true ++ out =
        List.replicate (if aligned && active then rank else s) true ++ out
      simp [hf]

open Construction

def chosenTail {a s q n cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin n) (c : RawColumns a s q (Fin cy)) : Fin (s+1) :=
  let α := (c.2 (firstBin s hs)).1
  if aligned hs c then
    if hi : vectors i α = true then
      Fin.castAdd 1 (activeSlot vectors cap α ⟨i,hi⟩)
    else Fin.last s
  else Fin.last s

theorem chosenTail_val_of_flag {a s q n cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin n) (c : RawColumns a s q (Fin cy))
    (flag : Bool) (hflag : flag = true ↔ aligned hs c) :
    (chosenTail hs vectors cap i c).val =
      if flag && vectors i (c.2 (firstBin s hs)).1 then
        activeRank vectors (c.2 (firstBin s hs)).1 i else s := by
  classical
  by_cases ha : aligned hs c
  · have hf : flag = true := hflag.mpr ha
    by_cases hi : vectors i (c.2 (firstBin s hs)).1 = true
    · simp [chosenTail,ha,hi,hf,activeSlot]
    · have hfalse : vectors i (c.2 (firstBin s hs)).1 = false :=
        Bool.eq_false_iff.mpr hi
      simp [chosenTail,ha,hfalse,hf]
  · have hf : flag = false := Bool.eq_false_iff.mpr
      (fun ht => ha (hflag.mp ht))
    simp [chosenTail,ha,hf]

theorem graphEntry_chosenTail {a s q n rx cy : ℕ} (hs : 0 < s)
    (R : Fin rx → Fin cy → Bool)
    (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin n) (x : Fin rx)
    (c : RawColumns a s q (Fin cy)) :
    graphEntry R hs vectors cap i x c =
      R x (c.1 (chosenTail hs vectors cap i c)) := by
  classical
  by_cases ha : aligned hs c
  · by_cases hi : vectors i (c.2 (firstBin s hs)).1 = true
    · simp [graphEntry,chosenTail,ha,hi]
    · simp [graphEntry,chosenTail,ha,hi]
  · simp [graphEntry,chosenTail,ha]

theorem graph_tail_choose_run {a s q n cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin n) (c : RawColumns a s q (Fin cy))
    (flag : Bool) (hflag : flag = true ↔ aligned hs c)
    (out : List Bool) :
    let α := (c.2 (firstBin s hs)).1
    let rank := activeRank vectors α i
    ∃ t ≤ rank+s+1,
      (run t (cfg (some ()) (initial flag (vectors i α))
        (List.replicate rank true) (List.replicate s true) out)).l = none ∧
      (run t (cfg (some ()) (initial flag (vectors i α))
        (List.replicate rank true) (List.replicate s true) out)).stk 2 =
        List.replicate (chosenTail hs vectors cap i c).val true ++ out := by
  dsimp
  obtain ⟨t,ht,hl,ho⟩ := choose_run flag
    (vectors i (c.2 (firstBin s hs)).1)
    (activeRank vectors (c.2 (firstBin s hs)).1 i) s out
  refine ⟨t,ht,hl,?_⟩
  rw [ho,chosenTail_val_of_flag hs vectors cap i c flag hflag]

end EthInapproximability.CurrentPaper.MatrixStage4GraphChoose
