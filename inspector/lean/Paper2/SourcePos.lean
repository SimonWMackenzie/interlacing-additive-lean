import Paper2.TagDispatch
import Paper2.SourceMatrix

/-! Unit 3, segment (1): the unary source position
`SourceMatrix.sourcePosition` from the physical test outputs.

`sourcePosition activity i Z = if (all outer tokens equal) then
(match activity i tok₀ with | some p => p.castSucc | none => last s) else last s`.
With the equality bit `eq`, the scan's activity bit `act` and rank marks
`rk` (`ScanJoin` / `ScanValue` outputs; `act = false`, `rk = 0` in the
unselected case), the position is `if eq && act then rk else s`.

ONE fixed program on seven cells (`eq`, `act`, `rk`, unary `s` preserved,
`pos`, copy scratch, flag): pop `eq`, pop `act`; on `true, true` move the
`rk` marks to `pos` and push flag `false`; otherwise clear `rk` and push flag
`true`; then the production `TagDispatch.ifProgram` on the flag runs either
`TagDispatch.haltProg` or the production source-preserving
`MatrixStage4ScalarPreparationOps.copyProgram` of `s` into `pos`. -/

namespace Paper2.SourcePos

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open BitMachineRawSequence (leftLabel)

abbrev P7 := Fin 7

def u (n : ℕ) : List Bool := List.replicate n true

inductive PL where
  | l0 | l1 | la | lr | lm
  deriving DecidableEq

def progA : PL → TM2.Stmt (fun _ : P7 => Bool) PL (Option Bool)
  | .l0 => pop 0 (fun _ b => b)
      (branch (fun v => v == some true) (goto (fun _ => .l1)) (goto (fun _ => .la)))
  | .l1 => pop 1 (fun _ b => b)
      (branch (fun v => v == some true) (goto (fun _ => .lm)) (goto (fun _ => .lr)))
  | .la => pop 1 (fun _ b => b) (goto (fun _ => .lr))
  | .lr => pop 2 (fun _ b => b)
      (branch (fun v => v.isSome) (goto (fun _ => .lr)) (push 6 (fun _ => true) halt))
  | .lm => pop 2 (fun _ b => b)
      (branch (fun v => v.isSome) (push 4 (fun _ => true) (goto (fun _ => .lm)))
        (push 6 (fun _ => false) halt))

def slots : Fin 3 ↪ P7 := ⟨![3, 4, 5], by decide⟩

def copyP := MatrixStage4ScalarPreparationOps.copyProgram slots

def progB := TagDispatch.ifProgram (6 : P7) (TagDispatch.haltProg (J := P7)) copyP ()
  BitMachineCopy.Label.scan () (none : Option Bool)

def program := BitMachineRawSequence.program progA progB (.inl ()) (none : Option Bool)
  ((none : Option Bool), ((), (none : Option Bool)))

/-- Entry bank. -/
def PB (e a : List Bool) (rk s : ℕ) : P7 → List Bool := ![e, a, u rk, u s, [], [], []]

/-- Exit bank. -/
def PF (s pos : ℕ) : P7 → List Bool := ![[], [], [], u s, u pos, [], []]

theorem iter_trans {α : Type*} {f : α → α} {a b c : α} {m n : ℕ}
    (h1 : f^[m] a = b) (h2 : f^[n] b = c) : f^[n + m] a = c := by
  rw [Function.iterate_add_apply, h1, h2]

theorem lm_run : ∀ (j : ℕ) (S : P7 → List Bool) (v : Option Bool), S 2 = u j →
    (advance progA)^[j + 1] (⟨some .lm, v, S⟩ : TM2.Cfg (fun _ : P7 => Bool) PL (Option Bool)) =
      ⟨none, none, Function.update (Function.update (Function.update S 2 []) 4 (u j ++ S 4)) 6
        (false :: S 6)⟩
  | 0, S, v, h => by
      rw [Function.iterate_one]
      have h' : S 2 = [] := h
      simp [advance, TM2.step, TM2.stepAux, progA, h', u]
      funext c
      by_cases h4 : c = 4
      · subst h4; simp
      · simp [Function.update_apply, h4]
  | j + 1, S, v, h => by
      have h' : S 2 = true :: u j := h
      have hs : advance progA (⟨some .lm, v, S⟩ : TM2.Cfg (fun _ : P7 => Bool) PL (Option Bool)) =
          ⟨some .lm, some true, Function.update (Function.update S 2 (u j)) 4 (true :: S 4)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, progA, h']
      rw [Function.iterate_succ_apply, hs, lm_run j _ _ (by simp)]
      congr 1
      funext c
      simp only [Function.update_apply]
      by_cases h6 : c = 6 <;> by_cases h4 : c = 4 <;> by_cases h2 : c = 2 <;>
        simp_all [u, List.replicate_succ']

theorem lr_run : ∀ (j : ℕ) (S : P7 → List Bool) (v : Option Bool), S 2 = u j →
    (advance progA)^[j + 1] (⟨some .lr, v, S⟩ : TM2.Cfg (fun _ : P7 => Bool) PL (Option Bool)) =
      ⟨none, none, Function.update (Function.update S 2 []) 6 (true :: S 6)⟩
  | 0, S, v, h => by
      rw [Function.iterate_one]
      have h' : S 2 = [] := h
      simp [advance, TM2.step, TM2.stepAux, progA, h']
  | j + 1, S, v, h => by
      have h' : S 2 = true :: u j := h
      have hs : advance progA (⟨some .lr, v, S⟩ : TM2.Cfg (fun _ : P7 => Bool) PL (Option Bool)) =
          ⟨some .lr, some true, Function.update S 2 (u j)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, progA, h']
      rw [Function.iterate_succ_apply, hs, lr_run j _ _ (by simp)]
      simp

/-- Part A: the decision; flag `false` iff `eq && act` (then `pos = rk`). -/
theorem partA_run (eq act : Bool) (rk s : ℕ) :
    ∃ t ≤ rk + 3,
      (advance progA)^[t] (⟨some .l0, none, PB [eq] [act] rk s⟩ :
        TM2.Cfg (fun _ : P7 => Bool) PL (Option Bool)) =
        ⟨none, none, ![[], [], [], u s, if eq && act then u rk else [], [],
          [!(eq && act)]]⟩ := by
  cases eq <;> cases act
  · -- false false
    have s1 : (advance progA)^[1] (⟨some .l0, none, PB [false] [false] rk s⟩ :
        TM2.Cfg (fun _ : P7 => Bool) PL (Option Bool)) =
        ⟨some .la, some false, Function.update (PB [false] [false] rk s) 0 []⟩ := rfl
    have s2 : (advance progA)^[1] (⟨some .la, some false,
        Function.update (PB [false] [false] rk s) 0 []⟩ :
        TM2.Cfg (fun _ : P7 => Bool) PL (Option Bool)) =
        ⟨some .lr, some false, Function.update (Function.update (PB [false] [false] rk s) 0 []) 1 []⟩ :=
      rfl
    refine ⟨(rk + 1) + (1 + 1), by omega, ?_⟩
    refine iter_trans (iter_trans s1 s2) ((lr_run rk _ _ (by rfl)).trans ?_)
    congr 1; funext c; fin_cases c <;> rfl
  · -- false true
    have s1 : (advance progA)^[1] (⟨some .l0, none, PB [false] [true] rk s⟩ :
        TM2.Cfg (fun _ : P7 => Bool) PL (Option Bool)) =
        ⟨some .la, some false, Function.update (PB [false] [true] rk s) 0 []⟩ := rfl
    have s2 : (advance progA)^[1] (⟨some .la, some false,
        Function.update (PB [false] [true] rk s) 0 []⟩ :
        TM2.Cfg (fun _ : P7 => Bool) PL (Option Bool)) =
        ⟨some .lr, some true, Function.update (Function.update (PB [false] [true] rk s) 0 []) 1 []⟩ :=
      rfl
    refine ⟨(rk + 1) + (1 + 1), by omega, ?_⟩
    refine iter_trans (iter_trans s1 s2) ((lr_run rk _ _ (by rfl)).trans ?_)
    congr 1; funext c; fin_cases c <;> rfl
  · -- true false
    have s1 : (advance progA)^[1] (⟨some .l0, none, PB [true] [false] rk s⟩ :
        TM2.Cfg (fun _ : P7 => Bool) PL (Option Bool)) =
        ⟨some .l1, some true, Function.update (PB [true] [false] rk s) 0 []⟩ := rfl
    have s2 : (advance progA)^[1] (⟨some .l1, some true,
        Function.update (PB [true] [false] rk s) 0 []⟩ :
        TM2.Cfg (fun _ : P7 => Bool) PL (Option Bool)) =
        ⟨some .lr, some false, Function.update (Function.update (PB [true] [false] rk s) 0 []) 1 []⟩ :=
      rfl
    refine ⟨(rk + 1) + (1 + 1), by omega, ?_⟩
    refine iter_trans (iter_trans s1 s2) ((lr_run rk _ _ (by rfl)).trans ?_)
    congr 1; funext c; fin_cases c <;> rfl
  · -- true true
    have s1 : (advance progA)^[1] (⟨some .l0, none, PB [true] [true] rk s⟩ :
        TM2.Cfg (fun _ : P7 => Bool) PL (Option Bool)) =
        ⟨some .l1, some true, Function.update (PB [true] [true] rk s) 0 []⟩ := rfl
    have s2 : (advance progA)^[1] (⟨some .l1, some true,
        Function.update (PB [true] [true] rk s) 0 []⟩ :
        TM2.Cfg (fun _ : P7 => Bool) PL (Option Bool)) =
        ⟨some .lm, some true, Function.update (Function.update (PB [true] [true] rk s) 0 []) 1 []⟩ :=
      rfl
    refine ⟨(rk + 1) + (1 + 1), by omega, ?_⟩
    refine iter_trans (iter_trans s1 s2) ((lm_run rk _ _ (by rfl)).trans ?_)
    congr 1; funext c; fin_cases c <;> simp [u, PB]

/-- The whole program: exact exit bank, explicit clock. -/
theorem pos_run (eq act : Bool) (rk s : ℕ) :
    ∃ t ≤ (rk + 3) + ((2 * s + 2) + 1) + 1, ∃ c,
      (advance program)^[t] (⟨some (leftLabel .l0),
        ((none : Option Bool), ((none : Option Bool), ((), (none : Option Bool)))),
        PB [eq] [act] rk s⟩ : TM2.Cfg (fun _ : P7 => Bool) _ _) =
        ⟨none, c, PF s (if eq && act then rk else s)⟩ := by
  obtain ⟨t1, ht1, h1⟩ := partA_run eq act rk s
  let S1 : P7 → List Bool := ![[], [], [], u s, if eq && act then u rk else [], [], [!(eq && act)]]
  by_cases hb : (eq && act) = true
  · have hS : S1 6 = false :: [] := by simp [S1, hb]
    have hP : (advance (TagDispatch.haltProg (J := P7)))^[1]
        (⟨some (), (), Function.update S1 6 []⟩ : TM2.Cfg (fun _ : P7 => Bool) Unit Unit) =
        ⟨none, (), Function.update S1 6 []⟩ := rfl
    obtain ⟨t2, ht2, h2⟩ := TagDispatch.if_false (6 : P7) (TagDispatch.haltProg (J := P7)) copyP ()
      BitMachineCopy.Label.scan () (none : Option Bool) S1 [] hS 1 () _ hP
    obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs progA progB .l0 (.inl ()) none none
      ((none : Option Bool), ((), (none : Option Bool))) _ (PB [eq] [act] rk s) S1 _ t1 t2 h1 h2
    refine ⟨t, by omega, ((none : Option Bool), (some false, ((), (none : Option Bool)))),
      hr.trans ?_⟩
    congr 1
    funext c; fin_cases c <;> simp [S1, PF, hb]
  · have hS : S1 6 = true :: [] := by simp [S1, hb]
    have hcopy := MatrixStage4ScalarPreparationOps.copy_run slots (Function.update S1 6 [])
      (by rfl)
    have hlen : (Function.update S1 6 [] (slots 0)).length = s := by
      show (u s).length = s; simp [u]
    rw [hlen] at hcopy
    obtain ⟨t2, ht2, h2⟩ := TagDispatch.if_true (6 : P7) (TagDispatch.haltProg (J := P7)) copyP ()
      BitMachineCopy.Label.scan () (none : Option Bool) S1 [] hS (2 * s + 2) none _ hcopy
    obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs progA progB .l0 (.inl ()) none none
      ((none : Option Bool), ((), (none : Option Bool))) _ (PB [eq] [act] rk s) S1 _ t1 t2 h1 h2
    refine ⟨t, by omega, ((none : Option Bool), (some true, ((), (none : Option Bool)))),
      hr.trans ?_⟩
    congr 1
    have hb' : (eq && act) = false := by simpa using hb
    funext c; fin_cases c <;> simp [S1, PF, hb', slots, u]

/-- Value identity with the production `SourceMatrix.sourcePosition`. -/
theorem sourcePosition_eq {X Y I : Type*} {s q₁ q₂ : ℕ} [NeZero s]
    (activity : I → Fin q₂ → Option (Fin s)) (i : I)
    (Z : SourceMatrix.RawColumn q₁ q₂ s Y) (eq act : Bool) (rk : ℕ)
    (heq : eq = true ↔ ∀ p, (Z.2 p).1 = (Z.2 0).1)
    (hact : Option.map Fin.val (activity i (Z.2 0).1) = if act then some rk else none) :
    (SourceMatrix.sourcePosition activity i Z).val = if eq && act then rk else s := by
  unfold SourceMatrix.sourcePosition
  by_cases he : ∀ p, (Z.2 p).1 = (Z.2 0).1
  · have heq' : eq = true := heq.mpr he
    rw [if_pos he, heq']
    cases ha : activity i (Z.2 0).1 with
    | none =>
        rw [ha] at hact
        cases act
        · simp
        · simp at hact
    | some p =>
        rw [ha] at hact
        cases act
        · simp at hact
        · simp at hact
          simp [hact]
  · have heq' : eq = false := by
      cases eq
      · rfl
      · exact absurd (heq.mp rfl) he
    rw [if_neg he, heq']
    simp

#print axioms lm_run
#print axioms lr_run
#print axioms partA_run
#print axioms pos_run
#print axioms sourcePosition_eq

end

end Paper2.SourcePos
