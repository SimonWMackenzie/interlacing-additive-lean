import EthInapproximability.CurrentPaper.SamplerMachineSearch
import Paper2.FiniteFallbackSearch
import Mathlib.Tactic

/-! U16 (private, lane owner:a-uniform-clock-2): the exhaustive colouring search
of frozen v12 D:104-110 as a physical machine, every step charged.

* Enumeration with carry: the ADMITTED first-success binary-counter controller
  `SamplerMachineSearch.program` (reused by exact name, `search_allWords` /
  `search_none`) over counter words of width `2v`: every candidate word is visited
  from the all-zero word, with physical increment-with-carry and overflow detection.
  Each vertex owns two counter bits; the two-bit digit is decoded SURJECTIVELY onto
  `Fin 3` (`00 ↦ 0`, `10 ↦ 1`, `01 ↦ 2`, `11 ↦ 2`), so the `4^v` counter words cover
  all `3^v` colourings. This is NOT a literal ternary counter (disclosed).
* Access: a fixed finite predicate program `P` that, for every edge of the internal
  edge tape (endpoints in terminated unary), physically walks the counter to each
  endpoint's two bits (moving them to a scratch stack and back), compares the two
  decoded colours, stops at the first monochromatic edge, and restores every stack.
* Identity: the physical accept bit equals `decide (ThreeColourable edge)`, i.e.
  `(FiniteFallbackSearchScratch.search edge).1` (admitted `search_found_iff`). -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Paper2.FallbackColourSearch

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

/-! ### Semantics -/

def dec (b0 b1 : Bool) : Fin 3 := if b1 then 2 else if b0 then 1 else 0

def decode2 : List Bool → Fin 3
  | b0 :: b1 :: _ => dec b0 b1
  | _ => 0

def encC : Fin 3 → List Bool
  | 0 => [false, false]
  | 1 => [true, false]
  | _ => [false, true]

def colWord : List (Fin 3) → List Bool
  | [] => []
  | x :: xs => encC x ++ colWord xs

/-- One edge on the internal edge tape: both endpoints in terminated unary. -/
def edgeWord1 (a b : Nat) : List Bool :=
  List.replicate a true ++ false :: (List.replicate b true ++ [false])

def edgesWord : List (Nat × Nat) → List Bool
  | [] => []
  | (a, b) :: es => edgeWord1 a b ++ edgesWord es

def edgesOK (q : List Bool) : List (Nat × Nat) → Bool
  | [] => true
  | (a, b) :: es => decide (decode2 (q.drop (2 * a)) ≠ decode2 (q.drop (2 * b))) && edgesOK q es

def edgeList {v e : Nat} (edge : Fin e → Bool → Fin v) : List (Nat × Nat) :=
  (List.finRange e).map (fun z => ((edge z false).val, (edge z true).val))

/-! ### The predicate program -/

structure Ctl where
  ca : Fin 3
  same : Bool
  acc : Bool
  t1 : Option Bool
  t2 : Option Bool
  t3 : Option Bool

def norm (ca : Fin 3) (same acc : Bool) : Ctl := ⟨ca, same, acc, none, none, none⟩

inductive Lab where
  | readA | readB | fetchA | restA | fetchB | restB | undoE

/-- Stacks: 0 counter (the controller's source), 1 edge tape, 2 processed edges,
3 and 4 unary endpoint registers, 5 counter scratch. -/
abbrev K := Fin 6

def P : Lab → TM2.Stmt (fun _ : K => Bool) Lab Ctl
  | .readA => pop 1 (fun v b => { v with t1 := b })
      (branch (fun v => v.t1.isSome)
        (branch (fun v => v.t1.getD false)
          (push 3 (fun _ => true) (push 2 (fun _ => true)
            (load (fun v => norm v.ca v.same v.acc) (goto (fun _ => .readA)))))
          (push 2 (fun _ => false)
            (load (fun v => norm v.ca v.same v.acc) (goto (fun _ => .readB)))))
        (load (fun v => norm v.ca v.same true) (goto (fun _ => .undoE))))
  | .readB => pop 1 (fun v b => { v with t1 := b })
      (branch (fun v => v.t1.isSome && v.t1.getD false)
        (push 4 (fun _ => true) (push 2 (fun _ => true)
          (load (fun v => norm v.ca v.same v.acc) (goto (fun _ => .readB)))))
        (branch (fun v => v.t1.isSome)
          (push 2 (fun _ => false)
            (load (fun v => norm v.ca v.same v.acc) (goto (fun _ => .fetchA))))
          (load (fun v => norm v.ca v.same false) (goto (fun _ => .undoE)))))
  | .fetchA => pop 3 (fun v b => { v with t1 := b })
      (pop 0 (fun v b => { v with t2 := b }) (pop 0 (fun v b => { v with t3 := b })
        (branch (fun v => v.t1.isSome)
          (push 5 (fun v => v.t2.getD false) (push 5 (fun v => v.t3.getD false)
            (load (fun v => norm v.ca v.same v.acc) (goto (fun _ => .fetchA)))))
          (push 0 (fun v => v.t3.getD false) (push 0 (fun v => v.t2.getD false)
            (load (fun v => norm (dec (v.t2.getD false) (v.t3.getD false)) v.same v.acc)
              (goto (fun _ => .restA))))))))
  | .restA => pop 5 (fun v b => { v with t1 := b })
      (branch (fun v => v.t1.isSome)
        (push 0 (fun v => v.t1.getD false)
          (load (fun v => norm v.ca v.same v.acc) (goto (fun _ => .restA))))
        (load (fun v => norm v.ca v.same v.acc) (goto (fun _ => .fetchB))))
  | .fetchB => pop 4 (fun v b => { v with t1 := b })
      (pop 0 (fun v b => { v with t2 := b }) (pop 0 (fun v b => { v with t3 := b })
        (branch (fun v => v.t1.isSome)
          (push 5 (fun v => v.t2.getD false) (push 5 (fun v => v.t3.getD false)
            (load (fun v => norm v.ca v.same v.acc) (goto (fun _ => .fetchB)))))
          (push 0 (fun v => v.t3.getD false) (push 0 (fun v => v.t2.getD false)
            (load (fun v => norm v.ca
                (decide (dec (v.t2.getD false) (v.t3.getD false) = v.ca)) v.acc)
              (goto (fun _ => .restB))))))))
  | .restB => pop 5 (fun v b => { v with t1 := b })
      (branch (fun v => v.t1.isSome)
        (push 0 (fun v => v.t1.getD false)
          (load (fun v => norm v.ca v.same v.acc) (goto (fun _ => .restB))))
        (branch (fun v => v.same)
          (load (fun v => norm v.ca v.same false) (goto (fun _ => .undoE)))
          (load (fun v => norm v.ca v.same v.acc) (goto (fun _ => .readA)))))
  | .undoE => pop 2 (fun v b => { v with t1 := b })
      (branch (fun v => v.t1.isSome)
        (push 1 (fun v => v.t1.getD false)
          (load (fun v => norm v.ca v.same v.acc) (goto (fun _ => .undoE))))
        halt)

def bk (q E W A Bq D : List Bool) : K → List Bool := ![q, E, W, A, Bq, D]

def c (l : Option Lab) (v : Ctl) (q E W A Bq D : List Bool) :
    TM2.Cfg (fun _ : K => Bool) Lab Ctl := ⟨l, v, bk q E W A Bq D⟩

abbrev step := advance P

theorem cfg_ext {x : TM2.Cfg (fun _ : K => Bool) Lab Ctl} {l : Option Lab} {v : Ctl}
    {S : K → List Bool} (hl : x.l = l) (hv : x.var = v) (hs : ∀ j, x.stk j = S j) :
    x = ⟨l, v, S⟩ := by
  cases x with
  | mk l' v' S' =>
    simp only at hl hv
    subst hl hv
    have : S' = S := funext hs
    subst this
    rfl

/-! ### Step lemmas -/

theorem readA_true (ca s acc) (q E W A Bq D : List Bool) :
    step (c (some .readA) (norm ca s acc) q (true :: E) W A Bq D) =
      c (some .readA) (norm ca s acc) q E (true :: W) (true :: A) Bq D := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

theorem readA_false (ca s acc) (q E W A Bq D : List Bool) :
    step (c (some .readA) (norm ca s acc) q (false :: E) W A Bq D) =
      c (some .readB) (norm ca s acc) q E (false :: W) A Bq D := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

theorem readA_nil (ca s acc) (q W A Bq D : List Bool) :
    step (c (some .readA) (norm ca s acc) q [] W A Bq D) =
      c (some .undoE) (norm ca s true) q [] W A Bq D := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

theorem readB_true (ca s acc) (q E W A Bq D : List Bool) :
    step (c (some .readB) (norm ca s acc) q (true :: E) W A Bq D) =
      c (some .readB) (norm ca s acc) q E (true :: W) A (true :: Bq) D := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

theorem readB_false (ca s acc) (q E W A Bq D : List Bool) :
    step (c (some .readB) (norm ca s acc) q (false :: E) W A Bq D) =
      c (some .fetchA) (norm ca s acc) q E (false :: W) A Bq D := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

theorem fetchA_cons (ca s acc) (b0 b1 : Bool) (q E W A Bq D : List Bool) :
    step (c (some .fetchA) (norm ca s acc) (b0 :: b1 :: q) E W (true :: A) Bq D) =
      c (some .fetchA) (norm ca s acc) q E W A Bq (b1 :: b0 :: D) := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

theorem fetchA_nil (ca s acc) (b0 b1 : Bool) (q E W Bq D : List Bool) :
    step (c (some .fetchA) (norm ca s acc) (b0 :: b1 :: q) E W [] Bq D) =
      c (some .restA) (norm (dec b0 b1) s acc) (b0 :: b1 :: q) E W [] Bq D := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

theorem restA_cons (ca s acc) (b : Bool) (q E W A Bq D : List Bool) :
    step (c (some .restA) (norm ca s acc) q E W A Bq (b :: D)) =
      c (some .restA) (norm ca s acc) (b :: q) E W A Bq D := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

theorem restA_nil (ca s acc) (q E W A Bq : List Bool) :
    step (c (some .restA) (norm ca s acc) q E W A Bq []) =
      c (some .fetchB) (norm ca s acc) q E W A Bq [] := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

theorem fetchB_cons (ca s acc) (b0 b1 : Bool) (q E W A Bq D : List Bool) :
    step (c (some .fetchB) (norm ca s acc) (b0 :: b1 :: q) E W A (true :: Bq) D) =
      c (some .fetchB) (norm ca s acc) q E W A Bq (b1 :: b0 :: D) := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

theorem fetchB_nil (ca s acc) (b0 b1 : Bool) (q E W A D : List Bool) :
    step (c (some .fetchB) (norm ca s acc) (b0 :: b1 :: q) E W A [] D) =
      c (some .restB) (norm ca (decide (dec b0 b1 = ca)) acc) (b0 :: b1 :: q) E W A [] D := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

theorem restB_cons (ca s acc) (b : Bool) (q E W A Bq D : List Bool) :
    step (c (some .restB) (norm ca s acc) q E W A Bq (b :: D)) =
      c (some .restB) (norm ca s acc) (b :: q) E W A Bq D := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

theorem restB_same (ca acc) (q E W A Bq : List Bool) :
    step (c (some .restB) (norm ca true acc) q E W A Bq []) =
      c (some .undoE) (norm ca true false) q E W A Bq [] := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

theorem restB_diff (ca acc) (q E W A Bq : List Bool) :
    step (c (some .restB) (norm ca false acc) q E W A Bq []) =
      c (some .readA) (norm ca false acc) q E W A Bq [] := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

theorem undo_cons (ca s acc) (b : Bool) (q E W A Bq D : List Bool) :
    step (c (some .undoE) (norm ca s acc) q E (b :: W) A Bq D) =
      c (some .undoE) (norm ca s acc) q (b :: E) W A Bq D := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

theorem undo_nil (ca s acc) (q E A Bq D : List Bool) :
    step (c (some .undoE) (norm ca s acc) q E [] A Bq D) =
      c none { norm ca s acc with t1 := none } q E [] A Bq D := by
  apply cfg_ext rfl rfl; intro j; fin_cases j <;> rfl

/-! ### Loops -/

theorem rep_cons (i : Nat) (A : List Bool) :
    List.replicate i true ++ true :: A = List.replicate (i + 1) true ++ A := by
  rw [List.replicate_succ', List.append_assoc, List.singleton_append]


theorem readA_loop (ca s acc) (a : Nat) : ∀ (q E W A Bq D : List Bool),
    (step^[a]) (c (some .readA) (norm ca s acc) q (List.replicate a true ++ E) W A Bq D) =
      c (some .readA) (norm ca s acc) q E (List.replicate a true ++ W)
        (List.replicate a true ++ A) Bq D := by
  induction a with
  | zero => intro q E W A Bq D; rfl
  | succ a ih =>
    intro q E W A Bq D
    conv_lhs => rw [List.replicate_succ, List.cons_append]
    rw [Function.iterate_succ_apply, readA_true, ih, rep_cons, rep_cons]

theorem readB_loop (ca s acc) (b : Nat) : ∀ (q E W A Bq D : List Bool),
    (step^[b]) (c (some .readB) (norm ca s acc) q (List.replicate b true ++ E) W A Bq D) =
      c (some .readB) (norm ca s acc) q E (List.replicate b true ++ W) A
        (List.replicate b true ++ Bq) D := by
  induction b with
  | zero => intro q E W A Bq D; rfl
  | succ b ih =>
    intro q E W A Bq D
    conv_lhs => rw [List.replicate_succ, List.cons_append]
    rw [Function.iterate_succ_apply, readB_true, ih, rep_cons, rep_cons]

theorem fetchA_loop (ca s acc) (a : Nat) : ∀ (q E W Bq D : List Bool), 2 * a ≤ q.length →
    (step^[a]) (c (some .fetchA) (norm ca s acc) q E W (List.replicate a true) Bq D) =
      c (some .fetchA) (norm ca s acc) (q.drop (2 * a)) E W [] Bq
        ((q.take (2 * a)).reverse ++ D) := by
  induction a with
  | zero => intro q E W Bq D _; simp [c]
  | succ a ih =>
    intro q E W Bq D hq
    match q, hq with
    | b0 :: b1 :: q', hq =>
      have hq' : 2 * a ≤ q'.length := by simp at hq; omega
      rw [Function.iterate_succ_apply, List.replicate_succ, fetchA_cons, ih q' E W Bq _ hq']
      have e1 : 2 * (a + 1) = 2 * a + 2 := by ring
      simp only [e1, List.drop_succ_cons, List.take_succ_cons, List.reverse_cons,
        List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]

theorem fetchB_loop (ca s acc) (b : Nat) : ∀ (q E W A D : List Bool), 2 * b ≤ q.length →
    (step^[b]) (c (some .fetchB) (norm ca s acc) q E W A (List.replicate b true) D) =
      c (some .fetchB) (norm ca s acc) (q.drop (2 * b)) E W A []
        ((q.take (2 * b)).reverse ++ D) := by
  induction b with
  | zero => intro q E W A D _; simp [c]
  | succ b ih =>
    intro q E W A D hq
    match q, hq with
    | b0 :: b1 :: q', hq =>
      have hq' : 2 * b ≤ q'.length := by simp at hq; omega
      rw [Function.iterate_succ_apply, List.replicate_succ, fetchB_cons, ih q' E W A _ hq']
      have e1 : 2 * (b + 1) = 2 * b + 2 := by ring
      simp only [e1, List.drop_succ_cons, List.take_succ_cons, List.reverse_cons,
        List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]

theorem restA_loop (ca s acc) : ∀ (D q E W A Bq : List Bool),
    (step^[D.length]) (c (some .restA) (norm ca s acc) q E W A Bq D) =
      c (some .restA) (norm ca s acc) (D.reverse ++ q) E W A Bq [] := by
  intro D
  induction D with
  | nil => intro q E W A Bq; rfl
  | cons b D ih =>
    intro q E W A Bq
    rw [List.length_cons, Function.iterate_succ_apply, restA_cons, ih]
    simp

theorem restB_loop (ca s acc) : ∀ (D q E W A Bq : List Bool),
    (step^[D.length]) (c (some .restB) (norm ca s acc) q E W A Bq D) =
      c (some .restB) (norm ca s acc) (D.reverse ++ q) E W A Bq [] := by
  intro D
  induction D with
  | nil => intro q E W A Bq; rfl
  | cons b D ih =>
    intro q E W A Bq
    rw [List.length_cons, Function.iterate_succ_apply, restB_cons, ih]
    simp

theorem undo_loop (ca s acc) : ∀ (W q E A Bq D : List Bool),
    (step^[W.length]) (c (some .undoE) (norm ca s acc) q E W A Bq D) =
      c (some .undoE) (norm ca s acc) q (W.reverse ++ E) [] A Bq D := by
  intro W
  induction W with
  | nil => intro q E A Bq D; rfl
  | cons b W ih =>
    intro q E A Bq D
    rw [List.length_cons, Function.iterate_succ_apply, undo_cons, ih]
    simp

theorem undo_run (ca s acc) (W q E : List Bool) :
    (step^[W.length + 1]) (c (some .undoE) (norm ca s acc) q E W [] [] []) =
      c none { norm ca s acc with t1 := none } q (W.reverse ++ E) [] [] [] [] := by
  rw [Function.iterate_succ_apply', undo_loop, undo_nil]

/-- Two-bit access: the counter word at an endpoint. -/
theorem drop_cons2 (q : List Bool) (a : Nat) (h : 2 * a + 2 ≤ q.length) :
    ∃ b0 b1 r, q.drop (2 * a) = b0 :: b1 :: r := by
  have hl : 2 ≤ (q.drop (2 * a)).length := by simp; omega
  match hq : q.drop (2 * a), hl with
  | b0 :: b1 :: r, _ => exact ⟨b0, b1, r, rfl⟩

theorem chain {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (h1 : f^[m] x = y) (h2 : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, h1, h2]

theorem one_step {x y : TM2.Cfg (fun _ : K => Bool) Lab Ctl} (h : step x = y) :
    step^[1] x = y := by
  rw [Function.iterate_one, h]

/-- One edge: read both unary endpoints, access both two-bit digits (walking the
counter and restoring it), compare the decoded colours. Every step counted. -/
theorem edge_run (ca : Fin 3) (s : Bool) (a b : Nat) (q E W : List Bool)
    (ha : 2 * a + 2 ≤ q.length) (hb : 2 * b + 2 ≤ q.length) :
    ∃ (ca' : Fin 3) (s' : Bool),
      (step^[4 * a + 4 * b + 6]) (c (some .readA) (norm ca s false) q
          (edgeWord1 a b ++ E) W [] [] []) =
        c (some (if decode2 (q.drop (2 * a)) = decode2 (q.drop (2 * b))
            then Lab.undoE else Lab.readA))
          (norm ca' s' false) q E ((edgeWord1 a b).reverse ++ W) [] [] [] := by
  obtain ⟨b0, b1, r, hr⟩ := drop_cons2 q a ha
  obtain ⟨d0, d1, r', hr'⟩ := drop_cons2 q b hb
  have heq : edgeWord1 a b ++ E =
      List.replicate a true ++ false :: (List.replicate b true ++ false :: E) := by
    simp [edgeWord1]
  have hW : (edgeWord1 a b).reverse ++ W =
      false :: (List.replicate b true ++ false :: (List.replicate a true ++ W)) := by
    simp [edgeWord1]
  rw [heq, hW]
  have h1 := readA_loop ca s false a q (false :: (List.replicate b true ++ false :: E)) W
    [] [] []
  simp only [List.append_nil] at h1
  have h2 := one_step (readA_false ca s false q (List.replicate b true ++ false :: E)
    (List.replicate a true ++ W) (List.replicate a true) [] [])
  have h3 := readB_loop ca s false b q (false :: E) (false :: (List.replicate a true ++ W))
    (List.replicate a true) [] []
  simp only [List.append_nil] at h3
  have h4 := one_step (readB_false ca s false q E
    (List.replicate b true ++ false :: (List.replicate a true ++ W))
    (List.replicate a true) (List.replicate b true) [])
  have h5 := fetchA_loop ca s false a q E
    (false :: (List.replicate b true ++ false :: (List.replicate a true ++ W)))
    (List.replicate b true) [] (by omega)
  rw [hr, List.append_nil] at h5
  have h6 := one_step (fetchA_nil ca s false b0 b1 r E
    (false :: (List.replicate b true ++ false :: (List.replicate a true ++ W)))
    (List.replicate b true) (List.take (2 * a) q).reverse)
  have h7 := restA_loop (dec b0 b1) s false (List.take (2 * a) q).reverse (b0 :: b1 :: r) E
    (false :: (List.replicate b true ++ false :: (List.replicate a true ++ W))) []
    (List.replicate b true)
  have hq : (List.take (2 * a) q).reverse.reverse ++ b0 :: b1 :: r = q := by
    rw [List.reverse_reverse, ← hr, List.take_append_drop]
  rw [hq] at h7
  have h8 := one_step (restA_nil (dec b0 b1) s false q E
    (false :: (List.replicate b true ++ false :: (List.replicate a true ++ W))) []
    (List.replicate b true))
  have h9 := fetchB_loop (dec b0 b1) s false b q E
    (false :: (List.replicate b true ++ false :: (List.replicate a true ++ W))) [] []
    (by omega)
  rw [hr', List.append_nil] at h9
  have h10 := one_step (fetchB_nil (dec b0 b1) s false d0 d1 r' E
    (false :: (List.replicate b true ++ false :: (List.replicate a true ++ W))) []
    (List.take (2 * b) q).reverse)
  have h11 := restB_loop (dec b0 b1) (decide (dec d0 d1 = dec b0 b1)) false
    (List.take (2 * b) q).reverse (d0 :: d1 :: r') E
    (false :: (List.replicate b true ++ false :: (List.replicate a true ++ W))) [] []
  have hq' : (List.take (2 * b) q).reverse.reverse ++ d0 :: d1 :: r' = q := by
    rw [List.reverse_reverse, ← hr', List.take_append_drop]
  rw [hq'] at h11
  have hlA : (List.take (2 * a) q).reverse.length = 2 * a := by simp; omega
  have hlB : (List.take (2 * b) q).reverse.length = 2 * b := by simp; omega
  rw [hlA] at h7
  rw [hlB] at h11
  have hA : decode2 (q.drop (2 * a)) = dec b0 b1 := by rw [hr]; rfl
  have hB : decode2 (q.drop (2 * b)) = dec d0 d1 := by rw [hr']; rfl
  have hcount : 4 * a + 4 * b + 6 =
      1 + (2 * b + (1 + (b + (1 + (2 * a + (1 + (a + (1 + (b + (1 + a)))))))))) := by ring
  rw [hA, hB, hcount]
  by_cases hc : dec b0 b1 = dec d0 d1
  · have h12 := one_step (restB_same (dec b0 b1) false q E
      (false :: (List.replicate b true ++ false :: (List.replicate a true ++ W))) [] [])
    have hd : decide (dec d0 d1 = dec b0 b1) = true := by simp [hc]
    rw [hd] at h10 h11
    refine ⟨dec b0 b1, true, ?_⟩
    rw [if_pos hc]
    exact chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain
      h1 h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12
  · have h12 := one_step (restB_diff (dec b0 b1) false q E
      (false :: (List.replicate b true ++ false :: (List.replicate a true ++ W))) [] [])
    have hd : decide (dec d0 d1 = dec b0 b1) = false := by
      simp only [decide_eq_false_iff_not]; exact fun h => hc h.symm
    rw [hd] at h10 h11
    refine ⟨dec b0 b1, false, ?_⟩
    rw [if_neg hc]
    exact chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain
      h1 h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12

theorem edgeWord1_length (a b : Nat) : (edgeWord1 a b).length = a + b + 2 := by
  simp [edgeWord1]; omega

/-- The whole edge tape: first monochromatic edge stops the test; the processed
edges are moved back, so the edge tape is restored exactly. -/
theorem edges_run (v : Nat) (q : List Bool) (hq : q.length = 2 * v) :
    ∀ (es : List (Nat × Nat)) (done : List Bool) (ca : Fin 3) (s : Bool),
      (∀ p ∈ es, p.1 < v ∧ p.2 < v) →
      ∃ t ≤ es.length * (8 * v) + done.length + (edgesWord es).length + 2, ∃ vf : Ctl,
        vf.acc = edgesOK q es ∧
        (step^[t]) (c (some .readA) (norm ca s false) q (edgesWord es) done.reverse [] [] []) =
          c none vf q (done ++ edgesWord es) [] [] [] [] := by
  intro es
  induction es with
  | nil =>
    intro done ca s _
    have h1 := one_step (readA_nil ca s false q done.reverse [] [] [])
    have h2 := undo_run ca s true done.reverse q []
    refine ⟨done.reverse.length + 1 + 1, by simp, { norm ca s true with t1 := none }, rfl, ?_⟩
    have h := chain h1 h2
    simpa [edgesWord] using h
  | cons p es ih =>
    intro done ca s hall
    obtain ⟨a, b⟩ := p
    have hab := hall (a, b) (List.mem_cons_self ..)
    have hrest : ∀ p ∈ es, p.1 < v ∧ p.2 < v := fun p hp => hall p (List.mem_cons_of_mem _ hp)
    have hav : a < v := hab.1
    have hbv : b < v := hab.2
    obtain ⟨ca', s', he⟩ := edge_run ca s a b q (edgesWord es) done.reverse
      (by omega) (by omega)
    have hm : (es.length + 1) * (8 * v) = es.length * (8 * v) + 8 * v := Nat.succ_mul _ _
    have hl := edgeWord1_length a b
    show ∃ t ≤ (es.length + 1) * (8 * v) + done.length + (edgeWord1 a b ++ edgesWord es).length + 2,
      ∃ vf : Ctl, vf.acc = edgesOK q ((a, b) :: es) ∧
        (step^[t]) (c (some .readA) (norm ca s false) q (edgeWord1 a b ++ edgesWord es)
          done.reverse [] [] []) = c none vf q (done ++ (edgeWord1 a b ++ edgesWord es)) [] [] [] []
    rw [List.length_append, hm]
    by_cases hc : decode2 (q.drop (2 * a)) = decode2 (q.drop (2 * b))
    · rw [if_pos hc] at he
      have h2 := undo_run ca' s' false ((edgeWord1 a b).reverse ++ done.reverse) q (edgesWord es)
      refine ⟨((edgeWord1 a b).reverse ++ done.reverse).length + 1 + (4 * a + 4 * b + 6),
        ?_, { norm ca' s' false with t1 := none }, ?_, ?_⟩
      · simp only [List.length_append, List.length_reverse]; omega
      · simp [edgesOK, hc, norm]
      · have h := chain he h2
        simpa [List.reverse_append, List.append_assoc] using h
    · rw [if_neg hc] at he
      obtain ⟨t, ht, vf, hacc, hrun⟩ := ih (done ++ edgeWord1 a b) ca' s' hrest
      rw [List.reverse_append] at hrun
      refine ⟨t + (4 * a + 4 * b + 6), ?_, vf, ?_, ?_⟩
      · simp only [List.length_append] at ht; omega
      · simp [edgesOK, hc, hacc]
      · have h := chain he hrun
        simpa [List.append_assoc] using h

def Sbank (es : List (Nat × Nat)) : K → List Bool := bk [] (edgesWord es) [] [] [] []
def v0 : Ctl := norm 0 false false

theorem update_Sbank (es : List (Nat × Nat)) (q : List Bool) :
    Function.update (Sbank es) 0 q = bk q (edgesWord es) [] [] [] [] := by
  funext j; fin_cases j <;> rfl

/-- The predicate program's contract, exactly in the admitted controller's form. -/
theorem pred_run (v : Nat) (es : List (Nat × Nat)) (hes : ∀ p ∈ es, p.1 < v ∧ p.2 < v)
    (q : List Bool) (hq : q.length = 2 * v) :
    ∃ (t : ℕ) (vf : Ctl), t ≤ es.length * (8 * v) + (edgesWord es).length + 2 ∧
      ((advance P)^[t]) ⟨some Lab.readA, v0, Function.update (Sbank es) 0 q⟩ =
        ⟨none, vf, Function.update (Sbank es) 0 q⟩ ∧ vf.acc = edgesOK q es := by
  obtain ⟨t, ht, vf, hacc, hrun⟩ := edges_run v q hq es [] 0 false hes
  refine ⟨t, vf, by simpa using ht, ?_, hacc⟩
  rw [update_Sbank]
  simpa [c, v0] using hrun

/-! ### Semantics of the decoded colouring -/

theorem edgesOK_iff (q : List Bool) (es : List (Nat × Nat)) :
    edgesOK q es = true ↔ ∀ p ∈ es, decode2 (q.drop (2 * p.1)) ≠ decode2 (q.drop (2 * p.2)) := by
  induction es with
  | nil => simp [edgesOK]
  | cons p es ih => obtain ⟨a, b⟩ := p; simp [edgesOK, ih]

theorem mem_edgeList {v e : Nat} (edge : Fin e → Bool → Fin v) (p : Nat × Nat) :
    p ∈ edgeList edge ↔ ∃ z, ((edge z false).val, (edge z true).val) = p := by
  simp [edgeList]

theorem edgeList_bound {v e : Nat} (edge : Fin e → Bool → Fin v) :
    ∀ p ∈ edgeList edge, p.1 < v ∧ p.2 < v := by
  intro p hp
  obtain ⟨z, rfl⟩ := (mem_edgeList edge p).1 hp
  exact ⟨(edge z false).isLt, (edge z true).isLt⟩

theorem encC_cons (x : Fin 3) (l : List Bool) :
    ∃ y0 y1, encC x ++ l = y0 :: y1 :: l ∧ dec y0 y1 = x := by
  fin_cases x
  · exact ⟨false, false, rfl, rfl⟩
  · exact ⟨true, false, rfl, rfl⟩
  · exact ⟨false, true, rfl, rfl⟩

theorem colWord_length (L : List (Fin 3)) : (colWord L).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    obtain ⟨y0, y1, h, -⟩ := encC_cons x (colWord L)
    simp only [colWord, h, List.length_cons, ih]; ring

theorem decode2_colWord (L : List (Fin 3)) : ∀ (a : Nat) (ha : a < L.length),
    decode2 ((colWord L).drop (2 * a)) = L[a] := by
  induction L with
  | nil => intro a ha; simp at ha
  | cons x L ih =>
    intro a ha
    obtain ⟨y0, y1, h, hd⟩ := encC_cons x (colWord L)
    rcases a with _ | a
    · simp only [colWord, h, Nat.mul_zero, List.drop_zero, List.getElem_cons_zero]
      exact hd
    · have e : 2 * (a + 1) = 2 * a + 2 := by ring
      simp only [colWord, h, e, List.drop_succ_cons, List.getElem_cons_succ]
      exact ih a (by simp at ha; omega)

theorem colourable_iff_exists {v e : Nat} (edge : Fin e → Bool → Fin v) :
    FiniteFallbackOutput.ThreeColourable edge ↔
      ∃ q : List Bool, q.length = 2 * v ∧ edgesOK q (edgeList edge) = true := by
  constructor
  · rintro ⟨col, hcol⟩
    refine ⟨colWord (List.ofFn col), by rw [colWord_length, List.length_ofFn], ?_⟩
    rw [edgesOK_iff]
    intro p hp
    obtain ⟨z, rfl⟩ := (mem_edgeList edge p).1 hp
    rw [decode2_colWord _ _ (by simp), decode2_colWord _ _ (by simp)]
    simpa using hcol z
  · rintro ⟨q, -, hq⟩
    refine ⟨fun u => decode2 (q.drop (2 * u.val)), ?_⟩
    intro z
    exact (edgesOK_iff q _).1 hq _ ((mem_edgeList edge _).2 ⟨z, rfl⟩)

theorem mem_counterWords (q : List Bool) : q ∈ SamplerEnumeration.counterWords q.length := by
  have h := SamplerEnumeration.counterWords_contains (n := q.length)
    (fun i => SamplerHorner.decodeBit q[i])
  have e : SamplerMachine.encodeWord
      (fun i : Fin q.length => SamplerHorner.decodeBit q[i]) = q := by
    simp [SamplerMachine.encodeWord, SamplerHorner.encodeBit_decodeBit]
  rwa [e] at h

theorem counterWords_length_of_mem (n : Nat) (q : List Bool)
    (h : q ∈ List.iterate SamplerMachineIncrement.increment (List.replicate n false) (2 ^ n)) :
    q.length = n := by
  obtain ⟨m, -, rfl⟩ := List.mem_iterate.1 h
  exact SamplerEnumeration.increment_iterate_length n m

theorem bitsValue_zero (m : Nat) :
    EncodedCommunication.bitsValue (List.replicate m false) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [EncodedCommunication.bitsValue, List.replicate_succ, ih, Nat.bit_val]

/-- Per-candidate charged clock of the predicate program. -/
def T {v e : Nat} (edge : Fin e → Bool → Fin v) : Nat :=
  (edgeList edge).length * (8 * v) + (edgesWord (edgeList edge)).length + 2

/-- U16 search (enumeration with carry + access + test, every step charged): the
admitted controller, run with the fixed predicate program `P` from the all-zero
counter of width `2v`, halts within `4^v` candidate rounds and its physical
accept bit is exactly the finite three-colourability decision. -/
theorem search_decides {v e : Nat} (edge : Fin e → Bool → Fin v) :
    ∃ (t : ℕ) (vc : Ctl) (flag : Bool) (q' : List Bool),
      t ≤ 2 ^ (2 * v) * (T edge + 4 * (2 * v) + 6) ∧
      vc.acc = decide (FiniteFallbackOutput.ThreeColourable edge) ∧
      SamplerMachineSearch.run P 0 Lab.readA v0 Ctl.acc t
        (SamplerMachineSearch.cfg 0 (Sbank (edgeList edge)) (some (.inl Lab.readA))
          (v0, false, none) (List.replicate (2 * v) false) []) =
        SamplerMachineSearch.cfg 0 (Sbank (edgeList edge)) none (vc, flag, none) q' [] := by
  have hP : ∀ q : List Bool, q.length = 2 * v →
      ∃ (t : ℕ) (vf : Ctl), t ≤ T edge ∧
        ((advance P)^[t]) ⟨some Lab.readA, v0, Function.update (Sbank (edgeList edge)) 0 q⟩ =
          ⟨none, vf, Function.update (Sbank (edgeList edge)) 0 q⟩ ∧
        Ctl.acc vf = edgesOK q (edgeList edge) :=
    fun q hq => pred_run v (edgeList edge) (edgeList_bound edge) q hq
  by_cases h : FiniteFallbackOutput.ThreeColourable edge
  · obtain ⟨q0, hq0, hok⟩ := (colourable_iff_exists edge).1 h
    have hmem : q0 ∈ SamplerEnumeration.counterWords (2 * v) := by
      have := mem_counterWords q0; rwa [hq0] at this
    cases hf : (SamplerEnumeration.counterWords (2 * v)).find?
        (fun q => edgesOK q (edgeList edge)) with
    | none =>
      exact absurd hok (by simpa using List.find?_eq_none.1 hf q0 hmem)
    | some found =>
      obtain ⟨t, vc, ht, hacc, hrun⟩ := SamplerMachineSearch.search_allWords P 0 Lab.readA v0
        Ctl.acc (Sbank (edgeList edge)) (2 * v) (T edge) (fun q => edgesOK q (edgeList edge))
        hP found hf
      exact ⟨t, vc, false, found, ht, by simp [hacc, h], hrun⟩
  · have hc : 2 ^ (2 * v) - 1 + 1 = 2 ^ (2 * v) := Nat.sub_add_cancel Nat.one_le_two_pow
    have hnone : (List.iterate SamplerMachineIncrement.increment (List.replicate (2 * v) false)
        (2 ^ (2 * v) - 1 + 1)).find? (fun q => edgesOK q (edgeList edge)) = none := by
      rw [hc]
      apply List.find?_eq_none.2
      intro q hq hok
      have hl := counterWords_length_of_mem (2 * v) q hq
      exact h ((colourable_iff_exists edge).2 ⟨q, hl, by simpa using hok⟩)
    obtain ⟨t, vc, ht, hacc, hrun⟩ := SamplerMachineSearch.search_none P 0 Lab.readA v0
      Ctl.acc (Sbank (edgeList edge)) (2 * v) (T edge) (fun q => edgesOK q (edgeList edge))
      hP (2 ^ (2 * v) - 1) (List.replicate (2 * v) false) (by simp)
      (by rw [bitsValue_zero]; omega) hnone
    refine ⟨t, vc, true, _, by rw [hc] at ht; exact ht, by simp [hacc, h], hrun⟩

/-- Identity with the ledger's semantic search bit. -/
theorem search_decides_eq_search {v e : Nat} (edge : Fin e → Bool → Fin v) :
    decide (FiniteFallbackOutput.ThreeColourable edge) =
      (FiniteFallbackSearchScratch.search edge).1 := by
  cases h : (FiniteFallbackSearchScratch.search edge).1
  · simp only [decide_eq_false_iff_not]
    intro hc
    have := (FiniteFallbackSearchScratch.search_found_iff edge).2 hc
    rw [h] at this; cases this
  · simpa using (FiniteFallbackSearchScratch.search_found_iff edge).1 h

theorem edgesWord_length_le {v e : Nat} (edge : Fin e → Bool → Fin v) :
    (edgesWord (edgeList edge)).length ≤ e * (2 * v) := by
  have key : ∀ es : List (Nat × Nat), (∀ p ∈ es, p.1 < v ∧ p.2 < v) →
      (edgesWord es).length ≤ es.length * (2 * v) := by
    intro es
    induction es with
    | nil => intro _; simp [edgesWord]
    | cons p es ih =>
      intro hall
      obtain ⟨a, b⟩ := p
      have hab := hall (a, b) (List.mem_cons_self ..)
      have hav : a < v := hab.1
      have hbv : b < v := hab.2
      have hr := ih (fun p hp => hall p (List.mem_cons_of_mem _ hp))
      simp only [edgesWord, List.length_append, edgeWord1_length, List.length_cons]
      rw [Nat.succ_mul]; omega
  have h := key (edgeList edge) (edgeList_bound edge)
  simpa [edgeList] using h

/-- Search clock as a function of `v` and `e` only. -/
theorem search_clock_le {v e : Nat} (edge : Fin e → Bool → Fin v) :
    2 ^ (2 * v) * (T edge + 4 * (2 * v) + 6) ≤ 4 ^ v * (10 * (e + 1) * (v + 1)) := by
  have h1 := edgesWord_length_le edge
  have h2 : (edgeList edge).length = e := by simp [edgeList]
  have h4 : (2 : Nat) ^ (2 * v) = 4 ^ v := by rw [pow_mul]; norm_num
  rw [h4]
  apply Nat.mul_le_mul_left
  unfold T
  rw [h2]
  nlinarith

#print axioms edge_run
#print axioms edges_run
#print axioms pred_run
#print axioms colourable_iff_exists
#print axioms search_decides
#print axioms search_decides_eq_search
#print axioms search_clock_le

end Paper2.FallbackColourSearch
