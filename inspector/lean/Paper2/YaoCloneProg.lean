import Paper2.YaoCloneSpec
import EthInapproximability.CurrentPaper.BitMachineComposition

/-! Unit 5 segment Y10 (lane a-yao-clone-owner-1): the physical clone machine,
program and single-phase runs.

ONE fixed TM2 program for fixed `K` (edge arity) and `M = K*S` (clones per
vertex).  Stacks: `inp` (input), `vm` (unary `v*M`), `ec` (unary edge counter),
`acc` (the output body, reversed), `cnt` (unary output edge count), `out`,
and for each position `j < K` a label stack `lab j` and a restore stack
`res j`.  Finite control: labels carry the edge's equality pattern `P`, the
pair index `q`, the lift index `n`, the current lift `r` and the position
`j` (all finite); the control state is the last two popped bits.

Per occurrence edge: load its `K` fields into `lab`; compare all `K*K`
pairs of unary labels (simultaneous pops, then restore) to obtain the
equality pattern; for every `r` in the explicit lexicographic list
`allFuns M K` (the admitted `YaoCloneSrc.allFuns`) test `injB P r` and, if
injective, print the `K` fields `l j * M + r j` (each label mark pushes `M`
marks; then `r j` marks and the terminator) and count the edge; then clear
`lab`.  Finally the body is reversed onto `out`, and the two unary headers
`e'` and `max 1 (v*M)` are pushed. -/

namespace Paper2.YaoCloneMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoCloneSource
open Paper2.YaoSourceCodec

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

inductive Stk (K : ℕ) where
  | inp | vm | ec | acc | cnt | out
  | lab (j : Fin K) | res (j : Fin K)
  deriving DecidableEq, Fintype

abbrev Pat (K : ℕ) := Fin K → Fin K → Bool

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2048 in
inductive Lbl (K M : ℕ) where
  | hv | he | edge
  | load (j : Fin (K + 1))
  | cmp (P : Fin K → Fin K → Bool) (q : Fin (K * K + 1))
  | cmpLoop (P : Fin K → Fin K → Bool) (q : Fin (K * K)) (i j : Fin K)
  | restI (P : Fin K → Fin K → Bool) (q : Fin (K * K)) (i j : Fin K)
  | restJ (P : Fin K → Fin K → Bool) (q : Fin (K * K)) (i j : Fin K)
  | lift (P : Fin K → Fin K → Bool) (n : Fin (M ^ K + 1))
  | pr (P : Fin K → Fin K → Bool) (n : Fin (M ^ K)) (r : Fin K → Fin M) (j : Fin (K + 1))
  | rs (P : Fin K → Fin K → Bool) (n : Fin (M ^ K)) (r : Fin K → Fin M) (j : Fin K)
  | clr (j : Fin (K + 1))
  | fin1 | fin2 | fin3 | fin4
  deriving Fintype

abbrev St := Option Bool × Option Bool

variable {K M : ℕ}

abbrev Stm (K M : ℕ) := TM2.Stmt (fun _ : Stk K => Bool) (Lbl K M) St

def pushN (k : Stk K) : ℕ → Stm K M → Stm K M
  | 0, q => q
  | n + 1, q => push k (fun _ => true) (pushN k n q)

def updP (P : Pat K) (i j : Fin K) (b : Bool) : Pat K :=
  Function.update P i (Function.update (P i) j b)

/-- The `n`-th lift of the explicit lexicographic list. -/
def liftAt (n : Fin (M ^ K)) : Fin K → Fin M :=
  (allFuns M K)[n.val]'(by rw [length_allFuns]; exact n.isLt)

def pairAt (q : Fin (K * K)) : Fin K × Fin K := finProdFinEquiv.symm q

def program : Lbl K M → Stm K M
  | .hv => pop .inp (fun _ b => (b, none))
      (branch (fun s => s.1 == some true) (pushN .vm M (goto fun _ => .hv)) (goto fun _ => .he))
  | .he => pop .inp (fun _ b => (b, none))
      (branch (fun s => s.1 == some true) (push .ec (fun _ => true) (goto fun _ => .he))
        (goto fun _ => .edge))
  | .edge => pop .ec (fun _ b => (b, none))
      (branch (fun s => s.1.isSome) (goto fun _ => .load 0) (goto fun _ => .fin1))
  | .load j => if h : j.val < K then
        pop .inp (fun _ b => (b, none))
          (branch (fun s => s.1 == some true)
            (push (.lab ⟨j.val, h⟩) (fun _ => true) (goto fun _ => .load j))
            (goto fun _ => .load ⟨j.val + 1, by omega⟩))
      else goto fun _ => .cmp (fun _ _ => false) 0
  | .cmp P q => if h : q.val < K * K then
        (if (pairAt ⟨q.val, h⟩).1 = (pairAt ⟨q.val, h⟩).2 then
          goto fun _ => .cmp (updP P (pairAt ⟨q.val, h⟩).1 (pairAt ⟨q.val, h⟩).2 true)
            ⟨q.val + 1, by omega⟩
         else goto fun _ => .cmpLoop P ⟨q.val, h⟩ (pairAt ⟨q.val, h⟩).1 (pairAt ⟨q.val, h⟩).2)
      else goto fun _ => .lift P 0
  | .cmpLoop P q i j => pop (.lab i) (fun _ b => (b, none)) (pop (.lab j) (fun s b => (s.1, b))
      (branch (fun s => s.1.isSome && s.2.isSome)
        (push (.res i) (fun _ => true) (push (.res j) (fun _ => true)
          (goto fun _ => .cmpLoop P q i j)))
        (branch (fun s => s.1.isSome)
          (push (.res i) (fun _ => true) (goto fun _ => .restI (updP P i j false) q i j))
          (branch (fun s => s.2.isSome)
            (push (.res j) (fun _ => true) (goto fun _ => .restI (updP P i j false) q i j))
            (goto fun _ => .restI (updP P i j true) q i j)))))
  | .restI P q i j => pop (.res i) (fun _ b => (b, none))
      (branch (fun s => s.1.isSome) (push (.lab i) (fun _ => true) (goto fun _ => .restI P q i j))
        (goto fun _ => .restJ P q i j))
  | .restJ P q i j => pop (.res j) (fun _ b => (b, none))
      (branch (fun s => s.1.isSome) (push (.lab j) (fun _ => true) (goto fun _ => .restJ P q i j))
        (goto fun _ => .cmp P ⟨q.val + 1, by omega⟩))
  | .lift P n => if h : n.val < M ^ K then
        (if injB P (liftAt ⟨n.val, h⟩) then
          push .cnt (fun _ => true) (goto fun _ => .pr P ⟨n.val, h⟩ (liftAt ⟨n.val, h⟩) 0)
         else goto fun _ => .lift P ⟨n.val + 1, by omega⟩)
      else goto fun _ => .clr 0
  | .pr P n r j => if h : j.val < K then
        pop (.lab ⟨j.val, h⟩) (fun _ b => (b, none))
          (branch (fun s => s.1.isSome)
            (push (.res ⟨j.val, h⟩) (fun _ => true) (pushN .acc M (goto fun _ => .pr P n r j)))
            (pushN .acc (r ⟨j.val, h⟩).val (push .acc (fun _ => false)
              (goto fun _ => .rs P n r ⟨j.val, h⟩))))
      else goto fun _ => .lift P ⟨n.val + 1, by omega⟩
  | .rs P n r j => pop (.res j) (fun _ b => (b, none))
      (branch (fun s => s.1.isSome) (push (.lab j) (fun _ => true) (goto fun _ => .rs P n r j))
        (goto fun _ => .pr P n r ⟨j.val + 1, by omega⟩))
  | .clr j => if h : j.val < K then
        pop (.lab ⟨j.val, h⟩) (fun _ b => (b, none))
          (branch (fun s => s.1.isSome) (goto fun _ => .clr j)
            (goto fun _ => .clr ⟨j.val + 1, by omega⟩))
      else goto fun _ => .edge
  | .fin1 => pop .acc (fun _ b => (b, none))
      (branch (fun s => s.1.isSome) (push .out (fun s => s.1.getD false) (goto fun _ => .fin1))
        (push .out (fun _ => false) (goto fun _ => .fin2)))
  | .fin2 => pop .cnt (fun _ b => (b, none))
      (branch (fun s => s.1.isSome) (push .out (fun _ => true) (goto fun _ => .fin2))
        (push .out (fun _ => false) (goto fun _ => .fin3)))
  | .fin3 => pop .vm (fun _ b => (b, none))
      (branch (fun s => s.1.isSome) (push .out (fun _ => true) (goto fun _ => .fin4))
        (push .out (fun _ => true) halt))
  | .fin4 => pop .vm (fun _ b => (b, none))
      (branch (fun s => s.1.isSome) (push .out (fun _ => true) (goto fun _ => .fin4)) halt)

/-! ## Banks -/

def bk (inp vm ec acc cnt out : List Bool) (lab res : Fin K → List Bool) : Stk K → List Bool
  | .inp => inp | .vm => vm | .ec => ec | .acc => acc | .cnt => cnt | .out => out
  | .lab j => lab j | .res j => res j

section BankLemmas
variable (inp vm ec acc cnt out : List Bool) (lab res : Fin K → List Bool) (x : List Bool)

@[simp] theorem bk_inp : bk inp vm ec acc cnt out lab res .inp = inp := rfl
@[simp] theorem bk_vm : bk inp vm ec acc cnt out lab res .vm = vm := rfl
@[simp] theorem bk_ec : bk inp vm ec acc cnt out lab res .ec = ec := rfl
@[simp] theorem bk_acc : bk inp vm ec acc cnt out lab res .acc = acc := rfl
@[simp] theorem bk_cnt : bk inp vm ec acc cnt out lab res .cnt = cnt := rfl
@[simp] theorem bk_out : bk inp vm ec acc cnt out lab res .out = out := rfl
@[simp] theorem bk_lab (j : Fin K) : bk inp vm ec acc cnt out lab res (.lab j) = lab j := rfl
@[simp] theorem bk_res (j : Fin K) : bk inp vm ec acc cnt out lab res (.res j) = res j := rfl

macro "bank_ext" : tactic => `(tactic| (funext k; cases k <;> simp [bk, Function.update_apply]))

@[simp] theorem upd_inp : Function.update (bk inp vm ec acc cnt out lab res) .inp x =
    bk x vm ec acc cnt out lab res := by bank_ext
@[simp] theorem upd_vm : Function.update (bk inp vm ec acc cnt out lab res) .vm x =
    bk inp x ec acc cnt out lab res := by bank_ext
@[simp] theorem upd_ec : Function.update (bk inp vm ec acc cnt out lab res) .ec x =
    bk inp vm x acc cnt out lab res := by bank_ext
@[simp] theorem upd_acc : Function.update (bk inp vm ec acc cnt out lab res) .acc x =
    bk inp vm ec x cnt out lab res := by bank_ext
@[simp] theorem upd_cnt : Function.update (bk inp vm ec acc cnt out lab res) .cnt x =
    bk inp vm ec acc x out lab res := by bank_ext
@[simp] theorem upd_out : Function.update (bk inp vm ec acc cnt out lab res) .out x =
    bk inp vm ec acc cnt x lab res := by bank_ext
@[simp] theorem upd_lab (j : Fin K) : Function.update (bk inp vm ec acc cnt out lab res) (.lab j) x =
    bk inp vm ec acc cnt out (Function.update lab j x) res := by bank_ext
@[simp] theorem upd_res (j : Fin K) : Function.update (bk inp vm ec acc cnt out lab res) (.res j) x =
    bk inp vm ec acc cnt out lab (Function.update res j x) := by bank_ext

end BankLemmas

theorem pushN_stepAux (k : Stk K) (n : ℕ) (q : Stm K M) (v : St) (S : Stk K → List Bool) :
    TM2.stepAux (pushN k n q) v S = TM2.stepAux q v (Function.update S k (rep n ++ S k)) := by
  induction n generalizing S with
  | zero => simp [pushN]
  | succ n ih =>
      simp only [pushN, TM2.stepAux]
      rw [ih]
      congr 1
      rw [Function.update_idem, Function.update_self]
      congr 1
      simp [List.replicate_succ']

/-! ## Reachability -/

abbrev Cfg (K M : ℕ) := TM2.Cfg (fun _ : Stk K => Bool) (Lbl K M) St

def run (K M : ℕ) (n : ℕ) (c : Cfg K M) : Cfg K M := ((advance (program (K := K) (M := M)))^[n]) c

/-- From label `l` and bank `S` (any control), reach label `l'` and bank `S'`
within `bd` transitions. -/
def RIn (l : Lbl K M) (S : Stk K → List Bool) (l' : Option (Lbl K M)) (S' : Stk K → List Bool)
    (bd : ℕ) : Prop :=
  ∀ σ : St, ∃ n ≤ bd, ∃ σ' : St, run K M n ⟨some l, σ, S⟩ = ⟨l', σ', S'⟩

theorem RIn.trans {l l'' : Lbl K M} {l' : Option (Lbl K M)} {S S' S'' : Stk K → List Bool}
    {b₁ b₂ : ℕ} (h₁ : RIn l S (some l'') S' b₁) (h₂ : RIn l'' S' l' S'' b₂) :
    RIn l S l' S'' (b₁ + b₂) := by
  intro σ
  obtain ⟨n₁, hn₁, σ₁, r₁⟩ := h₁ σ
  obtain ⟨n₂, hn₂, σ₂, r₂⟩ := h₂ σ₁
  refine ⟨n₂ + n₁, by omega, σ₂, ?_⟩
  simp only [run, Function.iterate_add_apply] at r₁ r₂ ⊢
  rw [r₁, r₂]

theorem RIn.mono {l : Lbl K M} {l' : Option (Lbl K M)} {S S' : Stk K → List Bool} {b₁ b₂ : ℕ}
    (h : RIn l S l' S' b₁) (hb : b₁ ≤ b₂) : RIn l S l' S' b₂ := by
  intro σ
  obtain ⟨n, hn, σ', r⟩ := h σ
  exact ⟨n, by omega, σ', r⟩

theorem RIn.step {l : Lbl K M} {l' : Option (Lbl K M)} {S S' : Stk K → List Bool}
    (h : ∀ σ : St, ∃ σ' : St, TM2.step program ⟨some l, σ, S⟩ = some ⟨l', σ', S'⟩) :
    RIn l S l' S' 1 := by
  intro σ
  obtain ⟨σ', h⟩ := h σ
  exact ⟨1, le_rfl, σ', by simp only [run, Function.iterate_one, advance, h, Option.getD_some]⟩

/-- One transition followed by a run. -/
theorem RIn.cons {l l₁ : Lbl K M} {l' : Option (Lbl K M)} {S S₁ S' : Stk K → List Bool} {b : ℕ}
    (h : ∀ σ : St, ∃ σ' : St, TM2.step program ⟨some l, σ, S⟩ = some ⟨some l₁, σ', S₁⟩)
    (h₂ : RIn l₁ S₁ l' S' b) : RIn l S l' S' (b + 1) := by
  have := RIn.trans (RIn.step h) h₂
  simpa [Nat.add_comm] using this

/-! ## Header phase -/

section Header
variable (ec acc cnt out : List Bool) (lab res : Fin K → List Bool)

theorem hv_run (v : ℕ) : ∀ (r vm : List Bool),
    RIn (K := K) (M := M) .hv (bk (unaryNat v ++ r) vm ec acc cnt out lab res) (some .he)
      (bk r (rep (v * M) ++ vm) ec acc cnt out lab res) (v + 1) := by
  induction v with
  | zero =>
      intro r vm
      apply RIn.step
      intro σ
      simp [TM2.step, TM2.stepAux, program, unaryNat]
  | succ v ih =>
      intro r vm
      have h := ih r (rep M ++ vm)
      rw [show rep (v * M) ++ (rep M ++ vm) = rep ((v + 1) * M) ++ vm by
        rw [← List.append_assoc, ← List.replicate_add, Nat.succ_mul]] at h
      refine RIn.cons ?_ h
      intro σ
      simp [TM2.step, TM2.stepAux, program, pushN_stepAux, unaryNat, List.replicate_succ]

theorem he_run (e : ℕ) (vm : List Bool) : ∀ (r ec : List Bool),
    RIn (K := K) (M := M) .he (bk (unaryNat e ++ r) vm ec acc cnt out lab res) (some .edge)
      (bk r vm (rep e ++ ec) acc cnt out lab res) (e + 1) := by
  induction e with
  | zero =>
      intro r ec
      apply RIn.step
      intro σ
      simp [TM2.step, TM2.stepAux, program, unaryNat]
  | succ e ih =>
      intro r ec
      have h := ih r (true :: ec)
      rw [show rep e ++ true :: ec = rep (e + 1) ++ ec by
        simp [List.replicate_succ']] at h
      refine RIn.cons ?_ h
      intro σ
      simp [TM2.step, TM2.stepAux, program, unaryNat, List.replicate_succ]

end Header

/-! ## Final assembly phase -/

section Final
variable (inp ec : List Bool) (lab res : Fin K → List Bool)

theorem fin1_run (vm cnt : List Bool) : ∀ (xs out : List Bool),
    RIn (K := K) (M := M) .fin1 (bk inp vm ec xs cnt out lab res) (some .fin2)
      (bk inp vm ec [] cnt (false :: (xs.reverse ++ out)) lab res) (xs.length + 1)
  | [], out => by
      apply RIn.step
      intro σ
      simp [TM2.step, TM2.stepAux, program]
  | x :: xs, out => by
      have h := fin1_run vm cnt xs (x :: out)
      rw [show xs.reverse ++ x :: out = (x :: xs).reverse ++ out by simp] at h
      refine (RIn.cons ?_ h).mono (by simp)
      intro σ
      simp [TM2.step, TM2.stepAux, program]

theorem fin2_run (vm : List Bool) (c : ℕ) : ∀ (out : List Bool),
    RIn (K := K) (M := M) .fin2 (bk inp vm ec [] (rep c) out lab res) (some .fin3)
      (bk inp vm ec [] [] (false :: (rep c ++ out)) lab res) (c + 1) := by
  induction c with
  | zero =>
      intro out
      apply RIn.step
      intro σ
      simp [TM2.step, TM2.stepAux, program]
  | succ c ih =>
      intro out
      have h := ih (true :: out)
      rw [show rep c ++ true :: out = rep (c + 1) ++ out by simp [List.replicate_succ']] at h
      refine RIn.cons ?_ h
      intro σ
      simp [TM2.step, TM2.stepAux, program, List.replicate_succ]

theorem fin4_run (w : ℕ) : ∀ (out : List Bool),
    RIn (K := K) (M := M) .fin4 (bk inp (rep w) ec [] [] out lab res) none
      (bk inp [] ec [] [] (rep w ++ out) lab res) (w + 1) := by
  induction w with
  | zero =>
      intro out
      apply RIn.step
      intro σ
      simp [TM2.step, TM2.stepAux, program]
  | succ w ih =>
      intro out
      have h := ih (true :: out)
      rw [show rep w ++ true :: out = rep (w + 1) ++ out by simp [List.replicate_succ']] at h
      refine RIn.cons ?_ h
      intro σ
      simp [TM2.step, TM2.stepAux, program, List.replicate_succ]

theorem fin3_run (w : ℕ) (out : List Bool) :
    RIn (K := K) (M := M) .fin3 (bk inp (rep w) ec [] [] out lab res) none
      (bk inp [] ec [] [] (rep (max 1 w) ++ out) lab res) (w + 2) := by
  cases w with
  | zero =>
      refine (RIn.step ?_).mono (by omega)
      intro σ
      simp [TM2.step, TM2.stepAux, program]
  | succ w =>
      have h := fin4_run (M := M) inp ec lab res w (true :: out)
      rw [show rep w ++ true :: out = rep (max 1 (w + 1)) ++ out by
        rw [show max 1 (w + 1) = w + 1 by omega]; simp [List.replicate_succ']] at h
      refine (RIn.cons ?_ h).mono (by omega)
      intro σ
      simp [TM2.step, TM2.stepAux, program, List.replicate_succ]

end Final

end Paper2.YaoCloneMachine
