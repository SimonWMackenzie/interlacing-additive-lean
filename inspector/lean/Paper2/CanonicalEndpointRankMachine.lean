import EthInapproximability.CurrentPaper.BitMachineClearBank
import Mathlib.Tactic

/-! A fixed four-stack TM2 controller for already-selected, terminated unary
endpoint and item words. Indexed-edge lookup and coordinate decoding are not
part of this machine. -/

namespace Paper2.CanonicalEndpointRankMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Kind where
  | edge | leftIncidence | rightIncidence
  deriving DecidableEq, Fintype, Repr

inductive ItemKind where
  | vertex | auxiliary
  deriving DecidableEq, Fintype, Repr

inductive Cmp where
  | lt | eq | gt
  deriving DecidableEq, Fintype, Repr

inductive Label where
  | scan | emit | done
  deriving DecidableEq, Fintype, Repr

structure Control where
  kind : Kind
  item : ItemKind
  uv : Cmp := .eq
  xu : Cmp := .eq
  xv : Cmp := .eq
  readU : Option Bool := none
  readV : Option Bool := none
  readX : Option Bool := none
  active : Bool := false
  deriving DecidableEq, Repr

abbrev Config := TM2.Cfg (fun _ : Fin 4 => Bool) Label Control

def contents (u v x out : List Bool) : Fin 4 → List Bool := ![u, v, x, out]

def cfg (l : Option Label) (q : Control)
    (u v x out : List Bool) : Config := ⟨l, q, contents u v x out⟩

def unaryWord (k : Nat) : List Bool := List.replicate k true ++ [false]

def initial (kind : Kind) (item : ItemKind) (u v x : Nat) : Config :=
  cfg (some .scan) {kind, item} (unaryWord u) (unaryWord v) (unaryWord x) []

def isTrue (b : Option Bool) : Bool := b == some true

def refineCmp (r : Cmp) (a b : Option Bool) : Cmp :=
  if r != .eq then r
  else if isTrue a then
    if isTrue b then .eq else .gt
  else if isTrue b then .lt else .eq

def cmpNat (a b : Nat) : Cmp :=
  if a < b then .lt else if b < a then .gt else .eq

def mergeCmp (old : Cmp) (a b : Nat) : Cmp :=
  if old == .eq then cmpNat a b else old

private theorem mergeCmp_step (old : Cmp) (a b : Nat)
    (ha hb : Option Bool)
    (hha : isTrue ha = decide (0 < a))
    (hhb : isTrue hb = decide (0 < b)) :
    mergeCmp (refineCmp old ha hb) (a - 1) (b - 1) =
      mergeCmp old a b := by
  cases old <;> cases a <;> cases b <;>
    simp_all [mergeCmp, refineCmp, cmpNat, isTrue]

def word (n : Nat) (terminator : Bool) : List Bool :=
  List.replicate n true ++ if terminator then [false] else []

private theorem word_zero (terminator : Bool) :
    word 0 terminator = if terminator then [false] else [] := by
  simp [word]

private theorem word_succ (n : Nat) (terminator : Bool) :
    word (n + 1) terminator = true :: word n terminator := by
  simp [word, List.replicate_succ]

private theorem unaryWord_eq_word (n : Nat) :
    unaryWord n = word n true := by
  simp [unaryWord, word]

def scanUpdate (q : Control) : Control :=
  {q with
    uv := refineCmp q.uv q.readU q.readV
    xu := refineCmp q.xu q.readX q.readU
    xv := refineCmp q.xv q.readX q.readV}

def scanMore (q : Control) : Bool :=
  isTrue q.readU || isTrue q.readV || isTrue q.readX

def activeOf (q : Control) : Bool :=
  match q.item with
  | .auxiliary => true
  | .vertex =>
      match q.kind with
      | .edge => q.xu == .eq || q.xv == .eq
      | .leftIncidence => q.xu == .eq
      | .rightIncidence => q.xv == .eq

def delta (q : Control) : Fin 3 :=
  match q.item with
  | .auxiliary =>
      match q.kind with
      | .edge => if q.uv == .eq then 1 else 2
      | .leftIncidence | .rightIncidence => 1
  | .vertex =>
      match q.kind with
      | .edge =>
          if (q.xu == .eq && q.uv == .gt) ||
              (q.xv == .eq && q.uv == .lt) then 1 else 0
      | .leftIncidence | .rightIncidence => 0

def finalControl (q : Control) : Control :=
  {kind := .edge, item := .vertex, active := activeOf q}

def program : Label → TM2.Stmt (fun _ : Fin 4 => Bool) Label Control
  | .scan =>
      pop 0 (fun q b => {q with readU := b})
        (pop 1 (fun q b => {q with readV := b})
          (pop 2 (fun q b => {q with readX := b})
            (load scanUpdate
              (branch scanMore
                (branch (fun q => q.item == .auxiliary && isTrue q.readX)
                  (push 3 (fun _ => true) (goto (fun _ => .scan)))
                  (goto (fun _ => .scan)))
                (goto (fun _ => .emit))))))
  | .emit =>
      branch (fun q => delta q == 2)
        (push 3 (fun _ => true)
          (push 3 (fun _ => true)
            (load finalControl (goto (fun _ => .done)))))
        (branch (fun q => delta q == 1)
          (push 3 (fun _ => true)
            (load finalControl (goto (fun _ => .done))))
          (load finalControl (goto (fun _ => .done))))
  | .done => .halt

def semanticActive (kind : Kind) (item : ItemKind) (u v x : Nat) : Bool :=
  match item with
  | .auxiliary => true
  | .vertex =>
      match kind with
      | .edge => x == u || x == v
      | .leftIncidence => x == u
      | .rightIncidence => x == v

def semanticRank (kind : Kind) (item : ItemKind) (u v x : Nat) : Nat :=
  match item with
  | .auxiliary =>
      x + (match kind with
        | .edge => if u = v then 1 else 2
        | .leftIncidence | .rightIncidence => 1)
  | .vertex =>
      match kind with
      | .edge => if (x = u && v < u) || (x = v && u < v) then 1 else 0
      | .leftIncidence | .rightIncidence => 0

def output (kind : Kind) (item : ItemKind) (u v x : Nat) : Config :=
  cfg none (Control.mk .edge .vertex .eq .eq .eq none none none
    (semanticActive kind item u v x))
    [] [] [] (List.replicate (semanticRank kind item u v x) true)

private def scanNext (q : Control) (u v x : List Bool) : Control :=
  scanUpdate {q with readU := u.head?, readV := v.head?, readX := x.head?}

private def scanOutput (q : Control) (u v x out : List Bool) : List Bool :=
  if scanMore (scanNext q u v x) &&
      q.item == .auxiliary && isTrue x.head? then true :: out else out

/-! ### Bank bookkeeping for the fixed four stacks -/

private theorem contents_zero (u v x out : List Bool) :
    contents u v x out 0 = u := rfl

private theorem contents_one (u v x out : List Bool) :
    contents u v x out 1 = v := rfl

private theorem contents_two (u v x out : List Bool) :
    contents u v x out 2 = x := rfl

private theorem contents_three (u v x out : List Bool) :
    contents u v x out 3 = out := rfl

private theorem update_zero (u v x out w : List Bool) :
    Function.update (contents u v x out) 0 w = contents w v x out := by
  funext j; fin_cases j <;> rfl

private theorem update_one (u v x out w : List Bool) :
    Function.update (contents u v x out) 1 w = contents u w x out := by
  funext j; fin_cases j <;> rfl

private theorem update_two (u v x out w : List Bool) :
    Function.update (contents u v x out) 2 w = contents u v w out := by
  funext j; fin_cases j <;> rfl

private theorem update_three (u v x out w : List Bool) :
    Function.update (contents u v x out) 3 w = contents u v x w := by
  funext j; fin_cases j <;> rfl

private theorem vertex_beq_auxiliary :
    (ItemKind.vertex == ItemKind.auxiliary) = false := rfl

private theorem auxiliary_beq_auxiliary :
    (ItemKind.auxiliary == ItemKind.auxiliary) = true := rfl

/-! ### One scan transition -/

private theorem advance_scan (q : Control) (u v x out : List Bool) :
    advance program (cfg (some .scan) q u v x out) =
      cfg (some (if scanMore (scanNext q u v x) then .scan else .emit))
        (scanNext q u v x) u.tail v.tail x.tail (scanOutput q u v x out) := by
  rcases q with ⟨kind, item, uv, xu, xv, readU, readV, readX, active⟩
  cases item <;>
  rcases u with _ | ⟨bu, us⟩ <;>
  rcases v with _ | ⟨bv, vs⟩ <;>
  rcases x with _ | ⟨bx, xs⟩ <;>
  (try cases bu) <;> (try cases bv) <;> (try cases bx) <;>
  simp only [advance, TM2.step, Option.getD_some, TM2.stepAux, program, cfg,
    contents_zero, contents_one, contents_two, contents_three,
    update_zero, update_one, update_two, update_three,
    scanNext, scanOutput, scanMore, scanUpdate, isTrue,
    vertex_beq_auxiliary, auxiliary_beq_auxiliary,
    List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons] <;>
  rfl

/-! ### Word reads -/

private theorem word_head_isTrue (n : Nat) (t : Bool) :
    isTrue (word n t).head? = decide (0 < n) := by
  cases n <;> cases t <;> simp [word, isTrue, List.replicate_succ]

private theorem word_tail (n : Nat) (t : Bool) :
    (word n t).tail = word (n - 1) (t && decide (0 < n)) := by
  cases n <;> cases t <;> simp [word, List.replicate_succ]

private theorem word_zero_false : word 0 false = [] := rfl

private theorem scanMore_scanNext (q : Control) (u v x : List Bool) :
    scanMore (scanNext q u v x) =
      (isTrue u.head? || isTrue v.head? || isTrue x.head?) := rfl

private theorem mergeCmp_zero (r : Cmp) : mergeCmp r 0 0 = r := by
  cases r <;> rfl

/-! ### The scan loop -/

private theorem scan_run (n : Nat) :
    ∀ (q : Control) (a b c : Nat) (ta tb tc : Bool) (out : List Bool),
      max a (max b c) = n →
      ∃ q' : Control,
        (advance program)^[n + 1]
            (cfg (some .scan) q (word a ta) (word b tb) (word c tc) out) =
          cfg (some .emit) q' [] [] []
            (List.replicate (if q.item = .auxiliary then c else 0) true ++ out) ∧
        q'.kind = q.kind ∧ q'.item = q.item ∧
        q'.uv = mergeCmp q.uv a b ∧ q'.xu = mergeCmp q.xu c a ∧
        q'.xv = mergeCmp q.xv c b := by
  induction n with
  | zero =>
      intro q a b c ta tb tc out h
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      have hc : c = 0 := by omega
      subst ha hb hc
      have hm : scanMore (scanNext q (word 0 ta) (word 0 tb) (word 0 tc)) = false := by
        rw [scanMore_scanNext, word_head_isTrue, word_head_isTrue, word_head_isTrue]
        rfl
      refine ⟨scanNext q (word 0 ta) (word 0 tb) (word 0 tc), ?_, rfl, rfl, ?_, ?_, ?_⟩
      · rw [Function.iterate_one, advance_scan, hm]
        have hout : scanOutput q (word 0 ta) (word 0 tb) (word 0 tc) out = out := by
          simp [scanOutput, hm]
        rw [hout, word_tail, word_tail, word_tail]
        simp [word_zero_false]
      · have hs := mergeCmp_step q.uv 0 0 _ _ (word_head_isTrue 0 ta) (word_head_isTrue 0 tb)
        rw [mergeCmp_zero] at hs
        simpa [mergeCmp_zero] using hs
      · have hs := mergeCmp_step q.xu 0 0 _ _ (word_head_isTrue 0 tc) (word_head_isTrue 0 ta)
        rw [mergeCmp_zero] at hs
        simpa [mergeCmp_zero] using hs
      · have hs := mergeCmp_step q.xv 0 0 _ _ (word_head_isTrue 0 tc) (word_head_isTrue 0 tb)
        rw [mergeCmp_zero] at hs
        simpa [mergeCmp_zero] using hs
  | succ n ih =>
      intro q a b c ta tb tc out h
      have hm : scanMore (scanNext q (word a ta) (word b tb) (word c tc)) = true := by
        rw [scanMore_scanNext, word_head_isTrue, word_head_isTrue, word_head_isTrue]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        omega
      obtain ⟨q', hrun, hk, hi, huv, hxu, hxv⟩ :=
        ih (scanNext q (word a ta) (word b tb) (word c tc)) (a - 1) (b - 1) (c - 1)
          (ta && decide (0 < a)) (tb && decide (0 < b)) (tc && decide (0 < c))
          (scanOutput q (word a ta) (word b tb) (word c tc) out) (by omega)
      refine ⟨q', ?_, hk, hi, ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, advance_scan, hm, if_pos rfl,
          word_tail, word_tail, word_tail, hrun]
        have hitem : (scanNext q (word a ta) (word b tb) (word c tc)).item = q.item := rfl
        rw [hitem]
        rcases q with ⟨kind, item, uv, xu, xv, readU, readV, readX, active⟩
        cases item
        · simp [scanOutput, hm]
        · cases c with
          | zero =>
              simp [scanOutput, hm, word_head_isTrue]
          | succ c =>
              simp [scanOutput, hm, word_head_isTrue, List.replicate_succ']
      · rw [huv]
        exact mergeCmp_step q.uv a b _ _ (word_head_isTrue a ta) (word_head_isTrue b tb)
      · rw [hxu]
        exact mergeCmp_step q.xu c a _ _ (word_head_isTrue c tc) (word_head_isTrue a ta)
      · rw [hxv]
        exact mergeCmp_step q.xv c b _ _ (word_head_isTrue c tc) (word_head_isTrue b tb)

/-! ### Emission and halting -/

private theorem advance_emit (q : Control) (u v x out : List Bool) :
    advance program (cfg (some .emit) q u v x out) =
      cfg (some .done) (finalControl q) u v x
        (List.replicate (delta q).val true ++ out) := by
  simp only [advance, TM2.step, Option.getD_some, TM2.stepAux, program, cfg,
    contents_three, update_three]
  generalize delta q = d
  fin_cases d <;> rfl

private theorem advance_done (q : Control) (u v x out : List Bool) :
    advance program (cfg (some .done) q u v x out) = cfg none q u v x out := rfl

/-- A halted configuration is fixed by `advance`. -/
theorem advance_halted (q : Control) (u v x out : List Bool) :
    advance program (cfg none q u v x out) = cfg none q u v x out := rfl

/-! ### Comparison semantics -/

private theorem cmpNat_beq_eq (a b : Nat) :
    (cmpNat a b == Cmp.eq) = decide (a = b) := by
  unfold cmpNat
  by_cases h1 : a < b
  · have : a ≠ b := by omega
    simp [h1, this]
  · by_cases h2 : b < a
    · have : a ≠ b := by omega
      simp [h1, h2, this]
    · have : a = b := by omega
      subst this
      simp

private theorem cmpNat_beq_gt (a b : Nat) :
    (cmpNat a b == Cmp.gt) = decide (b < a) := by
  unfold cmpNat
  by_cases h1 : a < b
  · have : ¬ b < a := by omega
    simp [h1, this]
  · by_cases h2 : b < a
    · simp [h1, h2]
    · simp [h1, h2]

private theorem cmpNat_beq_lt (a b : Nat) :
    (cmpNat a b == Cmp.lt) = decide (a < b) := by
  unfold cmpNat
  by_cases h1 : a < b
  · simp [h1]
  · by_cases h2 : b < a
    · simp [h1, h2]
    · simp [h1, h2]

private theorem mergeCmp_eq (a b : Nat) : mergeCmp Cmp.eq a b = cmpNat a b := rfl

private theorem nat_beq_decide (a b : Nat) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

private theorem activeOf_final (kind : Kind) (item : ItemKind) (u v x : Nat)
    (q' : Control) (hk : q'.kind = kind) (hi : q'.item = item)
    (hxu : q'.xu = cmpNat x u) (hxv : q'.xv = cmpNat x v) :
    activeOf q' = semanticActive kind item u v x := by
  unfold activeOf semanticActive
  rw [hk, hi, hxu, hxv]
  cases item <;> cases kind <;>
    simp only [cmpNat_beq_eq, nat_beq_decide]

private theorem delta_final (kind : Kind) (item : ItemKind) (u v x : Nat)
    (q' : Control) (hk : q'.kind = kind) (hi : q'.item = item)
    (huv : q'.uv = cmpNat u v)
    (hxu : q'.xu = cmpNat x u) (hxv : q'.xv = cmpNat x v) :
    (delta q').val + (if item = .auxiliary then x else 0) =
      semanticRank kind item u v x := by
  unfold delta semanticRank
  rw [hk, hi, huv, hxu, hxv]
  cases item <;> cases kind <;>
    simp only [cmpNat_beq_eq, cmpNat_beq_gt, cmpNat_beq_lt] <;>
    split_ifs <;> simp_all <;> omega

/-! ### Whole-bank run -/

/-- Exact whole-bank run with an arbitrary pre-existing output suffix: after
exactly `max u (max v x) + 3` transitions the three scratch operand stacks are
empty, the finite control is reset except for the separate activity bit, and
`semanticRank` true cells have been pushed onto the output stack. -/
theorem run_exact_out (kind : Kind) (item : ItemKind) (u v x : Nat)
    (out : List Bool) :
    (advance program)^[max u (max v x) + 3]
        (cfg (some .scan) {kind, item} (unaryWord u) (unaryWord v)
          (unaryWord x) out) =
      cfg none (Control.mk .edge .vertex .eq .eq .eq none none none
          (semanticActive kind item u v x))
        [] [] [] (List.replicate (semanticRank kind item u v x) true ++ out) := by
  obtain ⟨q', hrun, hk, hi, huv, hxu, hxv⟩ :=
    scan_run (max u (max v x)) {kind, item} u v x true true true out rfl
  have hsplit : max u (max v x) + 3 = 2 + (max u (max v x) + 1) := by omega
  rw [hsplit, Function.iterate_add_apply, unaryWord_eq_word, unaryWord_eq_word,
    unaryWord_eq_word, hrun, Function.iterate_succ_apply, Function.iterate_one,
    advance_emit, advance_done]
  have hA := activeOf_final kind item u v x q' hk hi (by rw [hxu]; rfl) (by rw [hxv]; rfl)
  have hR := delta_final kind item u v x q' hk hi (by rw [huv]; rfl)
    (by rw [hxu]; rfl) (by rw [hxv]; rfl)
  have hitem : ({kind, item} : Control).item = item := rfl
  rw [hitem, ← List.append_assoc, ← List.replicate_add, hR]
  unfold finalControl
  rw [hA]

/-- The fixed controller from its literal initial bank (empty output stack)
reaches the literal output configuration in exactly
`max u (max v x) + 3` transitions. -/
theorem run_exact (kind : Kind) (item : ItemKind) (u v x : Nat) :
    (advance program)^[max u (max v x) + 3] (initial kind item u v x) =
      output kind item u v x := by
  have h := run_exact_out kind item u v x []
  rw [List.append_nil] at h
  exact h

/-- The output configuration is halted: every later transition fixes it. -/
theorem output_fixed (kind : Kind) (item : ItemKind) (u v x : Nat) (t : Nat) :
    (advance program)^[t] (output kind item u v x) = output kind item u v x :=
  Function.iterate_fixed (advance_halted _ _ _ _ _) t

/-- Any clock at least `max u (max v x) + 3` gives the exact output. -/
theorem run_after (kind : Kind) (item : ItemKind) (u v x : Nat) (t : Nat)
    (ht : max u (max v x) + 3 ≤ t) :
    (advance program)^[t] (initial kind item u v x) = output kind item u v x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [Nat.add_comm, Function.iterate_add_apply, run_exact, output_fixed]

#print axioms run_exact_out
#print axioms run_exact
#print axioms output_fixed
#print axioms run_after

end Paper2.CanonicalEndpointRankMachine
