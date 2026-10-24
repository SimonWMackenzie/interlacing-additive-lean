import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
# A generic one-pass bit transducer with a unary counter stack (lane `owner:a-front-1`)

Private lane module, 27 September 2026. Support for WP-U18a (iii), (iv) and the D-A3 projection
machine (`AUTHOR_DECISIONS_2026-09-27.md`, D-A3: "a projection machine from `outputBits`").

A `Spec σ` is a finite-state transducer over the bit alphabet with one unary counter:

* on each input bit `b` in state `s` it emits the bounded word `emit s b`, then performs the
  counter operation `op s b` (`keep`; `inc`: push `incBy` marks; `dec`: pop one mark, and the
  next state is told whether a mark was present), and moves to `step s b present`;
* at the end of the input it emits `fin s`.

`machine P s₀` is ONE fixed `BitMachine.Machine` (`ofFinite`, four Boolean stacks: input,
output, buffer, counter; control `σ × Option Bool × Option Bool`). It is started from
`Machine.init` (no inserted state): every emitted bit is physically pushed onto the buffer, and
the buffer is physically moved onto the (initially empty) output stack at the end.
`machine_outputs` is the exact output with the exact transition count
`|w| + |out| + 2`.

No ledger row is closed by this module.
-/

namespace AFront.Transducer

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Op
  | keep | inc | dec
  deriving DecidableEq

/-- A one-pass bit transducer with a unary counter. -/
structure Spec (σ : Type) where
  step : σ → Bool → Bool → σ
  emit : σ → Bool → List Bool
  op : σ → Bool → Op
  fin : σ → List Bool
  incBy : ℕ
  bound : ℕ
  emit_le : ∀ s b, (emit s b).length ≤ bound
  fin_le : ∀ s, (fin s).length ≤ bound

variable {σ : Type} (P : Spec σ)

/-- One transition of the abstract transducer: next state and next counter value. -/
def Spec.next (s : σ) (c : ℕ) (b : Bool) : σ × ℕ :=
  match P.op s b with
  | .keep => (P.step s b true, c)
  | .inc => (P.step s b true, c + P.incBy)
  | .dec => if c = 0 then (P.step s b false, 0) else (P.step s b true, c - 1)

/-- The emitted stream before the final emission. -/
def Spec.stream : σ → ℕ → List Bool → List Bool
  | _, _, [] => []
  | s, c, b :: w => P.emit s b ++ Spec.stream (P.next s c b).1 (P.next s c b).2 w

/-- The state and counter after reading a word. -/
def Spec.last : σ → ℕ → List Bool → σ × ℕ
  | s, c, [] => (s, c)
  | s, c, b :: w => Spec.last (P.next s c b).1 (P.next s c b).2 w

/-- The full output of the transducer. -/
def Spec.out (s : σ) (c : ℕ) (w : List Bool) : List Bool :=
  P.stream s c w ++ P.fin (P.last s c w).1

theorem Spec.out_nil (s : σ) (c : ℕ) : P.out s c [] = P.fin s := by
  simp [Spec.out, Spec.stream, Spec.last]

theorem Spec.out_cons (s : σ) (c : ℕ) (b : Bool) (w : List Bool) :
    P.out s c (b :: w) = P.emit s b ++ P.out (P.next s c b).1 (P.next s c b).2 w := by
  simp [Spec.out, Spec.stream, Spec.last, List.append_assoc]

theorem Spec.stream_length (s : σ) (c : ℕ) (w : List Bool) :
    (P.stream s c w).length ≤ P.bound * w.length := by
  induction w generalizing s c with
  | nil => simp [Spec.stream]
  | cons b w ih =>
      simp only [Spec.stream, List.length_append, List.length_cons]
      have h1 := P.emit_le s b
      have h2 := ih (P.next s c b).1 (P.next s c b).2
      rw [Nat.mul_succ]
      omega

theorem Spec.out_length (s : σ) (c : ℕ) (w : List Bool) :
    (P.out s c w).length ≤ P.bound * (w.length + 1) := by
  simp only [Spec.out, List.length_append]
  have h1 := P.stream_length s c w
  have h2 := P.fin_le (P.last s c w).1
  rw [Nat.mul_succ]
  omega

/-! ## The physical machine -/

abbrev Stack := Fin 4

inductive Label
  | scan | move
  deriving DecidableEq, Fintype

abbrev Ctl (σ : Type) := σ × Option Bool × Option Bool

abbrev Stmt (σ : Type) := TM2.Stmt (fun _ : Stack => Bool) Label (Ctl σ)

/-- Push the entries `i, i+1, …, i+n-1` (those that exist) of a control-dependent word. -/
def pushList (k : Stack) (e : Ctl σ → List Bool) : ℕ → ℕ → Stmt σ → Stmt σ
  | _, 0, q => q
  | i, n + 1, q => .branch (fun v => decide (i < (e v).length))
      (.push k (fun v => (e v).getD i false) (pushList k e (i + 1) n q))
      (pushList k e (i + 1) n q)

/-- Push `m` counter marks. -/
def pushN (k : Stack) : ℕ → Stmt σ → Stmt σ
  | 0, q => q
  | m + 1, q => .push k (fun _ => true) (pushN k m q)

theorem stepAux_pushN (k : Stack) (m : ℕ) (q : Stmt σ) (v : Ctl σ) (S : Stack → List Bool) :
    TM2.stepAux (pushN k m q) v S =
      TM2.stepAux q v (Function.update S k (List.replicate m true ++ S k)) := by
  induction m generalizing S with
  | zero => simp [pushN]
  | succ m ih =>
      simp only [pushN, TM2.stepAux]
      rw [ih]
      congr 1
      simp [Function.update_idem, List.replicate_succ']

theorem stepAux_pushList (k : Stack) (e : Ctl σ → List Bool) (i n : ℕ) (q : Stmt σ)
    (v : Ctl σ) (S : Stack → List Bool) :
    TM2.stepAux (pushList k e i n q) v S =
      TM2.stepAux q v (Function.update S k
        ((((e v).drop i).take n).reverse ++ S k)) := by
  induction n generalizing i S with
  | zero => simp [pushList]
  | succ n ih =>
      simp only [pushList, TM2.stepAux]
      by_cases hi : i < (e v).length
      · simp only [hi, decide_true, cond_true]
        rw [ih]
        congr 1
        rw [Function.update_idem]
        congr 1
        rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, List.reverse_cons,
          List.append_assoc]
        simp [Function.update_self, List.getElem?_eq_getElem hi]
      · simp only [hi, decide_false, cond_false]
        rw [ih]
        have h1 : (e v).drop i = [] := List.drop_eq_nil_of_le (by omega)
        have h2 : (e v).drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
        simp [h1, h2]

theorem pushList_all (k : Stack) (e : Ctl σ → List Bool) (n : ℕ) (q : Stmt σ)
    (v : Ctl σ) (S : Stack → List Bool) (hn : (e v).length ≤ n) :
    TM2.stepAux (pushList k e 0 n q) v S =
      TM2.stepAux q v (Function.update S k ((e v).reverse ++ S k)) := by
  rw [stepAux_pushList]
  simp [List.take_of_length_le hn]

def bit (v : Ctl σ) : Bool := v.2.1.getD false

def opStmt : Stmt σ :=
  .branch (fun v => decide (P.op v.1 (bit v) = .keep))
    (.load (fun v => (P.step v.1 (bit v) true, v.2)) (.goto fun _ => .scan))
    (.branch (fun v => decide (P.op v.1 (bit v) = .inc))
      (pushN 3 P.incBy (.load (fun v => (P.step v.1 (bit v) true, v.2)) (.goto fun _ => .scan)))
      (.pop 3 (fun v c => (v.1, v.2.1, c))
        (.load (fun v => (P.step v.1 (bit v) v.2.2.isSome, v.2)) (.goto fun _ => .scan))))

def program : Label → Stmt σ
  | .scan => .pop 0 (fun v b => (v.1, b, v.2.2))
      (.branch (fun v => v.2.1.isSome)
        (pushList 2 (fun v => P.emit v.1 (bit v)) 0 P.bound (opStmt P))
        (pushList 2 (fun v => P.fin v.1) 0 P.bound (.goto fun _ => .move)))
  | .move => .pop 2 (fun v b => (v.1, b, v.2.2))
      (.branch (fun v => v.2.1.isSome)
        (.push 1 (fun v => bit v) (.goto fun _ => .move)) .halt)

/-- THE fixed machine of a transducer spec with start state `s₀`. -/
noncomputable def machine [Fintype σ] [DecidableEq σ] (s₀ : σ) : BitMachine.Machine :=
  ofFinite (0 : Stack) 1 Label.scan ((s₀, none, none) : Ctl σ) (program P)

abbrev Config (σ : Type) := TM2.Cfg (fun _ : Stack => Bool) Label (Ctl σ)

/-- The four-stack bank. -/
def bank (a b c d : List Bool) : Stack → List Bool := ![a, b, c, d]

theorem update0 (a b c d x : List Bool) : Function.update (bank a b c d) 0 x = bank x b c d := by
  funext k; fin_cases k <;> rfl
theorem update1 (a b c d x : List Bool) : Function.update (bank a b c d) 1 x = bank a x c d := by
  funext k; fin_cases k <;> rfl
theorem update2 (a b c d x : List Bool) : Function.update (bank a b c d) 2 x = bank a b x d := by
  funext k; fin_cases k <;> rfl
theorem update3 (a b c d x : List Bool) : Function.update (bank a b c d) 3 x = bank a b c x := by
  funext k; fin_cases k <;> rfl

@[simp] theorem bank0 (a b c d : List Bool) : bank a b c d 0 = a := rfl
@[simp] theorem bank1 (a b c d : List Bool) : bank a b c d 1 = b := rfl
@[simp] theorem bank2 (a b c d : List Bool) : bank a b c d 2 = c := rfl
@[simp] theorem bank3 (a b c d : List Bool) : bank a b c d 3 = d := rfl

/-- One input bit: exactly one transition. -/
theorem scan_step (s : σ) (c : ℕ) (o₁ o₂ : Option Bool) (b : Bool) (w buf : List Bool) :
    ∃ o₂' : Option Bool,
      advance (program P) (⟨some .scan, (s, o₁, o₂),
          bank (b :: w) [] buf (List.replicate c true)⟩ : Config σ) =
        ⟨some .scan, ((P.next s c b).1, some b, o₂'),
          bank w [] ((P.emit s b).reverse ++ buf) (List.replicate (P.next s c b).2 true)⟩ := by
  have hle := P.emit_le s b
  cases hop : P.op s b with
  | keep =>
      refine ⟨o₂, ?_⟩
      simp only [advance, TM2.step, program, TM2.stepAux, bank0, List.head?_cons,
        List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
      rw [update0, pushList_all _ _ _ _ _ _ (by simpa [bit] using hle)]
      simp [opStmt, TM2.stepAux, bit, hop, Spec.next, update2]
  | inc =>
      refine ⟨o₂, ?_⟩
      simp only [advance, TM2.step, program, TM2.stepAux, bank0, List.head?_cons,
        List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
      rw [update0, pushList_all _ _ _ _ _ _ (by simpa [bit] using hle)]
      simp only [opStmt, TM2.stepAux, bit, hop, Option.getD_some, update2, reduceCtorEq,
        decide_false, decide_true, cond_false, cond_true]
      rw [stepAux_pushN]
      simp [TM2.stepAux, Spec.next, hop, update3, List.replicate_append_replicate, Nat.add_comm]
  | dec =>
      cases c with
      | zero =>
          refine ⟨none, ?_⟩
          simp only [advance, TM2.step, program, TM2.stepAux, bank0, List.head?_cons,
            List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
          rw [update0, pushList_all _ _ _ _ _ _ (by simpa [bit] using hle)]
          simp [opStmt, TM2.stepAux, bit, hop, Spec.next, update2, update3]
      | succ c =>
          refine ⟨some true, ?_⟩
          simp only [advance, TM2.step, program, TM2.stepAux, bank0, List.head?_cons,
            List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
          rw [update0, pushList_all _ _ _ _ _ _ (by simpa [bit] using hle)]
          simp [opStmt, TM2.stepAux, bit, hop, Spec.next, update2, update3,
            List.replicate_succ]

/-- The scan loop: exactly `|w|` transitions. -/
theorem scan_run (w : List Bool) (s : σ) (c : ℕ) (o₁ o₂ : Option Bool) (buf : List Bool) :
    ∃ o₁' o₂' : Option Bool,
      ((advance (program P))^[w.length]) (⟨some .scan, (s, o₁, o₂),
          bank w [] buf (List.replicate c true)⟩ : Config σ) =
        ⟨some .scan, ((P.last s c w).1, o₁', o₂'),
          bank [] [] ((P.stream s c w).reverse ++ buf)
            (List.replicate (P.last s c w).2 true)⟩ := by
  induction w generalizing s c o₁ o₂ buf with
  | nil => exact ⟨o₁, o₂, by simp [Spec.last, Spec.stream]⟩
  | cons b w ih =>
      obtain ⟨o₂', h1⟩ := scan_step P s c o₁ o₂ b w buf
      obtain ⟨o₁'', o₂'', h2⟩ := ih (P.next s c b).1 (P.next s c b).2 (some b) o₂'
        ((P.emit s b).reverse ++ buf)
      refine ⟨o₁'', o₂'', ?_⟩
      rw [List.length_cons, Function.iterate_succ_apply, h1, h2]
      simp [Spec.last, Spec.stream, List.reverse_append, List.append_assoc]

/-- End of input: one transition (final emission). -/
theorem scan_end (s : σ) (o₁ o₂ : Option Bool) (buf cnt : List Bool) :
    advance (program P) (⟨some .scan, (s, o₁, o₂), bank [] [] buf cnt⟩ : Config σ) =
      ⟨some .move, (s, none, o₂), bank [] [] ((P.fin s).reverse ++ buf) cnt⟩ := by
  have hle := P.fin_le s
  simp only [advance, TM2.step, program, TM2.stepAux, bank0, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false]
  rw [update0, pushList_all _ _ _ _ _ _ (by simpa using hle)]
  simp [TM2.stepAux, update2]

/-- The move loop: exactly `|buf| + 1` transitions. -/
theorem move_run (buf out cnt : List Bool) (v : Ctl σ) :
    ∃ v' : Ctl σ, ((advance (program P))^[buf.length + 1])
        (⟨some .move, v, bank [] out buf cnt⟩ : Config σ) =
      ⟨none, v', bank [] (buf.reverse ++ out) [] cnt⟩ := by
  induction buf generalizing v out with
  | nil =>
      refine ⟨(v.1, none, v.2.2), ?_⟩
      simp [advance, TM2.step, program, TM2.stepAux, update2]
  | cons b bs ih =>
      have hstep : advance (program P) (⟨some .move, v, bank [] out (b :: bs) cnt⟩ : Config σ) =
          ⟨some .move, (v.1, some b, v.2.2), bank [] (b :: out) bs cnt⟩ := by
        simp [advance, TM2.step, program, TM2.stepAux, update1, update2, bit]
      obtain ⟨v', hv⟩ := ih (b :: out) (v.1, some b, v.2.2)
      refine ⟨v', ?_⟩
      rw [List.length_cons, Function.iterate_succ_apply, hstep, hv]
      simp [List.append_assoc]

theorem rawInit_eq [Fintype σ] [DecidableEq σ] (s₀ : σ) (w : List Bool) :
    (rawInit (0 : Stack) Label.scan ((s₀, none, none) : Ctl σ) w) =
      (⟨some .scan, (s₀, none, none), bank w [] [] (List.replicate 0 true)⟩ : Config σ) := by
  simp only [rawInit]
  congr 1
  funext k; fin_cases k <;> rfl

/-- **The exact run.** On every word `w`, the fixed machine prints exactly `P.out s₀ 0 w`,
halting after exactly `|w| + |P.out s₀ 0 w| + 2` transitions. -/
theorem machine_outputs [Fintype σ] [DecidableEq σ] (s₀ : σ) (w : List Bool) :
    (machine P s₀).OutputsWithin w (P.out s₀ 0 w) (w.length + (P.out s₀ 0 w).length + 2) := by
  obtain ⟨o₁, o₂, hscan⟩ := scan_run P w s₀ 0 none none []
  have hend := scan_end P (P.last s₀ 0 w).1 o₁ o₂ ((P.stream s₀ 0 w).reverse ++ [])
    (List.replicate (P.last s₀ 0 w).2 true)
  set buf := (P.fin (P.last s₀ 0 w).1).reverse ++ ((P.stream s₀ 0 w).reverse ++ [])
  obtain ⟨v', hmove⟩ := move_run P buf [] (List.replicate (P.last s₀ 0 w).2 true)
    ((P.last s₀ 0 w).1, none, o₂)
  have hbuf : buf.reverse = P.out s₀ 0 w := by
    simp [buf, Spec.out]
  have hlen : buf.length = (P.out s₀ 0 w).length := by
    rw [← hbuf, List.length_reverse]
  have hrun : ((advance (program P))^[(buf.length + 1) + 1 + w.length])
      (rawInit (0 : Stack) Label.scan ((s₀, none, none) : Ctl σ) w) =
      ⟨none, v', bank [] (buf.reverse ++ []) [] (List.replicate (P.last s₀ 0 w).2 true)⟩ := by
    rw [rawInit_eq, Function.iterate_add_apply, Function.iterate_add_apply, hscan,
      Function.iterate_one, hend, hmove]
  apply outputsWithin_of_raw_run (0 : Stack) 1 Label.scan ((s₀, none, none) : Ctl σ)
    (program P) w (P.out s₀ 0 w) ((buf.length + 1) + 1 + w.length)
    (w.length + (P.out s₀ 0 w).length + 2) (by omega)
  · rw [hrun]
  · rw [hrun]; simp [hbuf]

/-- The same run with the linear clock `(bound + 2)·(|w| + 1)`. -/
theorem machine_outputs_linear [Fintype σ] [DecidableEq σ] (s₀ : σ) (w : List Bool) :
    (machine P s₀).OutputsWithin w (P.out s₀ 0 w) ((P.bound + 2) * (w.length + 1)) := by
  apply BitMachine.outputsWithin_mono _ (machine_outputs P s₀ w)
  have h := P.out_length s₀ 0 w
  nlinarith

theorem machine_computes [Fintype σ] [DecidableEq σ] (s₀ : σ) :
    (machine P s₀).ComputesWithin (P.out s₀ 0) (fun n => (P.bound + 2) * (n + 1)) :=
  fun w => machine_outputs_linear P s₀ w

end AFront.Transducer
