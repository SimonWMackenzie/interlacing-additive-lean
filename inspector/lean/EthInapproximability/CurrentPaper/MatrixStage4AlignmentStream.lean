import EthInapproximability.CurrentPaper.MatrixStage4FamilyAddress

/-!
# A fixed stream comparator for variable many unary selector words

Input: a preserved unary reference on stack 1 and a sequence of unary
candidate words on stack 0, each terminated by `false`. The program compares
one candidate at a time, restores the reference from scratch, and carries
only a single alignment bit in finite control. A later theorem must connect
its input serialization to the raw-column digits with charged preparation.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4AlignmentStream

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | start | scan | drain | restore
  deriving DecidableEq, Fintype

abbrev Control := Bool × Option Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 3 => Bool) Label Control

def initial : Control := (true,none,none)

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .start => peek 0 (fun v b => (v.1,v.2.1,b))
      (branch (fun v => v.2.2.isSome)
        (goto (fun _ => .scan))
        (load (fun v => (v.1,none,none)) halt))
  | .scan => pop 1 (fun v b => (v.1,b,v.2.2))
      (pop 0 (fun v b => (v.1,v.2.1,b))
        (branch (fun v => v.2.2.isSome)
          (branch (fun v => v.2.2.getD false)
            (branch (fun v => v.2.1.isSome)
              (push 2 (fun _ => true) (goto (fun _ => .scan)))
              (load (fun v => (false,v.2)) (goto (fun _ => .drain))))
            (branch (fun v => v.2.1.isSome)
              (push 2 (fun _ => true)
                (load (fun v => (false,v.2)) (goto (fun _ => .restore))))
              (goto (fun _ => .restore))))
          (load (fun _ => (false,none,none)) halt)))
  | .drain => pop 0 (fun v b => (v.1,v.2.1,b))
      (branch (fun v => v.2.2.isSome && v.2.2.getD false)
        (goto (fun _ => .drain)) (goto (fun _ => .restore)))
  | .restore => pop 2 (fun v b => (v.1,b,v.2.2))
      (branch (fun v => v.2.1.isSome)
        (push 1 (fun _ => true) (goto (fun _ => .restore)))
        (load (fun v => (v.1,none,none)) (goto (fun _ => .start))))

def cfg (l : Option Label) (v : Control)
    (stream reference scratch : List Bool) : Config :=
  ⟨l,v,![stream,reference,scratch]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

theorem run_succ (c : Config) (t : ℕ) :
    run (t+1) c = run t (advance program c) :=
  Function.iterate_succ_apply _ _ _

theorem start_cons (a : Bool) (stream reference scratch : List Bool)
    (u w : Option Bool) (b : Bool) :
    advance program (cfg (some .start) (a,u,w)
      (b::stream) reference scratch) =
      cfg (some .scan) (a,u,some b)
        (b::stream) reference scratch := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]

theorem start_nil (a : Bool) (reference scratch : List Bool)
    (u w : Option Bool) :
    advance program (cfg (some .start) (a,u,w) [] reference scratch) =
      cfg none (a,none,none) [] reference scratch := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]

theorem scan_both (a : Bool) (u w : Option Bool)
    (stream reference scratch : List Bool) :
    advance program (cfg (some .scan) (a,u,w)
      (true::stream) (true::reference) scratch) =
      cfg (some .scan) (a,some true,some true)
        stream reference (true::scratch) := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]
  funext k
  fin_cases k <;> rfl

theorem scan_equal_end (a : Bool) (u w : Option Bool)
    (stream scratch : List Bool) :
    advance program (cfg (some .scan) (a,u,w)
      (false::stream) [] scratch) =
      cfg (some .restore) (a,none,some false)
        stream [] scratch := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]
  funext k
  fin_cases k <;> rfl

theorem scan_short_end (a : Bool) (u w : Option Bool)
    (stream reference scratch : List Bool) :
    advance program (cfg (some .scan) (a,u,w)
      (false::stream) (true::reference) scratch) =
      cfg (some .restore) (false,some true,some false)
        stream reference (true::scratch) := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]
  funext k
  fin_cases k <;> rfl

theorem scan_long_end (a : Bool) (u w : Option Bool)
    (stream scratch : List Bool) :
    advance program (cfg (some .scan) (a,u,w)
      (true::stream) [] scratch) =
      cfg (some .drain) (false,none,some true)
        stream [] scratch := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]
  funext k
  fin_cases k <;> rfl

theorem drain_true (a : Bool) (u w : Option Bool)
    (stream reference scratch : List Bool) :
    advance program (cfg (some .drain) (a,u,w)
      (true::stream) reference scratch) =
      cfg (some .drain) (a,u,some true)
        stream reference scratch := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]
  funext k
  fin_cases k <;> rfl

theorem drain_false (a : Bool) (u w : Option Bool)
    (stream reference scratch : List Bool) :
    advance program (cfg (some .drain) (a,u,w)
      (false::stream) reference scratch) =
      cfg (some .restore) (a,u,some false)
        stream reference scratch := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]
  funext k
  fin_cases k <;> rfl

theorem restore_true (a : Bool) (u w : Option Bool)
    (stream reference scratch : List Bool) :
    advance program (cfg (some .restore) (a,u,w)
      stream reference (true::scratch)) =
      cfg (some .restore) (a,some true,w)
        stream (true::reference) scratch := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]
  funext k
  fin_cases k <;> rfl

theorem restore_nil (a : Bool) (u w : Option Bool)
    (stream reference : List Bool) :
    advance program (cfg (some .restore) (a,u,w)
      stream reference []) =
      cfg (some .start) (a,none,none)
        stream reference [] := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]

private theorem replicate_true_rotate (k : ℕ) (reference : List Bool) :
    List.replicate k true ++ true::reference =
      true :: (List.replicate k true ++ reference) := by
  induction k with
  | zero => rfl
  | succ j hj =>
    simpa only [List.replicate_succ, List.cons_append] using
      congrArg (List.cons true) hj

theorem restore_run (k : ℕ) (a : Bool) (u w : Option Bool)
    (stream reference : List Bool) :
    run (k+1) (cfg (some .restore) (a,u,w)
      stream reference (List.replicate k true)) =
      cfg (some .start) (a,none,none)
        stream (List.replicate k true ++ reference) [] := by
  induction k generalizing u w reference with
  | zero =>
    simpa only [List.replicate_zero,List.nil_append] using
      run_succ (cfg (some .restore) (a,u,w) stream reference []) 0 |>.trans
        (restore_nil a u w stream reference)
  | succ k ih =>
    rw [run_succ]
    simp only [List.replicate_succ, restore_true]
    simpa only [replicate_true_rotate] using
      ih (some true) w (true::reference)

theorem drain_run (k : ℕ) (a : Bool) (u w : Option Bool)
    (stream reference scratch : List Bool) :
    run (k+1) (cfg (some .drain) (a,u,w)
      (List.replicate k true ++ false::stream) reference scratch) =
      cfg (some .restore) (a,u,some false)
        stream reference scratch := by
  induction k generalizing w with
  | zero =>
    simpa only [List.replicate_zero,List.nil_append] using
      run_succ (cfg (some .drain) (a,u,w)
        (false::stream) reference scratch) 0 |>.trans
        (drain_false a u w stream reference scratch)
  | succ k ih =>
    rw [run_succ]
    simp only [List.replicate_succ, List.cons_append, drain_true]
    exact ih (some true)

theorem scan_match_run (k : ℕ) (a : Bool) (u w : Option Bool)
    (stream scratch : List Bool) :
    run (k+1) (cfg (some .scan) (a,u,w)
      (List.replicate k true ++ false::stream)
      (List.replicate k true) scratch) =
      cfg (some .restore) (a,none,some false)
        stream [] (List.replicate k true ++ scratch) := by
  induction k generalizing u w scratch with
  | zero =>
    simpa only [List.replicate_zero,List.nil_append] using
      run_succ (cfg (some .scan) (a,u,w) (false::stream) [] scratch) 0 |>.trans
        (scan_equal_end a u w stream scratch)
  | succ k ih =>
    rw [run_succ]
    simp only [List.replicate_succ,List.cons_append,scan_both]
    simpa only [replicate_true_rotate] using
      ih (some true) (some true) (true::scratch)

theorem scan_short_run (k : ℕ) (a : Bool) (u w : Option Bool)
    (stream reference scratch : List Bool) :
    run (k+1) (cfg (some .scan) (a,u,w)
      (List.replicate k true ++ false::stream)
      (List.replicate k true ++ true::reference) scratch) =
      cfg (some .restore) (false,some true,some false)
        stream reference (List.replicate (k+1) true ++ scratch) := by
  induction k generalizing u w scratch with
  | zero =>
    simpa only [List.replicate_zero,List.nil_append,List.replicate_one,
      List.singleton_append] using
      run_succ (cfg (some .scan) (a,u,w)
        (false::stream) (true::reference) scratch) 0 |>.trans
        (scan_short_end a u w stream reference scratch)
  | succ k ih =>
    rw [run_succ]
    simp only [List.replicate_succ,List.cons_append,scan_both]
    simpa only [replicate_true_rotate,List.replicate_succ,List.cons_append] using
      ih (some true) (some true) (true::scratch)

theorem scan_long_run (k : ℕ) (a : Bool) (u w : Option Bool)
    (stream scratch : List Bool) :
    run (k+1) (cfg (some .scan) (a,u,w)
      (List.replicate k true ++ true::stream)
      (List.replicate k true) scratch) =
      cfg (some .drain) (false,none,some true)
        stream [] (List.replicate k true ++ scratch) := by
  induction k generalizing u w scratch with
  | zero =>
    simpa only [List.replicate_zero,List.nil_append] using
      run_succ (cfg (some .scan) (a,u,w)
        (true::stream) [] scratch) 0 |>.trans
        (scan_long_end a u w stream scratch)
  | succ k ih =>
    rw [run_succ]
    simp only [List.replicate_succ,List.cons_append,scan_both]
    simpa only [replicate_true_rotate] using
      ih (some true) (some true) (true::scratch)

theorem start_word (k : ℕ) (a : Bool) (stream reference : List Bool) :
    advance program (cfg (some .start) (a,none,none)
      (List.replicate k true ++ false::stream) reference []) =
    cfg (some .scan) (a,none,some (k != 0))
      (List.replicate k true ++ false::stream) reference [] := by
  cases k with
  | zero => simpa using start_cons a stream reference [] none none false
  | succ k =>
    simpa only [List.replicate_succ,List.cons_append,ne_eq,
      Nat.succ_ne_zero,not_false_eq_true] using
      start_cons a (List.replicate k true ++ false::stream)
        reference [] none none true

theorem word_equal_run (k : ℕ) (a : Bool) (stream : List Bool) :
    run (1 + (k+1) + (k+1))
      (cfg (some .start) (a,none,none)
        (List.replicate k true ++ false::stream)
        (List.replicate k true) []) =
      cfg (some .start) (a,none,none)
        stream (List.replicate k true) [] := by
  have hs : run 1 (cfg (some .start) (a,none,none)
      (List.replicate k true ++ false::stream)
      (List.replicate k true) []) =
      cfg (some .scan) (a,none,some (k != 0))
        (List.replicate k true ++ false::stream)
        (List.replicate k true) [] := by
    simpa only [run,Function.iterate_one] using
      start_word k a stream (List.replicate k true)
  calc
    run (1 + (k+1) + (k+1))
        (cfg (some .start) (a,none,none)
          (List.replicate k true ++ false::stream)
          (List.replicate k true) [])
      = run ((k+1)+(k+1))
          (cfg (some .scan) (a,none,some (k != 0))
            (List.replicate k true ++ false::stream)
            (List.replicate k true) []) := by
          simpa only [Nat.add_assoc] using run_add hs ((k+1)+(k+1))
    _ = run (k+1) (cfg (some .restore) (a,none,some false)
          stream [] (List.replicate k true)) := by
        simpa only [List.append_nil] using
          run_add (scan_match_run k a none (some (k != 0)) stream []) (k+1)
    _ = _ := by simpa only [List.append_nil] using
      restore_run k a none (some false) stream []

theorem word_short_run (k : ℕ) (a : Bool)
    (stream reference : List Bool) :
    run (1 + (k+1) + (k+2))
      (cfg (some .start) (a,none,none)
        (List.replicate k true ++ false::stream)
        (List.replicate k true ++ true::reference) []) =
      cfg (some .start) (false,none,none)
        stream (List.replicate (k+1) true ++ reference) [] := by
  have hs : run 1 (cfg (some .start) (a,none,none)
      (List.replicate k true ++ false::stream)
      (List.replicate k true ++ true::reference) []) =
      cfg (some .scan) (a,none,some (k != 0))
        (List.replicate k true ++ false::stream)
        (List.replicate k true ++ true::reference) [] := by
    simpa only [run,Function.iterate_one] using
      start_word k a stream (List.replicate k true ++ true::reference)
  calc
    run (1 + (k+1) + (k+2))
        (cfg (some .start) (a,none,none)
          (List.replicate k true ++ false::stream)
          (List.replicate k true ++ true::reference) [])
      = run ((k+1)+(k+2))
          (cfg (some .scan) (a,none,some (k != 0))
            (List.replicate k true ++ false::stream)
            (List.replicate k true ++ true::reference) []) := by
        simpa only [Nat.add_assoc] using run_add hs ((k+1)+(k+2))
    _ = run (k+2) (cfg (some .restore) (false,some true,some false)
          stream reference (List.replicate (k+1) true)) := by
        simpa only [List.append_nil] using
          run_add (scan_short_run k a none (some (k != 0))
            stream reference []) (k+2)
    _ = _ := by simpa only [List.append_nil] using
      restore_run (k+1) false (some true) (some false) stream reference

theorem start_true_word (k : ℕ) (a : Bool)
    (stream reference : List Bool) :
    advance program (cfg (some .start) (a,none,none)
      (List.replicate k true ++ true::stream) reference []) =
    cfg (some .scan) (a,none,some true)
      (List.replicate k true ++ true::stream) reference [] := by
  cases k with
  | zero => simpa using start_cons a stream reference [] none none true
  | succ k =>
    simpa only [List.replicate_succ,List.cons_append] using
      start_cons a (List.replicate k true ++ true::stream)
        reference [] none none true

theorem word_long_run (k h : ℕ) (a : Bool) (stream : List Bool) :
    run (1 + (k+1) + (h+1) + (k+1))
      (cfg (some .start) (a,none,none)
        (List.replicate k true ++ true::
          (List.replicate h true ++ false::stream))
        (List.replicate k true) []) =
      cfg (some .start) (false,none,none)
        stream (List.replicate k true) [] := by
  have hs : run 1 (cfg (some .start) (a,none,none)
      (List.replicate k true ++ true::
        (List.replicate h true ++ false::stream))
      (List.replicate k true) []) =
      cfg (some .scan) (a,none,some true)
        (List.replicate k true ++ true::
          (List.replicate h true ++ false::stream))
        (List.replicate k true) [] := by
    simpa only [run,Function.iterate_one] using
      start_true_word k a (List.replicate h true ++ false::stream)
        (List.replicate k true)
  calc
    run (1 + (k+1) + (h+1) + (k+1))
        (cfg (some .start) (a,none,none)
          (List.replicate k true ++ true::
            (List.replicate h true ++ false::stream))
          (List.replicate k true) [])
      = run ((k+1)+(h+1)+(k+1))
          (cfg (some .scan) (a,none,some true)
            (List.replicate k true ++ true::
              (List.replicate h true ++ false::stream))
            (List.replicate k true) []) := by
        simpa only [Nat.add_assoc] using
          run_add hs ((k+1)+(h+1)+(k+1))
    _ = run ((h+1)+(k+1))
          (cfg (some .drain) (false,none,some true)
            (List.replicate h true ++ false::stream)
            [] (List.replicate k true)) := by
        simpa only [List.append_nil,Nat.add_assoc] using
          run_add (scan_long_run k a none (some true)
            (List.replicate h true ++ false::stream) []) ((h+1)+(k+1))
    _ = run (k+1) (cfg (some .restore) (false,none,some false)
          stream [] (List.replicate k true)) := by
        simpa only [Nat.add_assoc] using
          run_add (drain_run h false none (some true)
            stream [] (List.replicate k true)) (k+1)
    _ = _ := by simpa only [List.append_nil] using
      restore_run k false none (some false) stream []

theorem word_run (p q : ℕ) (a : Bool) (stream : List Bool) :
    ∃ t ≤ 4*(p+q+1), run t (cfg (some .start) (a,none,none)
      (List.replicate p true ++ false::stream)
      (List.replicate q true) []) =
      cfg (some .start) (a && decide (p=q),none,none)
        stream (List.replicate q true) [] := by
  rcases lt_trichotomy p q with hlt | heq | hgt
  · let h := q-p-1
    have hq : q = p+1+h := by dsimp [h]; omega
    refine ⟨1+(p+1)+(p+2), by omega, ?_⟩
    have hw := word_short_run p a stream (List.replicate h true)
    rw [hq]
    have hneq : p ≠ p+1+h := by omega
    simp only [hneq,decide_false,Bool.and_false]
    simpa only [List.replicate_add,List.replicate_succ,
      replicate_true_rotate] using hw
  · subst q
    refine ⟨1+(p+1)+(p+1), by omega, ?_⟩
    simpa using word_equal_run p a stream
  · let h := p-q-1
    have hp : p = q+1+h := by dsimp [h]; omega
    refine ⟨1+(q+1)+(h+1)+(q+1), by omega, ?_⟩
    have hw := word_long_run q h a stream
    rw [hp]
    have hneq : q+1+h ≠ q := by omega
    simp only [hneq,decide_false,Bool.and_false]
    simpa only [List.replicate_add,List.replicate_succ,
      List.cons_append,List.append_assoc,replicate_true_rotate] using hw

def words : List ℕ → List Bool
  | [] => []
  | p::ps => List.replicate p true ++ false::words ps

def budget (ps : List ℕ) (q : ℕ) : ℕ :=
  (ps.map fun p => 4*(p+q+1)).sum

theorem words_run (ps : List ℕ) (q : ℕ) (a : Bool) :
    ∃ t ≤ budget ps q, run t (cfg (some .start) (a,none,none)
      (words ps) (List.replicate q true) []) =
      cfg (some .start)
        (a && ps.all (fun p => decide (p=q)),none,none)
        [] (List.replicate q true) [] := by
  induction ps generalizing a with
  | nil =>
    refine ⟨0, by simp [budget], ?_⟩
    simp [run,words]
  | cons p ps ih =>
    obtain ⟨t₁,hb₁,h₁⟩ := word_run p q a (words ps)
    obtain ⟨t₂,hb₂,h₂⟩ := ih (a && decide (p=q))
    refine ⟨t₁+t₂, ?_, ?_⟩
    · simp only [budget,List.map_cons,List.sum_cons] at hb₂ ⊢
      omega
    change run (t₁+t₂) (cfg (some .start) (a,none,none)
      (List.replicate p true ++ false::words ps)
      (List.replicate q true) []) = _
    rw [run_add h₁ t₂,h₂]
    simp only [List.all_cons,Bool.and_assoc]

theorem words_halt (ps : List ℕ) (q : ℕ) :
    ∃ t ≤ budget ps q + 1, run t (cfg (some .start) initial
      (words ps) (List.replicate q true) []) =
      cfg none (ps.all (fun p => decide (p=q)),none,none)
        [] (List.replicate q true) [] := by
  obtain ⟨t,hb,ht⟩ := words_run ps q true
  refine ⟨t+1, by omega, ?_⟩
  have hstop := start_nil (ps.all (fun p => decide (p=q)))
    (List.replicate q true) [] none none
  calc
    run (t+1) (cfg (some .start) initial
        (words ps) (List.replicate q true) [])
      = run 1 (cfg (some .start)
          (ps.all (fun p => decide (p=q)),none,none)
          [] (List.replicate q true) []) := by
        simpa only [initial,Bool.true_and] using run_add ht 1
    _ = _ := by simpa only [run,Function.iterate_one] using hstop

end EthInapproximability.CurrentPaper.MatrixStage4AlignmentStream
