import EthInapproximability.CurrentPaper.SourceCSPFinalOutput

/-!
# Fixed-coefficient physical unary affine map

This is a private generalization of the compiler-checked binary source-header
writer. Source: locked v8 Section 6, Boolean alphabet conversion. It consumes
two actual unary input words, computes their positive-coefficient linear
combination, and charges every pop and push. It does not supply either input.
-/

namespace EthInapproximability.CurrentPaper.SourceAffineUnary

open Turing Turing.TM2.Stmt BitMachineEncoding
open SourceBooleanEncoding

/-- The two positive fixed coefficients are stored by their predecessors.
No varying source count is compiled into the instruction table. -/
def vertexCoefficient (p : Nat × Nat) : Nat := p.1 + 1

def rowCoefficient (p : Nat × Nat) : Nat := p.2 + 1

theorem vertexCoefficient_pos (p : Nat × Nat) : 0 < vertexCoefficient p := by
  unfold vertexCoefficient
  omega

theorem rowCoefficient_pos (p : Nat × Nat) : 0 < rowCoefficient p := by
  unfold rowCoefficient
  omega

inductive Label (p : Nat × Nat) where
  | vertexScan
  | vertexPush : Fin (vertexCoefficient p) → Label p
  | rowScan
  | rowPush : Fin (rowCoefficient p) → Label p
  deriving DecidableEq, Fintype

abbrev Stack := Fin 3
abbrev Config (p : Nat × Nat) := TM2.Cfg (fun _ : Stack => Bool) (Label p) (Option Bool)

def contents (vertices rows output : List Bool) : Stack → List Bool :=
  ![vertices, rows, output]

def cfg {p : Nat × Nat} (label : Option (Label p)) (value : Option Bool)
    (vertices rows output : List Bool) : Config p :=
  ⟨label, value, contents vertices rows output⟩

/-- Consumes unary n and m, writing the affine unary variable count.
All labels are fixed once the coefficient pair p is fixed; only stack words carry n and m. -/
def program (p : Nat × Nat) : Label p → TM2.Stmt (fun _ : Stack => Bool) (Label p) (Option Bool)
  | .vertexScan =>
      pop 0 (fun _ b => b)
        (branch Option.isSome
          (goto (fun _ => .vertexPush ⟨0, vertexCoefficient_pos p⟩))
          (goto (fun _ => .rowScan)))
  | .vertexPush i =>
      push 2 (fun _ => true)
        (if h : i.val + 1 < vertexCoefficient p then
          goto (fun _ => .vertexPush ⟨i.val + 1, h⟩)
        else goto (fun _ => .vertexScan))
  | .rowScan =>
      pop 1 (fun _ b => b)
        (branch Option.isSome
          (goto (fun _ => .rowPush ⟨0, rowCoefficient_pos p⟩))
          halt)
  | .rowPush i =>
      push 2 (fun _ => true)
        (if h : i.val + 1 < rowCoefficient p then
          goto (fun _ => .rowPush ⟨i.val + 1, h⟩)
        else goto (fun _ => .rowScan))

theorem vertex_scan_cons (p : Nat × Nat) (b : Bool) (vs rs out : List Bool)
    (value : Option Bool) :
    advance (program p)
      (cfg (some .vertexScan) value (b :: vs) rs out) =
    cfg (some (.vertexPush ⟨0, vertexCoefficient_pos p⟩)) (some b)
      vs rs out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext i; fin_cases i <;> rfl

theorem vertex_scan_nil (p : Nat × Nat) (rs out : List Bool)
    (value : Option Bool) :
    advance (program p) (cfg (some .vertexScan) value [] rs out) =
      cfg (some .rowScan) none [] rs out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]

theorem row_scan_cons (p : Nat × Nat) (b : Bool) (rs out : List Bool)
    (value : Option Bool) :
    advance (program p) (cfg (some .rowScan) value [] (b :: rs) out) =
    cfg (some (.rowPush ⟨0, rowCoefficient_pos p⟩)) (some b)
      [] rs out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext i; fin_cases i <;> rfl

theorem row_scan_nil (p : Nat × Nat) (out : List Bool)
    (value : Option Bool) :
    advance (program p) (cfg (some .rowScan) value [] [] out) =
      cfg none none [] [] out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]

def run (p : Nat × Nat) (t : Nat) (c : Config p) : Config p :=
  ((advance (program p))^[t]) c

theorem run_add (p : Nat × Nat) (t u : Nat) (c : Config p) :
    run p (t + u) c = run p u (run p t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance (program p)) u t c

theorem vertex_push_next (p : Nat × Nat)
    (i : Fin (vertexCoefficient p))
    (h : i.val + 1 < vertexCoefficient p)
    (value : Option Bool) (vs rs out : List Bool) :
    advance (program p) (cfg (some (.vertexPush i)) value vs rs out) =
      cfg (some (.vertexPush ⟨i.val + 1, h⟩)) value vs rs
        (true :: out) := by
  simp [advance, TM2.step, TM2.stepAux, program, h, cfg, contents]
  funext x; fin_cases x <;> rfl

theorem vertex_push_last (p : Nat × Nat)
    (i : Fin (vertexCoefficient p))
    (h : ¬ i.val + 1 < vertexCoefficient p)
    (value : Option Bool) (vs rs out : List Bool) :
    advance (program p) (cfg (some (.vertexPush i)) value vs rs out) =
      cfg (some .vertexScan) value vs rs (true :: out) := by
  simp [advance, TM2.step, TM2.stepAux, program, h, cfg, contents]
  funext x; fin_cases x <;> rfl

theorem row_push_next (p : Nat × Nat)
    (i : Fin (rowCoefficient p))
    (h : i.val + 1 < rowCoefficient p)
    (value : Option Bool) (rs out : List Bool) :
    advance (program p) (cfg (some (.rowPush i)) value [] rs out) =
      cfg (some (.rowPush ⟨i.val + 1, h⟩)) value [] rs
        (true :: out) := by
  simp [advance, TM2.step, TM2.stepAux, program, h, cfg, contents]
  funext x; fin_cases x <;> rfl

theorem row_push_last (p : Nat × Nat)
    (i : Fin (rowCoefficient p))
    (h : ¬ i.val + 1 < rowCoefficient p)
    (value : Option Bool) (rs out : List Bool) :
    advance (program p) (cfg (some (.rowPush i)) value [] rs out) =
      cfg (some .rowScan) value [] rs (true :: out) := by
  simp [advance, TM2.step, TM2.stepAux, program, h, cfg, contents]
  funext x; fin_cases x <;> rfl

theorem vertex_push_run (p : Nat × Nat)
    (i : Fin (vertexCoefficient p))
    (value : Option Bool) (vs rs out : List Bool) :
    run p (vertexCoefficient p - i.val)
      (cfg (some (.vertexPush i)) value vs rs out) =
      cfg (some .vertexScan) value vs rs
        (List.replicate (vertexCoefficient p - i.val) true ++ out) := by
  let A := vertexCoefficient p
  have hmain : ∀ k : Nat, ∀ i : Fin A,
      A - i.val = k → ∀ value vs rs out,
      run p k (cfg (some (.vertexPush i)) value vs rs out) =
        cfg (some .vertexScan) value vs rs
          (List.replicate k true ++ out) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hk value vs rs out
      have hkpos : 0 < k := by have hi := i.isLt; omega
      by_cases hnext : i.val + 1 < A
      · let j : Fin A := ⟨i.val + 1, hnext⟩
        have hj : A - j.val = k - 1 := by dsimp [j]; omega
        have hlt : k - 1 < k := by omega
        calc
          run p k (cfg (some (.vertexPush i)) value vs rs out) =
              run p (k - 1)
                (advance (program p)
                  (cfg (some (.vertexPush i)) value vs rs out)) := by
                  rw [show k = (k - 1) + 1 by omega]
                  rfl
          _ = run p (k - 1)
                (cfg (some (.vertexPush j)) value vs rs (true :: out)) := by
                  rw [vertex_push_next p i hnext]
          _ = cfg (some .vertexScan) value vs rs
                (List.replicate (k - 1) true ++ true :: out) :=
                  ih (k - 1) hlt j hj value vs rs (true :: out)
          _ = cfg (some .vertexScan) value vs rs
                (List.replicate k true ++ out) := by
                  have hr : List.replicate (k - 1) true ++ [true] =
                      List.replicate k true := by
                    calc
                      _ = List.replicate ((k - 1) + 1) true := by
                            simp only [List.replicate_add, List.replicate_one]
                      _ = List.replicate k true := by congr 1; omega
                  simpa only [List.append_assoc, List.singleton_append] using
                    congrArg (fun xs : List Bool =>
                      cfg (some .vertexScan) value vs rs (xs ++ out)) hr
      · have hkone : k = 1 := by have hi := i.isLt; omega
        subst k
        have hd : A - i.val = 1 := by omega
        simpa only [hd, run, Function.iterate_one, List.replicate_one,
          List.singleton_append] using
          vertex_push_last p i hnext value vs rs out
  exact hmain (A - i.val) i rfl value vs rs out

theorem row_push_run (p : Nat × Nat)
    (i : Fin (rowCoefficient p))
    (value : Option Bool) (rs out : List Bool) :
    run p (rowCoefficient p - i.val)
      (cfg (some (.rowPush i)) value [] rs out) =
      cfg (some .rowScan) value [] rs
        (List.replicate (rowCoefficient p - i.val) true ++ out) := by
  let A := rowCoefficient p
  have hmain : ∀ k : Nat, ∀ i : Fin A,
      A - i.val = k → ∀ value rs out,
      run p k (cfg (some (.rowPush i)) value [] rs out) =
        cfg (some .rowScan) value [] rs
          (List.replicate k true ++ out) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hk value rs out
      have hkpos : 0 < k := by have hi := i.isLt; omega
      by_cases hnext : i.val + 1 < A
      · let j : Fin A := ⟨i.val + 1, hnext⟩
        have hj : A - j.val = k - 1 := by dsimp [j]; omega
        have hlt : k - 1 < k := by omega
        calc
          run p k (cfg (some (.rowPush i)) value [] rs out) =
              run p (k - 1)
                (advance (program p)
                  (cfg (some (.rowPush i)) value [] rs out)) := by
                  rw [show k = (k - 1) + 1 by omega]
                  rfl
          _ = run p (k - 1)
                (cfg (some (.rowPush j)) value [] rs (true :: out)) := by
                  rw [row_push_next p i hnext]
          _ = cfg (some .rowScan) value [] rs
                (List.replicate (k - 1) true ++ true :: out) :=
                  ih (k - 1) hlt j hj value rs (true :: out)
          _ = cfg (some .rowScan) value [] rs
                (List.replicate k true ++ out) := by
                  have hr : List.replicate (k - 1) true ++ [true] =
                      List.replicate k true := by
                    calc
                      _ = List.replicate ((k - 1) + 1) true := by
                            simp only [List.replicate_add, List.replicate_one]
                      _ = List.replicate k true := by congr 1; omega
                  simpa only [List.append_assoc, List.singleton_append] using
                    congrArg (fun xs : List Bool =>
                      cfg (some .rowScan) value [] rs (xs ++ out)) hr
      · have hkone : k = 1 := by have hi := i.isLt; omega
        subst k
        have hd : A - i.val = 1 := by omega
        simpa only [hd, run, Function.iterate_one, List.replicate_one,
          List.singleton_append] using
          row_push_last p i hnext value rs out
  exact hmain (A - i.val) i rfl value rs out

theorem vertex_run (p : Nat × Nat) (vs rs out : List Bool)
    (value : Option Bool) :
    run p ((vertexCoefficient p + 1) * vs.length + 1)
      (cfg (some .vertexScan) value vs rs out) =
    cfg (some .rowScan) none [] rs
      (List.replicate (vertexCoefficient p * vs.length) true ++ out) := by
  let A := vertexCoefficient p
  induction vs generalizing value out with
  | nil =>
      simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add,
        List.replicate_zero, List.nil_append, run, Function.iterate_one] using
        vertex_scan_nil p rs out value
  | cons b vs ih =>
      have hscan : run p 1
          (cfg (some .vertexScan) value (b :: vs) rs out) =
          cfg (some (.vertexPush ⟨0, vertexCoefficient_pos p⟩))
            (some b) vs rs out := vertex_scan_cons p b vs rs out value
      have hpush : run p A
          (cfg (some (.vertexPush ⟨0, vertexCoefficient_pos p⟩))
            (some b) vs rs out) =
          cfg (some .vertexScan) (some b) vs rs
            (List.replicate A true ++ out) := by
        simpa only [Nat.sub_zero] using
          vertex_push_run p ⟨0, vertexCoefficient_pos p⟩
            (some b) vs rs out
      have htail := ih (List.replicate A true ++ out) (some b)
      have htime : (A + 1) * (b :: vs).length + 1 =
          (1 + A) + ((A + 1) * vs.length + 1) := by
        simp only [List.length_cons, Nat.mul_succ]
        omega
      rw [htime, run_add p (1 + A) ((A + 1) * vs.length + 1),
        run_add p 1 A, hscan, hpush, htail]
      simp only [List.length_cons, Nat.mul_succ]
      rw [← List.append_assoc, ← List.replicate_add]

theorem row_run (p : Nat × Nat) (rs out : List Bool)
    (value : Option Bool) :
    run p ((rowCoefficient p + 1) * rs.length + 1)
      (cfg (some .rowScan) value [] rs out) =
    cfg none none [] []
      (List.replicate (rowCoefficient p * rs.length) true ++ out) := by
  let A := rowCoefficient p
  induction rs generalizing value out with
  | nil =>
      simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add,
        List.replicate_zero, List.nil_append, run, Function.iterate_one] using
        row_scan_nil p out value
  | cons b rs ih =>
      have hscan : run p 1
          (cfg (some .rowScan) value [] (b :: rs) out) =
          cfg (some (.rowPush ⟨0, rowCoefficient_pos p⟩))
            (some b) [] rs out := row_scan_cons p b rs out value
      have hpush : run p A
          (cfg (some (.rowPush ⟨0, rowCoefficient_pos p⟩))
            (some b) [] rs out) =
          cfg (some .rowScan) (some b) [] rs
            (List.replicate A true ++ out) := by
        simpa only [Nat.sub_zero] using
          row_push_run p ⟨0, rowCoefficient_pos p⟩
            (some b) rs out
      have htail := ih (List.replicate A true ++ out) (some b)
      have htime : (A + 1) * (b :: rs).length + 1 =
          (1 + A) + ((A + 1) * rs.length + 1) := by
        simp only [List.length_cons, Nat.mul_succ]
        omega
      rw [htime, run_add p (1 + A) ((A + 1) * rs.length + 1),
        run_add p 1 A, hscan, hpush, htail]
      simp only [List.length_cons, Nat.mul_succ]
      rw [← List.append_assoc, ← List.replicate_add]

/-- Exact physical affine-header run from two unary input words. -/
theorem run_correct (p : Nat × Nat) (n m : Nat) :
    run p (((vertexCoefficient p + 1) * n + 1) +
      ((rowCoefficient p + 1) * m + 1))
      (cfg (some .vertexScan) none
        (List.replicate n true) (List.replicate m true) []) =
    cfg none none [] []
      (List.replicate (vertexCoefficient p * n + rowCoefficient p * m)
        true) := by
  rw [run_add]
  have hv := vertex_run p (List.replicate n true)
    (List.replicate m true) [] none
  simp only [List.length_replicate, List.append_nil] at hv
  rw [hv]
  have hr := row_run p (List.replicate m true)
    (List.replicate (vertexCoefficient p * n) true) none
  simp only [List.length_replicate] at hr
  rw [hr]
  congr 1
  rw [← List.replicate_add]
  congr 1
  omega

#print axioms run_correct

end EthInapproximability.CurrentPaper.SourceAffineUnary
