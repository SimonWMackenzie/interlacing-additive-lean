import EthInapproximability.CurrentPaper.MatrixMaterializationMachine

/-!
# Reading selector alignment from physical words

Source: locked v8 `03-exact-hardness.tex`, the aligned-selector condition,
and `B-effectivity-details.tex`, `thm:paper-materialization`. The controller
compares coordinate zero with each of the other three coordinate words.
Every comparison uses literal pops and restores both words exactly. It then
loads the three tail bits. No alignment bit or rank is supplied as input.

Stacks 0--3 hold coordinates, 4--5 are initially empty scratch, 6--7 are
framed, and 8 holds the three tail bits followed by an arbitrary suffix.
The theorem works for arbitrary Boolean words, hence also unary coordinates.
-/

namespace EthInapproximability.CurrentPaper.MatrixSelectorAlignment

open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Header := MatrixMaterializationMachine.Control
abbrev Control := Header × Option Bool × Option Bool

inductive Label where
  | scan (i : Fin 3) | restore0 (i : Fin 3) | restore1 (i : Fin 3)
  | tail0 | tail1 | tail2
  deriving DecidableEq, Fintype

def next (i : Fin 3) : Label :=
  if h : i.val + 1 < 3 then .scan ⟨i.val + 1, h⟩ else .tail0

def target (i : Fin 3) : Fin 9 := ⟨i.val + 1, by omega⟩

def matchHeads (s : Control) : Control :=
  ({s.1 with aligned := s.1.aligned && decide (s.2.1 = s.2.2)}, s.2)

def program : Label → TM2.Stmt (fun _ : Fin 9 => Bool) Label Control
  | .scan i => pop 0 (fun s b => (s.1, b, s.2.2))
      (pop (target i) (fun s b => (s.1, s.2.1, b))
        (branch (fun s => s.2.1.isSome)
          (push 4 (fun s => s.2.1.getD false)
            (branch (fun s => s.2.2.isSome)
              (push 5 (fun s => s.2.2.getD false)
                (load matchHeads (goto (fun _ => .scan i))))
              (load matchHeads (goto (fun _ => .scan i)))))
          (branch (fun s => s.2.2.isSome)
            (push 5 (fun s => s.2.2.getD false)
              (load matchHeads (goto (fun _ => .scan i))))
            (goto (fun _ => .restore0 i)))))
  | .restore0 i => pop 4 (fun s b => (s.1, b, none))
      (branch (fun s => s.2.1.isSome)
        (push 0 (fun s => s.2.1.getD false) (goto (fun _ => .restore0 i)))
        (goto (fun _ => .restore1 i)))
  | .restore1 i => pop 5 (fun s b => (s.1, none, b))
      (branch (fun s => s.2.2.isSome)
        (push (target i) (fun s => s.2.2.getD false) (goto (fun _ => .restore1 i)))
        (goto (fun _ => next i)))
  | .tail0 => pop 8 (fun s b => ({s.1 with tail0 := b.getD false}, none, none))
      (goto (fun _ => .tail1))
  | .tail1 => pop 8 (fun s b => ({s.1 with tail1 := b.getD false}, none, none))
      (goto (fun _ => .tail2))
  | .tail2 => pop 8 (fun s b =>
      (MatrixMaterializationMachine.header s.1.aligned
        ![s.1.tail0, s.1.tail1, b.getD false], none, none)) halt

abbrev Config := TM2.Cfg (fun _ : Fin 9 => Bool) Label Control

def contents (α : Fin 4 → List Bool) (a b : List Bool)
    (free : Fin 2 → List Bool) (tail : List Bool) : Fin 9 → List Bool :=
  ![α 0, α 1, α 2, α 3, a, b, free 0, free 1, tail]

def cfg (l : Option Label) (s : Control) (α : Fin 4 → List Bool)
    (a b : List Bool) (free : Fin 2 → List Bool) (tail : List Bool) : Config :=
  ⟨l, s, contents α a b free tail⟩

def pair (i : Fin 3) (p q : List Bool) (α : Fin 4 → List Bool) : Fin 4 → List Bool :=
  Function.update (Function.update α 0 p) i.succ q

def pairCfg (l : Option Label) (s : Control) (i : Fin 3) (p q : List Bool)
    (α : Fin 4 → List Bool) (a b : List Bool)
    (free : Fin 2 → List Bool) (tail : List Bool) : Config :=
  cfg l s (pair i p q α) a b free tail

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem scan_step (i : Fin 3) (s : Control) (p q : List Bool)
    (α : Fin 4 → List Bool) (a b : List Bool) (free : Fin 2 → List Bool) (tail : List Bool) :
    TM2.step program (pairCfg (some (.scan i)) s i p q α a b free tail) =
      some (pairCfg
        (some (if p = [] ∧ q = [] then .restore0 i else .scan i))
        ({s.1 with aligned := s.1.aligned && decide (p.head? = q.head?)}, p.head?, q.head?)
        i p.tail q.tail α (p.head?.toList ++ a) (q.head?.toList ++ b) free tail) := by
  cases p <;> cases q <;> fin_cases i <;>
    simp only [List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
      Option.toList_none, Option.toList_some, List.nil_append, List.singleton_append,
      List.cons_ne_nil, and_self, and_false, and_true,
      reduceIte, decide_true, Bool.and_true] <;>
    apply congrArg (fun S => some (⟨_, _, S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

theorem scan_run (i : Fin 3) (s : Control) (p q : List Bool)
    (α : Fin 4 → List Bool) (a b : List Bool) (free : Fin 2 → List Bool) (tail : List Bool) :
    run (max p.length q.length + 1) (pairCfg (some (.scan i)) s i p q α a b free tail) =
      pairCfg (some (.restore0 i))
        ({s.1 with aligned := s.1.aligned && decide (p = q)}, none, none)
        i [] [] α (p.reverse ++ a) (q.reverse ++ b) free tail := by
  induction p generalizing q s a b with
  | nil =>
      induction q generalizing s b with
      | nil =>
          simpa only [List.length_nil, Nat.max_self, Nat.zero_add, List.reverse_nil,
            List.nil_append, decide_true, Bool.and_true] using
            run_succ (scan_step i s [] [] α a b free tail) 0
      | cons c q ih =>
          rw [List.length_nil, Nat.zero_max, List.length_cons,
            run_succ (scan_step i s [] (c :: q) α a b free tail) _]
          simpa [List.reverse_cons, List.append_assoc, Bool.and_assoc] using
            ih ({s.1 with aligned := false}, none, some c) (c :: b)
  | cons c p ih =>
      cases q with
      | nil =>
          rw [List.length_nil, Nat.max_zero, List.length_cons,
            run_succ (scan_step i s (c :: p) [] α a b free tail) _]
          simpa [List.reverse_cons, List.append_assoc, Bool.and_assoc] using
            ih ({s.1 with aligned := false}, some c, none) [] (c :: a) b
      | cons d q =>
          rw [List.length_cons, List.length_cons, max_add_add_right,
            run_succ (scan_step i s (c :: p) (d :: q) α a b free tail) _]
          simpa [List.reverse_cons, List.append_assoc, Bool.and_assoc, List.cons.injEq,
            Bool.and_comm, Bool.and_left_comm] using
            ih ({s.1 with aligned := s.1.aligned && decide (c = d)}, some c, some d)
              q (c :: a) (d :: b)

private theorem restore0_cons (i : Fin 3) (s : Control) (p q : List Bool)
    (α : Fin 4 → List Bool) (v : Bool) (a b : List Bool)
    (free : Fin 2 → List Bool) (tail : List Bool) :
    TM2.step program (pairCfg (some (.restore0 i)) s i p q α (v :: a) b free tail) =
      some (pairCfg (some (.restore0 i)) (s.1, some v, none)
        i (v :: p) q α a b free tail) := by
  fin_cases i <;> apply congrArg (fun S => some (⟨_, _, S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem restore0_nil (i : Fin 3) (s : Control) (p q : List Bool)
    (α : Fin 4 → List Bool) (b : List Bool) (free : Fin 2 → List Bool) (tail : List Bool) :
    TM2.step program (pairCfg (some (.restore0 i)) s i p q α [] b free tail) =
      some (pairCfg (some (.restore1 i)) (s.1, none, none) i p q α [] b free tail) := by
  fin_cases i <;> apply congrArg (fun S => some (⟨_, _, S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem restore1_cons (i : Fin 3) (s : Control) (p q : List Bool)
    (α : Fin 4 → List Bool) (v : Bool) (a b : List Bool)
    (free : Fin 2 → List Bool) (tail : List Bool) :
    TM2.step program (pairCfg (some (.restore1 i)) s i p q α a (v :: b) free tail) =
      some (pairCfg (some (.restore1 i)) (s.1, none, some v)
        i p (v :: q) α a b free tail) := by
  fin_cases i <;> apply congrArg (fun S => some (⟨_, _, S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem restore1_nil (i : Fin 3) (s : Control) (p q : List Bool)
    (α : Fin 4 → List Bool) (a : List Bool) (free : Fin 2 → List Bool) (tail : List Bool) :
    TM2.step program (pairCfg (some (.restore1 i)) s i p q α a [] free tail) =
      some (pairCfg (some (next i)) (s.1, none, none) i p q α a [] free tail) := by
  fin_cases i <;> apply congrArg (fun S => some (⟨_, _, S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

theorem restore0_run (i : Fin 3) (s : Control) (p q : List Bool)
    (α : Fin 4 → List Bool) (a b : List Bool) (free : Fin 2 → List Bool) (tail : List Bool) :
    run (a.length + 1) (pairCfg (some (.restore0 i)) s i p q α a b free tail) =
      pairCfg (some (.restore1 i)) (s.1, none, none) i (a.reverse ++ p) q α [] b free tail := by
  induction a generalizing p s with
  | nil => exact run_succ (restore0_nil i s p q α b free tail) 0
  | cons v a ih =>
      rw [List.length_cons, run_succ (restore0_cons i s p q α v a b free tail) _]
      simpa [List.reverse_cons, List.append_assoc] using ih (s.1, some v, none) (v :: p)

theorem restore1_run (i : Fin 3) (s : Control) (p q : List Bool)
    (α : Fin 4 → List Bool) (a b : List Bool) (free : Fin 2 → List Bool) (tail : List Bool) :
    run (b.length + 1) (pairCfg (some (.restore1 i)) s i p q α a b free tail) =
      pairCfg (some (next i)) (s.1, none, none) i p (b.reverse ++ q) α a [] free tail := by
  induction b generalizing q s with
  | nil => exact run_succ (restore1_nil i s p q α a free tail) 0
  | cons v b ih =>
      rw [List.length_cons, run_succ (restore1_cons i s p q α v a b free tail) _]
      simpa [List.reverse_cons, List.append_assoc] using ih (s.1, none, some v) (v :: q)

def pairTime (p q : List Bool) : ℕ := max p.length q.length + p.length + q.length + 3

theorem pair_run (i : Fin 3) (s : Control) (α : Fin 4 → List Bool)
    (free : Fin 2 → List Bool) (tail : List Bool) :
    run (pairTime (α 0) (α i.succ)) (cfg (some (.scan i)) s α [] [] free tail) =
      cfg (some (next i))
        ({s.1 with aligned := s.1.aligned && decide (α 0 = α i.succ)}, none, none)
        α [] [] free tail := by
  have hi : pair i (α 0) (α i.succ) α = α := by
    funext k
    simp [pair]
  have h₁ := scan_run i s (α 0) (α i.succ) α [] [] free tail
  simp only [List.append_nil] at h₁
  have h₂ := restore0_run i
    ({s.1 with aligned := s.1.aligned && decide (α 0 = α i.succ)}, none, none)
    [] [] α (α 0).reverse (α i.succ).reverse free tail
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h₂
  have h₃ := restore1_run i
    ({s.1 with aligned := s.1.aligned && decide (α 0 = α i.succ)}, none, none)
    (α 0) [] α [] (α i.succ).reverse free tail
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h₃
  have h := ((run_add h₁ ((α 0).length + 1)).trans h₂)
  have hh := (run_add h ((α i.succ).length + 1)).trans h₃
  have ht : max (α 0).length (α i.succ).length + 1 + ((α 0).length + 1) +
      ((α i.succ).length + 1) = pairTime (α 0) (α i.succ) := by unfold pairTime; omega
  simpa only [pairCfg, hi, ht] using hh

theorem tails_run (s : Control) (α : Fin 4 → List Bool)
    (free : Fin 2 → List Bool) (tail : Fin 3 → Bool) (suffix : List Bool) :
    run 3 (cfg (some .tail0) s α [] [] free (tail 0 :: tail 1 :: tail 2 :: suffix)) =
      cfg none (MatrixMaterializationMachine.header s.1.aligned tail, none, none)
        α [] [] free suffix := by
  have h₀ : TM2.step program
      (cfg (some .tail0) s α [] [] free (tail 0 :: tail 1 :: tail 2 :: suffix)) =
      some (cfg (some .tail1) ({s.1 with tail0 := tail 0}, none, none)
        α [] [] free (tail 1 :: tail 2 :: suffix)) := by
    apply congrArg (fun S => some (⟨_, _, S⟩ : Config))
    funext k; fin_cases k <;> rfl
  have h₁ : TM2.step program
      (cfg (some .tail1) ({s.1 with tail0 := tail 0}, none, none)
        α [] [] free (tail 1 :: tail 2 :: suffix)) =
      some (cfg (some .tail2) ({s.1 with tail0 := tail 0, tail1 := tail 1}, none, none)
        α [] [] free (tail 2 :: suffix)) := by
    apply congrArg (fun S => some (⟨_, _, S⟩ : Config))
    funext k; fin_cases k <;> rfl
  have h₂ : TM2.step program
      (cfg (some .tail2) ({s.1 with tail0 := tail 0, tail1 := tail 1}, none, none)
        α [] [] free (tail 2 :: suffix)) =
      some (cfg none (MatrixMaterializationMachine.header s.1.aligned tail, none, none)
        α [] [] free suffix) := by
    apply congrArg (fun S => some (⟨_, _, S⟩ : Config))
    funext k; fin_cases k <;> rfl
  rw [run_succ h₀ 2, run_succ h₁ 1, run_succ h₂ 0]
  rfl

def initial : Control := (MatrixMaterializationMachine.header true (fun _ => false), none, none)

def time (α : Fin 4 → List Bool) : ℕ :=
  pairTime (α 0) (α 1) + pairTime (α 0) (α 2) + pairTime (α 0) (α 3) + 3

theorem all_equal (α : Fin 4 → List Bool) :
    ((decide (α 0 = α 1) && decide (α 0 = α 2)) && decide (α 0 = α 3)) =
      decide (∀ p, α p = α 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩ p
    fin_cases p
    · rfl
    · exact h₁.symm
    · exact h₂.symm
    · exact h₃.symm
  · intro h
    exact ⟨⟨(h 1).symm, (h 2).symm⟩, (h 3).symm⟩

/-- Actual finite-control alignment and tail decoding, with exact restoration
of all four coordinate words and both foreign stacks. -/
theorem alignment_run (α : Fin 4 → List Bool) (free : Fin 2 → List Bool)
    (tail : Fin 3 → Bool) (suffix : List Bool) :
    run (time α) (cfg (some (.scan 0)) initial α [] [] free
      (tail 0 :: tail 1 :: tail 2 :: suffix)) =
      cfg none (MatrixMaterializationMachine.header (decide (∀ p, α p = α 0)) tail,
        none, none) α [] [] free suffix := by
  let bits := tail 0 :: tail 1 :: tail 2 :: suffix
  let h₀ := initial.1
  let h₁ : Header := {h₀ with aligned := decide (α 0 = α 1)}
  let h₂ : Header := {h₀ with aligned := decide (α 0 = α 1) && decide (α 0 = α 2)}
  let h₃ : Header := {h₀ with aligned :=
    (decide (α 0 = α 1) && decide (α 0 = α 2)) && decide (α 0 = α 3)}
  have r₀ : run (pairTime (α 0) (α 1))
      (cfg (some (.scan 0)) initial α [] [] free bits) =
      cfg (some (.scan 1)) (h₁, none, none) α [] [] free bits := by
    simpa only [next, initial, MatrixMaterializationMachine.header, Fin.val_zero,
      Nat.zero_add, Fin.succ_zero_eq_one, reduceDIte, h₁, h₀, Bool.true_and] using
      pair_run 0 initial α free bits
  have r₁ : run (pairTime (α 0) (α 2))
      (cfg (some (.scan 1)) (h₁, none, none) α [] [] free bits) =
      cfg (some (.scan 2)) (h₂, none, none) α [] [] free bits := by
    simpa only [next, h₁, h₂, Fin.val_one, reduceDIte] using pair_run 1 (h₁, none, none) α free bits
  have r₂ : run (pairTime (α 0) (α 3))
      (cfg (some (.scan 2)) (h₂, none, none) α [] [] free bits) =
      cfg (some .tail0) (h₃, none, none) α [] [] free bits := by
    simpa only [next, h₂, h₃, reduceDIte] using pair_run 2 (h₂, none, none) α free bits
  have r₃ := tails_run (h₃, none, none) α free tail suffix
  have r₀₁ := (run_add r₀ (pairTime (α 0) (α 2))).trans r₁
  have r₀₁₂ := (run_add r₀₁ (pairTime (α 0) (α 3))).trans r₂
  have h := (run_add r₀₁₂ 3).trans r₃
  simpa only [time, bits, h₃, all_equal] using h

theorem time_linear (α : Fin 4 → List Bool) :
    time α ≤ 6 * (α 0).length + 2 * ((α 1).length + (α 2).length + (α 3).length) + 12 := by
  unfold time pairTime
  omega

/-- Specialization to the unary coordinate words produced by label decoding. -/
theorem unary_alignment_run (α : Fin 4 → ℕ) (free : Fin 2 → List Bool)
    (tail : Fin 3 → Bool) (suffix : List Bool) :
    run (time (fun p => List.replicate (α p) true))
      (cfg (some (.scan 0)) initial (fun p => List.replicate (α p) true) [] [] free
        (tail 0 :: tail 1 :: tail 2 :: suffix)) =
      cfg none (MatrixMaterializationMachine.header (decide (∀ p, α p = α 0)) tail,
        none, none) (fun p => List.replicate (α p) true) [] [] free suffix := by
  have he : (∀ p, List.replicate (α p) true = List.replicate (α 0) true) ↔
      (∀ p, α p = α 0) := by
    constructor
    · intro h p
      simpa only [List.length_replicate] using congrArg List.length (h p)
    · intro h p
      rw [h p]
  simpa only [he] using alignment_run (fun p => List.replicate (α p) true) free tail suffix

theorem unary_time_linear (α : Fin 4 → ℕ) :
    time (fun p => List.replicate (α p) true) ≤
      6 * α 0 + 2 * (α 1 + α 2 + α 3) + 12 := by
  simpa only [List.length_replicate] using time_linear (fun p => List.replicate (α p) true)

end EthInapproximability.CurrentPaper.MatrixSelectorAlignment
