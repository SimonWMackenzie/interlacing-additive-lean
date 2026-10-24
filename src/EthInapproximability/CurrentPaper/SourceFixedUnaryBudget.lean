import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineInline

/-!
# Fixed-arity multiplication of a unary constraint count

For fixed source arity `q`, the program copies a unary `m` stack exactly `q`
times into its output stack. Each copy is a genuine source-preserving Boolean
stack subroutine, so this constructs the `q*m` budget used by the vertex-size
guard without a unit-cost multiplication.
-/

namespace EthInapproximability.CurrentPaper.SourceFixedUnaryBudget

open Turing BitMachineEncoding

inductive Label (q : Nat) where
  | start (i : Fin (q + 1))
  | copy (i : Fin q) (l : BitMachineCopy.Label)
  deriving DecidableEq, Fintype

abbrev Config (q : Nat) := TM2.Cfg (fun _ : Fin 3 => Bool) (Label q) (Option Bool)

def program {q : Nat} : Label q →
    TM2.Stmt (fun _ : Fin 3 => Bool) (Label q) (Option Bool)
  | .start i =>
      if h : i.val < q then
        .load (fun _ => none) (.goto (fun _ => .copy ⟨i.val, h⟩ .scan))
      else .load (fun _ => none) .halt
  | .copy i l => BitMachineInline.stmt (.copy i) id id
      (some (.start ⟨i.val + 1, by omega⟩)) (BitMachineCopy.program l)

def run {q : Nat} (t : Nat) (c : Config q) := ((advance (program (q := q)))^[t]) c

theorem run_one {q : Nat} (c : Config q) : run 1 c = advance program c := rfl

theorem run_add {q : Nat} (t u : Nat) (c : Config q) :
    run (t + u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance (program (q := q))) u t c

def contents (source target : List Bool) : Fin 3 → List Bool :=
  BitMachineCopy.stackContents source target []

theorem start_step {q : Nat} (i : Fin (q + 1)) (hi : i.val < q)
    (v : Option Bool) (S : Fin 3 → List Bool) :
    advance program (⟨some (.start i), v, S⟩ : Config q) =
      ⟨some (.copy ⟨i.val, hi⟩ .scan), none, S⟩ := by
  simp only [advance, TM2.step, program, hi, ↓reduceDIte,
    TM2.stepAux, Option.getD_some]

theorem finish_step {q : Nat} (v : Option Bool) (S : Fin 3 → List Bool) :
    advance program (⟨some (.start (Fin.last q)), v, S⟩ : Config q) =
      ⟨none, none, S⟩ := by
  simp only [advance, TM2.step, program, Fin.val_last,
    lt_self_iff_false, ↓reduceDIte, TM2.stepAux, Option.getD_some]

theorem one_copy {q : Nat} (i : Fin q) (source target : List Bool) :
    ∃ t ≤ 2 * source.length + 2,
      run t (⟨some (.copy i .scan), none, contents source target⟩ : Config q) =
        ⟨some (.start ⟨i.val + 1, by omega⟩), none,
          contents source (source ++ target)⟩ := by
  have h := BitMachineCopy.run_correct none source target
  have hh : (BitMachineCopy.run (2 * source.length + 2)
      (BitMachineCopy.cfg (some .scan) none source target [])).l = none := by
    rw [h]
    rfl
  obtain ⟨t, ht, hr⟩ := BitMachineInline.outputs (.copy i) id id
    (fun _ => rfl) (some (.start ⟨i.val + 1, by omega⟩))
    BitMachineCopy.program program (fun _ => rfl)
    (BitMachineCopy.cfg (some .scan) none source target [])
    (2 * source.length + 2) hh
  change ((advance program)^[t]) _ =
    BitMachineInline.cfg (.copy i) id
      (some (.start ⟨i.val + 1, by omega⟩))
      (BitMachineCopy.run (2 * source.length + 2)
        (BitMachineCopy.cfg (some .scan) none source target [])) at hr
  rw [h] at hr
  refine ⟨t, ht, ?_⟩
  simpa only [run, BitMachineInline.cfg, BitMachineCopy.cfg, contents,
    Option.map_some, Option.map_none, id_eq] using hr

private theorem repeat_commute (k : Nat) (source : List Bool) :
    (List.replicate k source).flatten ++ source =
      source ++ (List.replicate k source).flatten := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [List.replicate_succ, List.flatten_cons, List.append_assoc]
      rw [ih]

theorem run_from (q : Nat) (source : List Bool) (i : Fin (q + 1))
    (target : List Bool) (v : Option Bool) :
    ∃ t ≤ (q - i.val) * (2 * source.length + 3) + 1,
      run t (⟨some (.start i), v, contents source target⟩ : Config q) =
        ⟨none, none, contents source
          ((List.replicate (q - i.val) source).flatten ++ target)⟩ := by
  by_cases hi : i.val < q
  · obtain ⟨t, ht, hr⟩ := one_copy ⟨i.val, hi⟩ source target
    obtain ⟨u, hu, hrun⟩ := run_from q source ⟨i.val + 1, by omega⟩
      (source ++ target) none
    refine ⟨1 + t + u, ?_, ?_⟩
    · have hc : q - i.val = (q - (i.val + 1)) + 1 := by omega
      have hu' : u ≤ (q - (i.val + 1)) * (2 * source.length + 3) + 1 := by
        simpa only [] using hu
      rw [hc]
      have hmul : (q - (i.val + 1) + 1) * (2 * source.length + 3) =
          (q - (i.val + 1)) * (2 * source.length + 3) +
            (2 * source.length + 3) := by ring
      rw [hmul]
      omega
    · rw [show 1 + t + u = (1 + t) + u by omega,
        run_add, run_add]
      rw [run_one, start_step i hi v (contents source target), hr, hrun]
      have hc : q - i.val = (q - (i.val + 1)) + 1 := by omega
      simp only [hc, List.replicate_succ, List.flatten_cons, List.append_assoc]
      simp only [← List.append_assoc,
        repeat_commute (q - (i.val + 1)) source]
  · have he : i = Fin.last q := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    subst i
    refine ⟨1, by simp, ?_⟩
    rw [show (q - (Fin.last q).val) = 0 by simp]
    simp only [List.replicate_zero, List.flatten_nil, List.nil_append]
    exact run_one _ |>.trans (finish_step v (contents source target))
termination_by q - i.val

private theorem flatten_replicate_unary (q m : Nat) :
    (List.replicate q (List.replicate m true)).flatten =
      List.replicate (q * m) true := by
  induction q with
  | zero => simp
  | succ q ih =>
      simp only [List.replicate_succ, List.flatten_cons, ih]
      simpa only [Nat.succ_mul, Nat.add_comm, List.replicate_add]

theorem multiply (q m : Nat) :
    ∃ t ≤ q * (2 * m + 3) + 1,
      run t (⟨some (.start 0), none,
        contents (List.replicate m true) []⟩ : Config q) =
        ⟨none, none, contents (List.replicate m true)
          (List.replicate (q * m) true)⟩ := by
  obtain ⟨t, ht, hr⟩ := run_from q (List.replicate m true) 0 [] none
  refine ⟨t, by simpa only [Fin.val_zero, Nat.sub_zero, List.length_replicate] using ht,
    ?_⟩
  simpa only [Fin.val_zero, Nat.sub_zero, List.append_nil,
    flatten_replicate_unary] using hr

end EthInapproximability.CurrentPaper.SourceFixedUnaryBudget
