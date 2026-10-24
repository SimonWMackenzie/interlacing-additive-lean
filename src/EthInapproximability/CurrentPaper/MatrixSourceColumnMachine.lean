import EthInapproximability.CurrentPaper.MatrixStrideGather
import EthInapproximability.CurrentPaper.MatrixMaterializationMachine

/-!
# Reading the source-row rule from a gathered column

A reversed prefix of the source column starts with the current bit, followed
by the earlier bits in reverse order. The finite controller saves the first
bit and counts the remaining active bits, saturating at two. Alignment and
the three tail bits are supplied in finite control; neither a rank nor the
answer is input. Column-selector decoding is a separate operation.

Source: locked v8 `03-exact-hardness.tex`, the literal source-vector rule, and
Appendix B, `thm:paper-materialization`.
-/

namespace EthInapproximability.CurrentPaper.MatrixSourceColumnMachine

open Turing Turing.TM2.Stmt BitMachineEncoding
open MatrixMaterializationMachine

inductive Label where
  | current | scan
  deriving DecidableEq, Fintype

abbrev Control := MatrixMaterializationMachine.Control
abbrev Config := TM2.Cfg (fun _ : Fin 2 => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label Control
  | .current => pop 0 (fun s b => {s with answer := b.getD false}) (goto (fun _ => .scan))
  | .scan => pop 0 (fun s b =>
      {s with rank := increment s.rank (b.getD false), live := b.isSome})
      (branch Control.live (goto (fun _ => .scan))
        (push 1 (fun s => select s s.answer) (load (fun _ => {}) halt)))

def cfg (l : Option Label) (s : Control) (q out : List Bool) : Config :=
  ⟨l, s, ![q, out]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_current (s : Control) (b : Bool) (q out : List Bool) :
    TM2.step program (cfg (some .current) s (b :: q) out) =
      some (cfg (some .scan) {s with answer := b} q out) := by
  apply congrArg (fun S => some (⟨some .scan, {s with answer := b}, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem step_scan_cons (s : Control) (b : Bool) (q out : List Bool) :
    TM2.step program (cfg (some .scan) s (b :: q) out) =
      some (cfg (some .scan) {s with rank := increment s.rank b, live := true} q out) := by
  apply congrArg (fun S => some
    (⟨some .scan, {s with rank := increment s.rank b, live := true}, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem step_scan_nil (s : Control) (out : List Bool) :
    TM2.step program (cfg (some .scan) s [] out) =
      some (cfg none {} [] (select s s.answer :: out)) := by
  apply congrArg (fun S => some (⟨none, ({} : Control), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

/-- The rank is calculated by literal pops, not supplied to the controller. -/
theorem scan_run (s : Control) (before out : List Bool) :
    run (before.length + 1) (cfg (some .scan) s before out) =
      cfg none {} [] (select {s with rank := countFrom s.rank before} s.answer :: out) := by
  induction before generalizing s with
  | nil => exact run_succ (step_scan_nil s out) 0
  | cons b before ih =>
      rw [List.length_cons, run_succ (step_scan_cons _ _ _ _) _]
      simpa only [countFrom, select] using ih {s with rank := increment s.rank b, live := true}

theorem consume_run (aligned : Bool) (tail : Fin 3 → Bool) (active : Bool)
    (before out : List Bool) :
    run (before.length + 2) (cfg (some .current) (header aligned tail) (active :: before) out) =
      cfg none {} [] (answer aligned tail before active :: out) := by
  have h₁ := run_succ (step_current (header aligned tail) active before out) 0
  have h₂ := scan_run {header aligned tail with answer := active} before out
  have h := (run_add h₁ (before.length + 1)).trans h₂
  have ht : 1 + (before.length + 1) = before.length + 2 := by omega
  simpa only [ht, answer, select, header] using h

/-- Reversing the predecessor list cannot change its saturated active count. -/
theorem countFrom_reverse (r : Fin 3) (before : List Bool) :
    countFrom r before.reverse = countFrom r before := by
  apply Fin.ext
  simp only [countFrom_val, List.filter_reverse, List.length_reverse]

theorem answer_reverse (aligned : Bool) (tail : Fin 3 → Bool) (before : List Bool)
    (active : Bool) :
    answer aligned tail before.reverse active = answer aligned tail before active := by
  simp only [answer, countFrom_reverse]

/-- Exactly the source bits strictly before the selected row. -/
def beforeColumn {n d : ℕ} (v : Fin n → Fin d → Bool) (i : Fin n) (α : Fin d) : List Bool :=
  List.ofFn fun j : Fin i.val => v ⟨j.val, j.isLt.trans i.isLt⟩ α

@[simp] theorem beforeColumn_length {n d : ℕ}
    (v : Fin n → Fin d → Bool) (i : Fin n) (α : Fin d) :
    (beforeColumn v i α).length = i.val := by simp [beforeColumn]

theorem beforeColumn_count {n d : ℕ}
    (v : Fin n → Fin d → Bool) (i : Fin n) (α : Fin d) :
    ((beforeColumn v i α).filter id).length = Construction.activeRank v α i := by
  let p : Fin i.val → Bool := fun j => v ⟨j.val, j.isLt.trans i.isLt⟩ α
  change ((List.ofFn p).filter id).length = _
  rw [List.ofFn_eq_map, List.filter_map, List.length_map]
  have hn := (List.nodup_finRange i.val).filter (id ∘ p)
  rw [← List.toFinset_card_of_nodup hn, List.toFinset_filter, List.toFinset_finRange]
  apply Finset.card_bij (fun j _ => (⟨j.val, j.isLt.trans i.isLt⟩ : Fin n))
  · intro j hj
    have hv : v ⟨j.val, j.isLt.trans i.isLt⟩ α = true := by simpa [p] using hj
    simp only [Construction.activeBefore, Construction.activeItems, Finset.mem_filter,
      Finset.mem_univ, true_and, hv]
    exact j.isLt
  · intro j hj k hk he
    exact Fin.ext (congrArg (fun x : Fin n => x.val) he)
  · intro j hj
    have h : v j α = true ∧ j < i := by
      simpa [Construction.activeBefore, Construction.activeItems] using hj
    refine ⟨⟨j.val, h.2⟩, ?_, ?_⟩
    · simpa [p] using h.1
    · exact Fin.ext rfl

/-- The order of the gathered predecessor bits agrees with the manuscript's
rank because rank counts the active predecessors, rather than their order. -/
theorem reversed_rank {n d : ℕ}
    (v : Fin n → Fin d → Bool) (i : Fin n) (α : Fin d) :
    (countFrom 0 (beforeColumn v i α).reverse).val =
      min 2 (Construction.activeRank v α i) := by
  simp only [countFrom_reverse, countFrom_val, beforeColumn_count, Fin.val_zero, Nat.zero_add]

theorem source_answer_correct {n d N₁ : ℕ}
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (i : Fin n) (c : ExactConstruction.Columns d N₁) :
    answer (decide (ExactConstruction.aligned c)) c.1
      (beforeColumn v i (c.2 0).1).reverse (v i (c.2 0).1) =
      ExactConstruction.vectorEntry v cap i c := by
  rw [answer_reverse, answer_eq]
  unfold ExactConstruction.vectorEntry
  by_cases h : ExactConstruction.aligned c
  · simp only [h, decide_true, Bool.true_and, ↓reduceIte]
    by_cases hi : v i (c.2 0).1 = true
    · simp only [hi, ↓reduceIte, ↓reduceDIte]
      apply congrArg c.1
      apply Fin.ext
      rw [countFrom_val, beforeColumn_count]
      have hr := (Construction.activeRank_lt_card v (c.2 0).1 i hi).trans_le (cap _)
      change min 2 (0 + Construction.activeRank v (c.2 0).1 i) =
        Construction.activeRank v (c.2 0).1 i
      omega
    · simp [hi]
  · simp [h]

theorem gathered_prefix {n d : ℕ} (v : Fin n → Fin d → Bool) (i : Fin n) (α : Fin d) :
    MatrixStrideGather.word d α.val (i.val + 1) (MatrixMaterialization.rowMajor v) =
      beforeColumn v i α ++ [v i α] := by
  rw [MatrixStrideGather.word_eq_ofFn, List.ofFn_succ']
  simp only [Fin.val_castSucc, Fin.val_last, List.concat_eq_append]
  have hbefore :
      (List.ofFn fun j : Fin i.val =>
        (MatrixMaterialization.rowMajor v)[α.val + j.val * d]?.getD false) =
      beforeColumn v i α := by
    apply congrArg List.ofFn
    funext j
    rw [Nat.add_comm α.val]
    exact congrArg (fun b : Option Bool => b.getD false)
      (MatrixMaterialization.rowMajor_entry v ⟨j.val, j.isLt.trans i.isLt⟩ α)
  rw [hbefore, Nat.add_comm α.val, MatrixMaterialization.rowMajor_entry]
  rfl

/-- Given the literal strided gather output, the controller computes the
source-row matrix entry in exactly `i + 2` further transitions. -/
theorem consume_source_prefix {n d N₁ : ℕ}
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (i : Fin n) (c : ExactConstruction.Columns d N₁) (out : List Bool) :
    run (i.val + 2)
      (cfg (some .current) (header (decide (ExactConstruction.aligned c)) c.1)
        ((MatrixStrideGather.word d (c.2 0).1.val (i.val + 1)
          (MatrixMaterialization.rowMajor v)).reverse) out) =
      cfg none {} [] (ExactConstruction.vectorEntry v cap i c :: out) := by
  rw [gathered_prefix, List.reverse_concat]
  have h := consume_run (decide (ExactConstruction.aligned c)) c.1 (v i (c.2 0).1)
    (beforeColumn v i (c.2 0).1).reverse out
  rw [source_answer_correct v cap i c] at h
  simpa only [List.length_reverse, beforeColumn_length] using h

namespace Gather

open BitMachineComposition BitMachineSubroutine BitMachineSubroutineRenaming

abbrev Label := MatrixStrideGather.Label ⊕ MatrixSourceColumnMachine.Label
abbrev Control := MatrixStrideGather.Control × MatrixSourceColumnMachine.Control
abbrev Config := TM2.Cfg (fun _ : Fin 11 => Bool) Label Control

def gatherBank : (Fin 7 ⊕ Fin 3) ⊕ Fin 1 ≃ Fin 11 :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 1))).trans finSumFinEquiv

private def consumerPerm : Fin 11 ≃ Fin 11 where
  toFun i := ![5, 10, 0, 1, 2, 3, 4, 6, 7, 8, 9] i
  invFun i := ![2, 3, 4, 5, 6, 0, 7, 8, 9, 10, 1] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def consumerBank : Fin 2 ⊕ Fin 9 ≃ Fin 11 := finSumFinEquiv.trans consumerPerm

def program : Label → TM2.Stmt (fun _ : Fin 11 => Bool) Label Control
  | .inl l => renameStmt gatherBank (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some MatrixSourceColumnMachine.Label.current) (MatrixStrideGather.program l))
  | .inr l => renameStmt consumerBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftStmt none (MatrixSourceColumnMachine.program l))

def cfg (l : Option Label) (s : MatrixSourceColumnMachine.Control)
    (index source buffer counter stride out : List Bool) : Config :=
  ⟨l, ((MatrixStrideGather.baseControl, false), s),
    ![index, [], [], source, [], buffer, [], counter, stride, [], out]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem gather_input (s : MatrixSourceColumnMachine.Control)
    (idx source counter stride out : List Bool) :
    renameCfg gatherBank (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some MatrixSourceColumnMachine.Label.current) s (fun _ : Fin 1 => out)
        (MatrixStrideGather.cfg (some (.inr .test)) false idx source [] counter stride [])) =
      cfg (some (.inl (.inr .test))) s idx source [] counter stride out := by
  apply congrArg (fun S => (⟨some (.inl (.inr .test)),
    ((MatrixStrideGather.baseControl, false), s), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem gather_output (s : MatrixSourceColumnMachine.Control)
    (idx source buffer stride out : List Bool) :
    renameCfg gatherBank (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some MatrixSourceColumnMachine.Label.current) s (fun _ : Fin 1 => out)
        (MatrixStrideGather.cfg none false idx source buffer [] stride [])) =
      cfg (some (.inr .current)) s idx source buffer [] stride out := by
  apply congrArg (fun S => (⟨some (.inr .current),
    ((MatrixStrideGather.baseControl, false), s), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem consumer_input (s : MatrixSourceColumnMachine.Control)
    (idx source buffer stride out : List Bool) :
    renameCfg consumerBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftCfg none (MatrixStrideGather.baseControl, false)
        (![idx, [], [], source, [], [], [], stride, []] : Fin 9 → List Bool)
        (MatrixSourceColumnMachine.cfg (some .current) s buffer out)) =
      cfg (some (.inr .current)) s idx source buffer [] stride out := by
  apply congrArg (fun S => (⟨some (.inr .current),
    ((MatrixStrideGather.baseControl, false), s), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem consumer_output (idx source stride out : List Bool) :
    renameCfg consumerBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftCfg none (MatrixStrideGather.baseControl, false)
        (![idx, [], [], source, [], [], [], stride, []] : Fin 9 → List Bool)
        (MatrixSourceColumnMachine.cfg none {} [] out)) =
      cfg none {} idx source [] [] stride out := by
  apply congrArg (fun S => (⟨none,
    ((MatrixStrideGather.baseControl, false),
      ({} : MatrixSourceColumnMachine.Control)), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

/-- One physical controller gathers the actual prefix from the row-major
source, counts it, and writes the exact source-vector entry. Only alignment
and tail bits are preloaded in finite control; the source support premise is
used to identify the answer and is never inspected by the machine. -/
theorem source_run {n d N₁ : ℕ}
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (i : Fin n) (c : ExactConstruction.Columns d N₁) (out : List Bool) :
    ∃ t ≤ (i.val + 1) *
        (3 * ((c.2 0).1.val + (i.val + 1) * d) + 3 * (n * d) + 2 * d + 12) + i.val + 3,
      run t (cfg (some (.inl (.inr .test))) (header (decide (ExactConstruction.aligned c)) c.1)
        (List.replicate (c.2 0).1.val true) (MatrixMaterialization.rowMajor v) []
        (List.replicate (i.val + 1) true) (List.replicate d true) out) =
        cfg none {} (List.replicate ((c.2 0).1.val + (i.val + 1) * d) true)
          (MatrixMaterialization.rowMajor v) [] [] (List.replicate d true)
          (ExactConstruction.vectorEntry v cap i c :: out) := by
  let src := MatrixMaterialization.rowMajor v
  let α := (c.2 0).1.val
  let hcontrol := header (decide (ExactConstruction.aligned c)) c.1
  let address := List.replicate (α + (i.val + 1) * d) true
  let buffer := (MatrixStrideGather.word d α (i.val + 1) src).reverse
  obtain ⟨kg, hkg, hrg⟩ := MatrixStrideGather.gather_run (i.val + 1) α d false src []
  simp only [List.append_nil] at hrg
  have hg : (((advance MatrixStrideGather.program)^[kg])
      (MatrixStrideGather.cfg (some (.inr .test)) false (List.replicate α true) src []
        (List.replicate (i.val + 1) true) (List.replicate d true) [])).l = none := by
    change (MatrixStrideGather.run kg _).l = none
    rw [hrg]
    rfl
  obtain ⟨tg, htg, hrunG⟩ := lift_outputs_renamed gatherBank (Equiv.refl _) (Equiv.refl _)
    MatrixStrideGather.program program (some MatrixSourceColumnMachine.Label.current)
    (fun _ => rfl) hcontrol (fun _ : Fin 1 => out)
    (MatrixStrideGather.cfg (some (.inr .test)) false (List.replicate α true) src []
      (List.replicate (i.val + 1) true) (List.replicate d true) []) kg hg
  change (((advance MatrixStrideGather.program)^[kg]) _) = _ at hrg
  rw [hrg, gather_input, gather_output] at hrunG
  have hrc := consume_source_prefix v cap i c out
  have hc : (((advance MatrixSourceColumnMachine.program)^[i.val + 2])
      (MatrixSourceColumnMachine.cfg (some .current) hcontrol buffer out)).l = none := by
    change (MatrixSourceColumnMachine.run (i.val + 2) _).l = none
    rw [hrc]
    rfl
  obtain ⟨tc, htc, hrunC⟩ := lift_outputs_renamed consumerBank
    (Equiv.sumComm _ _) (Equiv.prodComm _ _)
    MatrixSourceColumnMachine.program program none (fun _ => rfl)
    (MatrixStrideGather.baseControl, false)
    (![address, [], [], src, [], [], [], List.replicate d true, []] : Fin 9 → List Bool)
    (MatrixSourceColumnMachine.cfg (some .current) hcontrol buffer out) (i.val + 2) hc
  change (((advance MatrixSourceColumnMachine.program)^[i.val + 2]) _) = _ at hrc
  rw [hrc, consumer_input, consumer_output] at hrunC
  refine ⟨tg + tc, ?_, ?_⟩
  · simp only [src, MatrixMaterialization.rowMajor_length] at hkg
    dsimp [α] at hkg
    omega
  · exact (run_add hrunG tc).trans hrunC

end Gather

end EthInapproximability.CurrentPaper.MatrixSourceColumnMachine
