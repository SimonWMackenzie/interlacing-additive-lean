import CurrentAdditive.CodeDIndependenceGuard

noncomputable section

namespace CurrentAdditive.CodeDIndependenceGuardRun

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

noncomputable abbrev Stack := GaussStateMatrixContext.Bank

variable (S : Stack → List Bool) (r m : Nat)
  (hr : S 1 = List.replicate r true)
  (hm : S 3 = List.replicate m true)
  (h20 : S 20 = []) (h21 : S 21 = [])
  (h22 : S 22 = []) (h29 : S 29 = [])

include hr hm h20 h21 h22 h29

theorem row_global :
    ∃ t ≤ 2 * r + 3,
      CodeDIndependenceGuard.run t (CodeDIndependenceGuard.initial S) =
        ⟨some .toCountCopy, .copy ((), none),
          CodeDIndependenceGuard.afterRow S⟩ := by
  let c : TM2.Cfg (fun _ : Stack => Bool)
      SourceClausePreservingBroadcast.Label (Unit × Option Bool) :=
    ⟨some .scan, ((), none), S⟩
  have hcore := SourceClausePreservingBroadcast.run_halt
    (1 : Stack) 29 [20] (by decide) (by simp) (by decide)
    (by decide) (List.replicate r true) S hr h29
  have hl : (((advance (SourceClausePreservingBroadcast.program
      (1 : Stack) 29 [20]))^[2 * r + 3]) c).l = none := by
    rw [show 2 * r + 3 = 2 * (List.replicate r true).length + 3 by simp]
    rw [hcore]
  obtain ⟨t, ht, he⟩ := BitMachineInline.outputs
    CodeDIndependenceGuard.Label.rowCopy CodeDIndependenceGuard.Control.copy
    CodeDIndependenceGuard.readCopy (by intro v; rfl)
    (some CodeDIndependenceGuard.Label.toCountCopy)
    (SourceClausePreservingBroadcast.program (1 : Stack) 29 [20])
    CodeDIndependenceGuard.program (by intro l; rfl) c (2 * r + 3) hl
  refine ⟨t, ht, ?_⟩
  change CodeDIndependenceGuard.run t _ = _ at he
  rw [show 2 * r + 3 = 2 * (List.replicate r true).length + 3 by simp,
    hcore] at he
  simpa [BitMachineInline.cfg, CodeDIndependenceGuard.initial,
    CodeDIndependenceGuard.afterRow, hr] using he

theorem after_row_13 : CodeDIndependenceGuard.afterRow S 3 = S 3 := by
  unfold CodeDIndependenceGuard.afterRow
  exact SourceClausePreservingBroadcast.other_preserved 1 29 [20]
    (S 1) S 3 (by decide) (by decide) (by decide)

theorem after_row_20 : CodeDIndependenceGuard.afterRow S 20 =
    List.replicate r true := by
  have h := SourceClausePreservingBroadcast.target_written
    (1 : Stack) 29 [20] (by decide) (by decide) (by decide)
    (S 1) S 20 (by simp)
  simpa [CodeDIndependenceGuard.afterRow, hr, h20] using h

theorem after_row_21 : CodeDIndependenceGuard.afterRow S 21 = [] := by
  unfold CodeDIndependenceGuard.afterRow
  rw [SourceClausePreservingBroadcast.other_preserved
    1 29 [20] (S 1) S 21 (by decide) (by decide) (by decide)]
  exact h21

theorem after_row_22 : CodeDIndependenceGuard.afterRow S 22 = [] := by
  unfold CodeDIndependenceGuard.afterRow
  rw [SourceClausePreservingBroadcast.other_preserved
    1 29 [20] (S 1) S 22 (by decide) (by decide) (by decide)]
  exact h22

theorem after_row_29 : CodeDIndependenceGuard.afterRow S 29 = [] :=
  SourceClausePreservingBroadcast.temp_empty _ _ _ _ _

theorem count_global :
    ∃ t ≤ 2 * m + 3,
      CodeDIndependenceGuard.run t
        ⟨some (.countCopy .scan), .copy ((), none),
          CodeDIndependenceGuard.afterRow S⟩ =
        ⟨some .toCompare, .copy ((), none),
          CodeDIndependenceGuard.afterCount S⟩ := by
  let S' := CodeDIndependenceGuard.afterRow S
  let c : TM2.Cfg (fun _ : Stack => Bool)
      SourceClausePreservingBroadcast.Label (Unit × Option Bool) :=
    ⟨some .scan, ((), none), S'⟩
  have hsource : S' 3 = List.replicate m true :=
    (after_row_13 S r m hr hm h20 h21 h22 h29).trans hm
  have hcore := SourceClausePreservingBroadcast.run_halt
    (3 : Stack) 29 [21] (by decide) (by simp) (by decide)
    (by decide) (List.replicate m true) S' hsource
    (after_row_29 S r m hr hm h20 h21 h22 h29)
  have hl : (((advance (SourceClausePreservingBroadcast.program
      (3 : Stack) 29 [21]))^[2 * m + 3]) c).l = none := by
    rw [show 2 * m + 3 = 2 * (List.replicate m true).length + 3 by simp]
    rw [hcore]
  obtain ⟨t, ht, he⟩ := BitMachineInline.outputs
    CodeDIndependenceGuard.Label.countCopy CodeDIndependenceGuard.Control.copy
    CodeDIndependenceGuard.readCopy (by intro v; rfl)
    (some CodeDIndependenceGuard.Label.toCompare)
    (SourceClausePreservingBroadcast.program (3 : Stack) 29 [21])
    CodeDIndependenceGuard.program (by intro l; rfl) c (2 * m + 3) hl
  refine ⟨t, ht, ?_⟩
  change CodeDIndependenceGuard.run t _ = _ at he
  rw [show 2 * m + 3 = 2 * (List.replicate m true).length + 3 by simp,
    hcore] at he
  simpa [BitMachineInline.cfg, CodeDIndependenceGuard.afterCount,
    hsource, S'] using he

theorem after_count_20 : CodeDIndependenceGuard.afterCount S 20 =
    List.replicate r true := by
  unfold CodeDIndependenceGuard.afterCount
  rw [SourceClausePreservingBroadcast.other_preserved
    3 29 [21] _ (CodeDIndependenceGuard.afterRow S) 20
    (by decide) (by decide) (by decide)]
  exact after_row_20 S r m hr hm h20 h21 h22 h29

theorem after_count_21 : CodeDIndependenceGuard.afterCount S 21 =
    List.replicate m true := by
  have h := SourceClausePreservingBroadcast.target_written
    (3 : Stack) 29 [21] (by decide) (by decide) (by decide)
    ((CodeDIndependenceGuard.afterRow S) 3)
    (CodeDIndependenceGuard.afterRow S) 21 (by simp)
  simpa [CodeDIndependenceGuard.afterCount,
    after_row_13 S r m hr hm h20 h21 h22 h29, hm,
    after_row_21 S r m hr hm h20 h21 h22 h29] using h

theorem after_count_22 : CodeDIndependenceGuard.afterCount S 22 = [] := by
  unfold CodeDIndependenceGuard.afterCount
  rw [SourceClausePreservingBroadcast.other_preserved
    3 29 [21] _ (CodeDIndependenceGuard.afterRow S) 22
    (by decide) (by decide) (by decide)]
  exact after_row_22 S r m hr hm h20 h21 h22 h29

theorem after_count_29 : CodeDIndependenceGuard.afterCount S 29 = [] :=
  SourceClausePreservingBroadcast.temp_empty _ _ _ _ _

theorem compare_global :
    ∃ t ≤ max r m + 2, ∃ w : EntryUnaryCompare.CV,
      CodeDIndependenceGuard.run t
        ⟨some (.compare .loop), .compare (none, none),
          CodeDIndependenceGuard.afterCount S⟩ =
        ⟨some .choose, .compare w,
          CodeDIndependenceGuard.afterCompare S r m⟩ := by
  let S' := CodeDIndependenceGuard.afterCount S
  let P := EntryUnaryCompare.program (20 : Stack) 21 22 true false false
  let c : TM2.Cfg (fun _ : Stack => Bool) EntryUnaryCompare.CL
      EntryUnaryCompare.CV := ⟨some .loop, (none, none), S'⟩
  obtain ⟨u, hu, w, hr0⟩ := EntryUnaryCompare.compare_run
    (20 : Stack) 21 22 (by decide) (by decide) (by decide)
    true false false S' (none, none) r m
    (after_count_20 S r m hr hm h20 h21 h22 h29)
    (after_count_21 S r m hr hm h20 h21 h22 h29)
  have hv : EntryUnaryCompare.verdict true false false r m =
      decide (r < m) := by simp [EntryUnaryCompare.verdict]
  rw [hv] at hr0
  have hl : (((advance P)^[u]) c).l = none := by rw [hr0]
  obtain ⟨t, ht, he⟩ := BitMachineInline.outputs
    CodeDIndependenceGuard.Label.compare CodeDIndependenceGuard.Control.compare
    CodeDIndependenceGuard.readCompare (by intro v; rfl)
    (some CodeDIndependenceGuard.Label.choose) P CodeDIndependenceGuard.program
    (by intro l; rfl) c u hl
  refine ⟨t, ht.trans hu, w, ?_⟩
  change CodeDIndependenceGuard.run t _ = _ at he
  rw [hr0] at he
  simpa [BitMachineInline.cfg, CodeDIndependenceGuard.afterCompare, P, c,
    S', after_count_22 S r m hr hm h20 h21 h22 h29]
    using he

theorem after_compare_flag :
    CodeDIndependenceGuard.afterCompare S r m 22 = [decide (r < m)] := by
  simp [CodeDIndependenceGuard.afterCompare, after_count_22 S r m hr hm h20 h21 h22 h29]

theorem after_choose_eq : CodeDIndependenceGuard.afterChoose S r m = S := by
  funext j
  by_cases hj20 : j = 20
  · subst j; simp [CodeDIndependenceGuard.afterChoose,
      CodeDIndependenceGuard.afterCompare, h20]
  by_cases hj21 : j = 21
  · subst j; simp [CodeDIndependenceGuard.afterChoose,
      CodeDIndependenceGuard.afterCompare, h21]
  by_cases hj22 : j = 22
  · subst j; simp [CodeDIndependenceGuard.afterChoose, h22]
  have hbase : CodeDIndependenceGuard.afterChoose S r m j =
      CodeDIndependenceGuard.afterCount S j := by
    simp [CodeDIndependenceGuard.afterChoose,
      CodeDIndependenceGuard.afterCompare, hj20, hj21, hj22]
  rw [hbase]
  by_cases hj29 : j = 29
  · subst j
    exact (after_count_29 S r m hr hm h20 h21 h22 h29).trans h29.symm
  by_cases hj13 : j = 3
  · subst j
    unfold CodeDIndependenceGuard.afterCount
    rw [SourceClausePreservingBroadcast.source_restored 3 29 [21]
      (by decide) _ _]
    exact after_row_13 S r m hr hm h20 h21 h22 h29
  by_cases hj30 : j = 1
  · subst j
    unfold CodeDIndependenceGuard.afterCount
    rw [SourceClausePreservingBroadcast.other_preserved 3 29 [21]
      _ (CodeDIndependenceGuard.afterRow S) 1
      (by decide) (by decide) (by decide)]
    unfold CodeDIndependenceGuard.afterRow
    exact SourceClausePreservingBroadcast.source_restored 1 29 [20]
      (by decide) (S 1) S
  have hCount := SourceClausePreservingBroadcast.other_preserved
    (3 : Stack) 29 [21] ((CodeDIndependenceGuard.afterRow S) 3)
    (CodeDIndependenceGuard.afterRow S) j
    hj13
    (by exact hj29)
    (by simpa only [List.mem_singleton] using hj21)
  rw [CodeDIndependenceGuard.afterCount, hCount]
  exact SourceClausePreservingBroadcast.other_preserved
    (1 : Stack) 29 [20] (S 1) S j
    hj30
    hj29 (by simpa only [List.mem_singleton] using hj20)

def clock : Nat := 2 * r + 3 + 1 + 2 * m + 3 + 1 + max r m + 2 + 1

theorem outputs :
    ∃ t ≤ clock r m,
      CodeDIndependenceGuard.run t (CodeDIndependenceGuard.initial S) =
        ⟨some (if r < m then .active else .terminal),
          .choose (some (decide (r < m))), S⟩ := by
  obtain ⟨t0, h0, hr0⟩ := row_global S r m hr hm h20 h21 h22 h29
  obtain ⟨t1, h1, hr1⟩ := count_global S r m hr hm h20 h21 h22 h29
  obtain ⟨t2, h2, w, hr2⟩ := compare_global S r m hr hm h20 h21 h22 h29
  have hstep0 := CodeDIndependenceGuard.to_count_step
    (CodeDIndependenceGuard.afterRow S) (.copy ((), none))
  have hs0 := (CodeDIndependenceGuard.run_add hr0 1).trans hstep0
  have hstep1 := CodeDIndependenceGuard.to_compare_step
    (CodeDIndependenceGuard.afterCount S) (.copy ((), none))
  have hs1 := (CodeDIndependenceGuard.run_add
    ((CodeDIndependenceGuard.run_add hs0 t1).trans hr1) 1).trans hstep1
  have hs2 := (CodeDIndependenceGuard.run_add hs1 t2).trans hr2
  have hflag := after_compare_flag S r m hr hm h20 h21 h22 h29
  have hs3 := (CodeDIndependenceGuard.run_add hs2 1).trans
    (CodeDIndependenceGuard.choose_step
      (CodeDIndependenceGuard.afterCompare S r m) (decide (r < m))
      (.compare w) hflag)
  refine ⟨t0 + 1 + t1 + 1 + t2 + 1, ?_, ?_⟩
  · unfold clock; omega
  · have hrestore : Function.update
        (CodeDIndependenceGuard.afterCompare S r m) 22 [] = S :=
      after_choose_eq S r m hr hm h20 h21 h22 h29
    rw [hrestore] at hs3
    simpa using hs3

#print axioms outputs

end CurrentAdditive.CodeDIndependenceGuardRun
