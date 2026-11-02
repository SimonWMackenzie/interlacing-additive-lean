import CurrentAdditive.GaussPivotGuard32

namespace CurrentAdditive.GaussPivotGuardRun

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 32

variable (S : Stack → List Bool) (r m : Nat)
  (hr : S 30 = List.replicate r true)
  (hm : S 13 = List.replicate m true)
  (h20 : S 20 = []) (h21 : S 21 = [])
  (h22 : S 22 = []) (h29 : S 29 = [])

include hr hm h20 h21 h22 h29

theorem row_global :
    ∃ t ≤ 2 * r + 3,
      GaussPivotGuard32.run t (GaussPivotGuard32.initial S) =
        ⟨some .toCountCopy, .copy ((), none),
          GaussPivotGuard32.afterRow S⟩ := by
  let c : TM2.Cfg (fun _ : Stack => Bool)
      SourceClausePreservingBroadcast.Label (Unit × Option Bool) :=
    ⟨some .scan, ((), none), S⟩
  have hcore := SourceClausePreservingBroadcast.run_halt
    (30 : Stack) 29 [20] (by decide) (by simp) (by decide)
    (by decide) (List.replicate r true) S hr h29
  have hl : (((advance (SourceClausePreservingBroadcast.program
      (30 : Stack) 29 [20]))^[2 * r + 3]) c).l = none := by
    rw [show 2 * r + 3 = 2 * (List.replicate r true).length + 3 by simp]
    rw [hcore]
  obtain ⟨t, ht, he⟩ := BitMachineInline.outputs
    GaussPivotGuard32.Label.rowCopy GaussPivotGuard32.Control.copy
    GaussPivotGuard32.readCopy (by intro v; rfl)
    (some GaussPivotGuard32.Label.toCountCopy)
    (SourceClausePreservingBroadcast.program (30 : Stack) 29 [20])
    GaussPivotGuard32.program (by intro l; rfl) c (2 * r + 3) hl
  refine ⟨t, ht, ?_⟩
  change GaussPivotGuard32.run t _ = _ at he
  rw [show 2 * r + 3 = 2 * (List.replicate r true).length + 3 by simp,
    hcore] at he
  simpa [BitMachineInline.cfg, GaussPivotGuard32.initial,
    GaussPivotGuard32.afterRow, hr] using he

theorem after_row_13 : GaussPivotGuard32.afterRow S 13 = S 13 := by
  unfold GaussPivotGuard32.afterRow
  exact SourceClausePreservingBroadcast.other_preserved 30 29 [20]
    (S 30) S 13 (by decide) (by decide) (by decide)

theorem after_row_20 : GaussPivotGuard32.afterRow S 20 =
    List.replicate r true := by
  have h := SourceClausePreservingBroadcast.target_written
    (30 : Stack) 29 [20] (by decide) (by decide) (by decide)
    (S 30) S 20 (by simp)
  simpa [GaussPivotGuard32.afterRow, hr, h20] using h

theorem after_row_21 : GaussPivotGuard32.afterRow S 21 = [] := by
  unfold GaussPivotGuard32.afterRow
  rw [SourceClausePreservingBroadcast.other_preserved
    30 29 [20] (S 30) S 21 (by decide) (by decide) (by decide)]
  exact h21

theorem after_row_22 : GaussPivotGuard32.afterRow S 22 = [] := by
  unfold GaussPivotGuard32.afterRow
  rw [SourceClausePreservingBroadcast.other_preserved
    30 29 [20] (S 30) S 22 (by decide) (by decide) (by decide)]
  exact h22

theorem after_row_29 : GaussPivotGuard32.afterRow S 29 = [] :=
  SourceClausePreservingBroadcast.temp_empty _ _ _ _ _

theorem count_global :
    ∃ t ≤ 2 * m + 3,
      GaussPivotGuard32.run t
        ⟨some (.countCopy .scan), .copy ((), none),
          GaussPivotGuard32.afterRow S⟩ =
        ⟨some .toCompare, .copy ((), none),
          GaussPivotGuard32.afterCount S⟩ := by
  let S' := GaussPivotGuard32.afterRow S
  let c : TM2.Cfg (fun _ : Stack => Bool)
      SourceClausePreservingBroadcast.Label (Unit × Option Bool) :=
    ⟨some .scan, ((), none), S'⟩
  have hsource : S' 13 = List.replicate m true :=
    (after_row_13 S r m hr hm h20 h21 h22 h29).trans hm
  have hcore := SourceClausePreservingBroadcast.run_halt
    (13 : Stack) 29 [21] (by decide) (by simp) (by decide)
    (by decide) (List.replicate m true) S' hsource
    (after_row_29 S r m hr hm h20 h21 h22 h29)
  have hl : (((advance (SourceClausePreservingBroadcast.program
      (13 : Stack) 29 [21]))^[2 * m + 3]) c).l = none := by
    rw [show 2 * m + 3 = 2 * (List.replicate m true).length + 3 by simp]
    rw [hcore]
  obtain ⟨t, ht, he⟩ := BitMachineInline.outputs
    GaussPivotGuard32.Label.countCopy GaussPivotGuard32.Control.copy
    GaussPivotGuard32.readCopy (by intro v; rfl)
    (some GaussPivotGuard32.Label.toCompare)
    (SourceClausePreservingBroadcast.program (13 : Stack) 29 [21])
    GaussPivotGuard32.program (by intro l; rfl) c (2 * m + 3) hl
  refine ⟨t, ht, ?_⟩
  change GaussPivotGuard32.run t _ = _ at he
  rw [show 2 * m + 3 = 2 * (List.replicate m true).length + 3 by simp,
    hcore] at he
  simpa [BitMachineInline.cfg, GaussPivotGuard32.afterCount,
    hsource, S'] using he

theorem after_count_20 : GaussPivotGuard32.afterCount S 20 =
    List.replicate r true := by
  unfold GaussPivotGuard32.afterCount
  rw [SourceClausePreservingBroadcast.other_preserved
    13 29 [21] _ (GaussPivotGuard32.afterRow S) 20
    (by decide) (by decide) (by decide)]
  exact after_row_20 S r m hr hm h20 h21 h22 h29

theorem after_count_21 : GaussPivotGuard32.afterCount S 21 =
    List.replicate m true := by
  have h := SourceClausePreservingBroadcast.target_written
    (13 : Stack) 29 [21] (by decide) (by decide) (by decide)
    ((GaussPivotGuard32.afterRow S) 13)
    (GaussPivotGuard32.afterRow S) 21 (by simp)
  simpa [GaussPivotGuard32.afterCount,
    after_row_13 S r m hr hm h20 h21 h22 h29, hm,
    after_row_21 S r m hr hm h20 h21 h22 h29] using h

theorem after_count_22 : GaussPivotGuard32.afterCount S 22 = [] := by
  unfold GaussPivotGuard32.afterCount
  rw [SourceClausePreservingBroadcast.other_preserved
    13 29 [21] _ (GaussPivotGuard32.afterRow S) 22
    (by decide) (by decide) (by decide)]
  exact after_row_22 S r m hr hm h20 h21 h22 h29

theorem after_count_29 : GaussPivotGuard32.afterCount S 29 = [] :=
  SourceClausePreservingBroadcast.temp_empty _ _ _ _ _

theorem compare_global :
    ∃ t ≤ max r m + 2, ∃ w : EntryUnaryCompare.CV,
      GaussPivotGuard32.run t
        ⟨some (.compare .loop), .compare (none, none),
          GaussPivotGuard32.afterCount S⟩ =
        ⟨some .choose, .compare w,
          GaussPivotGuard32.afterCompare S r m⟩ := by
  let S' := GaussPivotGuard32.afterCount S
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
    GaussPivotGuard32.Label.compare GaussPivotGuard32.Control.compare
    GaussPivotGuard32.readCompare (by intro v; rfl)
    (some GaussPivotGuard32.Label.choose) P GaussPivotGuard32.program
    (by intro l; rfl) c u hl
  refine ⟨t, ht.trans hu, w, ?_⟩
  change GaussPivotGuard32.run t _ = _ at he
  rw [hr0] at he
  simpa [BitMachineInline.cfg, GaussPivotGuard32.afterCompare, P, c,
    S', after_count_22 S r m hr hm h20 h21 h22 h29]
    using he

theorem after_compare_flag :
    GaussPivotGuard32.afterCompare S r m 22 = [decide (r < m)] := by
  simp [GaussPivotGuard32.afterCompare, after_count_22 S r m hr hm h20 h21 h22 h29]

theorem after_choose_eq : GaussPivotGuard32.afterChoose S r m = S := by
  funext j
  by_cases hj20 : j = 20
  · subst j; simp [GaussPivotGuard32.afterChoose,
      GaussPivotGuard32.afterCompare, h20]
  by_cases hj21 : j = 21
  · subst j; simp [GaussPivotGuard32.afterChoose,
      GaussPivotGuard32.afterCompare, h21]
  by_cases hj22 : j = 22
  · subst j; simp [GaussPivotGuard32.afterChoose, h22]
  have hbase : GaussPivotGuard32.afterChoose S r m j =
      GaussPivotGuard32.afterCount S j := by
    simp [GaussPivotGuard32.afterChoose,
      GaussPivotGuard32.afterCompare, hj20, hj21, hj22]
  rw [hbase]
  by_cases hj29 : j = 29
  · subst j
    exact (after_count_29 S r m hr hm h20 h21 h22 h29).trans h29.symm
  by_cases hj13 : j = 13
  · subst j
    unfold GaussPivotGuard32.afterCount
    rw [SourceClausePreservingBroadcast.source_restored 13 29 [21]
      (by decide) _ _]
    exact after_row_13 S r m hr hm h20 h21 h22 h29
  by_cases hj30 : j = 30
  · subst j
    unfold GaussPivotGuard32.afterCount
    rw [SourceClausePreservingBroadcast.other_preserved 13 29 [21]
      _ (GaussPivotGuard32.afterRow S) 30
      (by decide) (by decide) (by decide)]
    unfold GaussPivotGuard32.afterRow
    exact SourceClausePreservingBroadcast.source_restored 30 29 [20]
      (by decide) (S 30) S
  have hCount := SourceClausePreservingBroadcast.other_preserved
    (13 : Stack) 29 [21] ((GaussPivotGuard32.afterRow S) 13)
    (GaussPivotGuard32.afterRow S) j
    hj13
    (by exact hj29)
    (by simpa only [List.mem_singleton] using hj21)
  rw [GaussPivotGuard32.afterCount, hCount]
  exact SourceClausePreservingBroadcast.other_preserved
    (30 : Stack) 29 [20] (S 30) S j
    hj30
    hj29 (by simpa only [List.mem_singleton] using hj20)

def clock : Nat := 2 * r + 3 + 1 + 2 * m + 3 + 1 + max r m + 2 + 1

theorem outputs :
    ∃ t ≤ clock r m,
      GaussPivotGuard32.run t (GaussPivotGuard32.initial S) =
        ⟨some (if r < m then .active else .terminal),
          .choose (some (decide (r < m))), S⟩ := by
  obtain ⟨t0, h0, hr0⟩ := row_global S r m hr hm h20 h21 h22 h29
  obtain ⟨t1, h1, hr1⟩ := count_global S r m hr hm h20 h21 h22 h29
  obtain ⟨t2, h2, w, hr2⟩ := compare_global S r m hr hm h20 h21 h22 h29
  have hstep0 := GaussPivotGuard32.to_count_step
    (GaussPivotGuard32.afterRow S) (.copy ((), none))
  have hs0 := (GaussPivotGuard32.run_add hr0 1).trans hstep0
  have hstep1 := GaussPivotGuard32.to_compare_step
    (GaussPivotGuard32.afterCount S) (.copy ((), none))
  have hs1 := (GaussPivotGuard32.run_add
    ((GaussPivotGuard32.run_add hs0 t1).trans hr1) 1).trans hstep1
  have hs2 := (GaussPivotGuard32.run_add hs1 t2).trans hr2
  have hflag := after_compare_flag S r m hr hm h20 h21 h22 h29
  have hs3 := (GaussPivotGuard32.run_add hs2 1).trans
    (GaussPivotGuard32.choose_step
      (GaussPivotGuard32.afterCompare S r m) (decide (r < m))
      (.compare w) hflag)
  refine ⟨t0 + 1 + t1 + 1 + t2 + 1, ?_, ?_⟩
  · unfold clock; omega
  · have hrestore : Function.update
        (GaussPivotGuard32.afterCompare S r m) 22 [] = S :=
      after_choose_eq S r m hr hm h20 h21 h22 h29
    rw [hrestore] at hs3
    simpa using hs3

#print axioms outputs

end CurrentAdditive.GaussPivotGuardRun
