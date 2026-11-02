import CurrentAdditive.GaussStepActiveRun32

/-! The fixed pivot branch copies its four destination fields while
preserving the old parsed row, column, list, and every auxiliary bank above
the destination range. This supplies the literal next-stage bank invariant. -/

namespace CurrentAdditive.GaussPivotBranchForeign32

noncomputable section

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussStepFields32

private theorem broadcast_foreign
    (source target : Stack) (U : Stack → List Bool)
    (bits : List Bool) (hbits : bits = U source)
    (hst : source ≠ 31) (j : Stack)
    (hjtarget : j ≠ target) (hjtemp : j ≠ 31) :
    SourceClausePreservingBroadcast.result source 31 [target]
      bits U j = U j := by
  by_cases hsource : j = source
  · subst j
    rw [SourceClausePreservingBroadcast.source_restored
      source 31 [target] hst bits U]
    exact hbits
  · exact SourceClausePreservingBroadcast.other_preserved
      source 31 [target] bits U j hsource hjtemp
      (by simpa using hjtarget)

theorem after3_foreign (T : Stack → List Bool) (j : Stack)
    (hj : 8 ≤ j.val) (hj31 : j ≠ 31) :
    GaussBranchFields32.after3 .pivot T j = T j := by
  have hdest (p : Fin 4) : j ≠ GaussBranchFields32.dest p := by
    intro e
    have hv := congrArg Fin.val e
    fin_cases p <;> simp [GaussBranchFields32.dest] at hv <;> omega
  have hsource (p : Fin 4) :
      GaussBranchFields32.source .pivot p ≠ 31 := by
    fin_cases p <;> decide
  have h0 (q : Stack) (hq : 8 ≤ q.val) (hq31 : q ≠ 31) :
      GaussBranchFields32.after0 .pivot T q = T q := by
    exact broadcast_foreign
      (GaussBranchFields32.source .pivot 0)
      (GaussBranchFields32.dest 0) T
      (T (GaussBranchFields32.source .pivot 0)) rfl
      (hsource 0) q (by
        intro e; have hv := congrArg Fin.val e
        simp [GaussBranchFields32.dest] at hv
        omega) hq31
  have h1 (q : Stack) (hq : 8 ≤ q.val) (hq31 : q ≠ 31) :
      GaussBranchFields32.after1 .pivot T q = T q := by
    have hs := h0 (GaussBranchFields32.source .pivot 1)
      (by decide) (hsource 1)
    calc
      _ = GaussBranchFields32.after0 .pivot T q := by
        exact broadcast_foreign
          (GaussBranchFields32.source .pivot 1)
          (GaussBranchFields32.dest 1)
          (GaussBranchFields32.after0 .pivot T)
          (T (GaussBranchFields32.source .pivot 1))
          hs.symm (hsource 1) q (by
            intro e; have hv := congrArg Fin.val e
            simp [GaussBranchFields32.dest] at hv
            omega) hq31
      _ = T q := h0 q hq hq31
  have h2 (q : Stack) (hq : 8 ≤ q.val) (hq31 : q ≠ 31) :
      GaussBranchFields32.after2 .pivot T q = T q := by
    have hs := h1 (GaussBranchFields32.source .pivot 2)
      (by decide) (hsource 2)
    calc
      _ = GaussBranchFields32.after1 .pivot T q := by
        exact broadcast_foreign
          (GaussBranchFields32.source .pivot 2)
          (GaussBranchFields32.dest 2)
          (GaussBranchFields32.after1 .pivot T)
          (T (GaussBranchFields32.source .pivot 2))
          hs.symm (hsource 2) q (by
            intro e; have hv := congrArg Fin.val e
            simp [GaussBranchFields32.dest] at hv
            omega) hq31
      _ = T q := h1 q hq hq31
  have hs := h2 (GaussBranchFields32.source .pivot 3)
    (by decide) (hsource 3)
  calc
    _ = GaussBranchFields32.after2 .pivot T j := by
      exact broadcast_foreign
        (GaussBranchFields32.source .pivot 3)
        (GaussBranchFields32.dest 3)
        (GaussBranchFields32.after2 .pivot T)
        (T (GaussBranchFields32.source .pivot 3))
        hs.symm (hsource 3) j (hdest 3) hj31
    _ = T j := h2 j hj hj31

theorem adjusted_foreign (T : Stack → List Bool) (j : Stack)
    (hj : 8 ≤ j.val) (hj31 : j ≠ 31) :
    GaussStepBranchRun32.adjusted .pivot T j = T j := by
  change (Function.update
    (Function.update (GaussBranchFields32.after3 .pivot T) 5
      (true :: (GaussBranchFields32.after3 .pivot T) 5)) 6
      (true :: (GaussBranchFields32.after3 .pivot T) 6)) j = T j
  rw [Function.update_of_ne (by
      intro e; have hv := congrArg Fin.val e; omega : j ≠ 6),
    Function.update_of_ne (by
      intro e; have hv := congrArg Fin.val e; omega : j ≠ 5)]
  exact after3_foreign T j hj hj31

theorem adjusted_scratch (T : Stack → List Bool) :
    GaussStepBranchRun32.adjusted .pivot T 31 = [] := by
  change (Function.update
    (Function.update (GaussBranchFields32.after3 .pivot T) 5
      (true :: (GaussBranchFields32.after3 .pivot T) 5)) 6
      (true :: (GaussBranchFields32.after3 .pivot T) 6)) 31 = []
  rw [Function.update_of_ne (by decide : (31 : Stack) ≠ 6),
    Function.update_of_ne (by decide : (31 : Stack) ≠ 5)]
  exact SourceClausePreservingBroadcast.temp_empty _ _ _ _ _

#print axioms after3_foreign
#print axioms adjusted_foreign
#print axioms adjusted_scratch

end
end CurrentAdditive.GaussPivotBranchForeign32
