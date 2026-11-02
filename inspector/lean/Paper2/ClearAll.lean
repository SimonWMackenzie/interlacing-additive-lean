import EthInapproximability.CurrentPaper.BitMachineInline

/-! Unit 3, segment (2) tool: ONE fixed program that clears a finite list of
cells `cs : Fin N → K` (any bank), each by charged pops, with a uniform clock
`N * (Lmax + 1) + 1` whenever every listed cell holds at most `Lmax` bits.
Together with `StepXGrowth.exit_length_le` (which bounds every exit cell of
`stepX` by its entry length plus `pushBound * T`), this clears the existential
scratch of one request level with a clock independent of the pair and level. -/

set_option maxHeartbeats 4000000

namespace Paper2.ClearAll

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

variable {K : Type*} [DecidableEq K]

/-- Label `i < N`: pop cell `cs i` until empty, then go to `i + 1`; label `N`: halt. -/
def prog {N : ℕ} (cs : Fin N → K) :
    Fin (N + 1) → TM2.Stmt (fun _ : K => Bool) (Fin (N + 1)) (Option Bool)
  | i => if h : i.val < N then
      pop (cs ⟨i.val, h⟩) (fun _ b => b)
        (branch (fun v => v.isSome) (goto (fun _ => i))
          (goto (fun _ => ⟨i.val + 1, by omega⟩)))
    else halt

theorem cell_run {N : ℕ} (cs : Fin N → K) (i : ℕ) (h : i < N) (xs : List Bool)
    (T : K → List Bool) (hT : T (cs ⟨i, h⟩) = xs) (v : Option Bool) :
    ((advance (prog cs))^[xs.length + 1])
        (⟨some ⟨i, by omega⟩, v, T⟩ : TM2.Cfg (fun _ : K => Bool) (Fin (N + 1)) (Option Bool)) =
      ⟨some ⟨i + 1, by omega⟩, none, Function.update T (cs ⟨i, h⟩) []⟩ := by
  induction xs generalizing T v with
  | nil =>
    have hT' : Function.update T (cs ⟨i, h⟩) [] = T := by
      rw [← hT]; exact Function.update_eq_self _ _
    rw [hT']
    simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, prog, h, hT]
  | cons b xs ih =>
    have e1 : advance (prog cs)
        (⟨some ⟨i, by omega⟩, v, T⟩ : TM2.Cfg (fun _ : K => Bool) (Fin (N + 1)) (Option Bool)) =
        ⟨some ⟨i, by omega⟩, some b, Function.update T (cs ⟨i, h⟩) xs⟩ := by
      simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, prog, h, hT]
    rw [List.length_cons, Function.iterate_succ_apply, e1,
      ih (Function.update T (cs ⟨i, h⟩) xs) (by rw [Function.update_self]) (some b),
      Function.update_idem]

/-- The bank with the listed cells of index `≥ i` cleared. -/
noncomputable def clearFrom {N : ℕ} (cs : Fin N → K) (i : ℕ) (T : K → List Bool) :
    K → List Bool :=
  fun k => by
    classical
    exact if ∃ j : Fin N, i ≤ j.val ∧ cs j = k then [] else T k

theorem clearFrom_N {N : ℕ} (cs : Fin N → K) (T : K → List Bool) : clearFrom cs N T = T := by
  funext k
  simp only [clearFrom]
  rw [if_neg]
  rintro ⟨j, hj, -⟩
  exact absurd j.isLt (by omega)

theorem clearFrom_step {N : ℕ} (cs : Fin N → K) (hinj : Function.Injective cs) (i : ℕ)
    (h : i < N) (T : K → List Bool) :
    clearFrom cs (i + 1) (Function.update T (cs ⟨i, h⟩) []) = clearFrom cs i T := by
  funext k
  simp only [clearFrom]
  by_cases hk : k = cs ⟨i, h⟩
  · subst hk
    rw [if_neg, if_pos ⟨⟨i, h⟩, le_rfl, rfl⟩, Function.update_self]
    rintro ⟨j, hj, hjk⟩
    have := hinj hjk
    subst this
    simp at hj
  · rw [Function.update_of_ne hk]
    by_cases hex : ∃ j : Fin N, i + 1 ≤ j.val ∧ cs j = k
    · rw [if_pos hex, if_pos (by obtain ⟨j, hj, hjk⟩ := hex; exact ⟨j, by omega, hjk⟩)]
    · rw [if_neg hex, if_neg]
      rintro ⟨j, hj, hjk⟩
      by_cases hji : j.val = i
      · apply hk
        rw [← hjk]
        congr 1
        exact Fin.ext hji
      · exact hex ⟨j, by omega, hjk⟩

/-- Clearing all listed cells: ONE run, uniform clock. -/
theorem all_run {N : ℕ} (cs : Fin N → K) (hinj : Function.Injective cs) (Lmax : ℕ)
    (T : K → List Bool) (hL : ∀ j, (T (cs j)).length ≤ Lmax) (v : Option Bool) :
    ∃ t ≤ N * (Lmax + 1) + 1, ∃ v',
      ((advance (prog cs))^[t])
          (⟨some ⟨0, by omega⟩, v, T⟩ : TM2.Cfg (fun _ : K => Bool) (Fin (N + 1)) (Option Bool)) =
        ⟨none, v', clearFrom cs 0 T⟩ := by
  suffices H : ∀ m, m ≤ N → ∀ (T : K → List Bool) (v : Option Bool),
      (∀ j, (T (cs j)).length ≤ Lmax) →
      ∃ t ≤ m * (Lmax + 1) + 1, ∃ v',
        ((advance (prog cs))^[t])
            (⟨some ⟨N - m, by omega⟩, v, T⟩ :
              TM2.Cfg (fun _ : K => Bool) (Fin (N + 1)) (Option Bool)) =
          ⟨none, v', clearFrom cs (N - m) T⟩ by
    have := H N le_rfl T v hL
    simpa using this
  intro m
  induction m with
  | zero =>
    intro _ T v _
    refine ⟨1, by omega, v, ?_⟩
    have hlab : (⟨N - 0, by omega⟩ : Fin (N + 1)) = ⟨N, by omega⟩ := Fin.ext (by simp)
    have hcl : clearFrom cs (N - 0) T = T := by
      rw [Nat.sub_zero]; exact clearFrom_N cs T
    rw [hlab, hcl, Function.iterate_one]
    simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, prog]
  | succ m ih =>
    intro hm T v hL
    have hi : N - (m + 1) < N := by omega
    have e1 := cell_run cs (N - (m + 1)) hi (T (cs ⟨N - (m + 1), hi⟩)) T rfl v
    have hL' : ∀ j, ((Function.update T (cs ⟨N - (m + 1), hi⟩) []) (cs j)).length ≤ Lmax := by
      intro j
      by_cases hj : cs j = cs ⟨N - (m + 1), hi⟩
      · rw [hj, Function.update_self]; simp
      · rw [Function.update_of_ne hj]; exact hL j
    obtain ⟨t', ht', v', hr⟩ := ih (by omega) _ none hL'
    have hlab : (⟨N - (m + 1) + 1, by omega⟩ : Fin (N + 1)) = ⟨N - m, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [hlab] at e1
    have hc : clearFrom cs (N - m) (Function.update T (cs ⟨N - (m + 1), hi⟩) []) =
        clearFrom cs (N - (m + 1)) T := by
      have := clearFrom_step cs hinj (N - (m + 1)) hi T
      rwa [show N - (m + 1) + 1 = N - m by omega] at this
    refine ⟨t' + ((T (cs ⟨N - (m + 1), hi⟩)).length + 1), ?_, v', ?_⟩
    · have := hL ⟨N - (m + 1), hi⟩
      have : (m + 1) * (Lmax + 1) + 1 = (Lmax + 1) + (m * (Lmax + 1) + 1) := by ring
      omega
    · rw [Function.iterate_add_apply, e1, hr, hc]

end Paper2.ClearAll

#print axioms Paper2.ClearAll.cell_run
#print axioms Paper2.ClearAll.clearFrom_step
#print axioms Paper2.ClearAll.all_run
