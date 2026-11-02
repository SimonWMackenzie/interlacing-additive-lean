import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
# A charged unary comparator writing its verdict bit to a stack

Lane owner:b-stage4-entry-program-2, segment 2 (component).

ONE fixed three-label controller on any bank, with three distinct cells
`A`, `B`, `O`: it pops `A` and `B` in lockstep; when one runs out it pushes
the verdict bit (`lt` if `|A| < |B|`, `eq` if equal, `gt` if `|A| > |B|`) on
`O`, then drains the longer word. Exit: `A` and `B` blank, `O` extended by the
verdict, every other cell unchanged. Clock `max |A| |B| + 2` (exact bound).
-/

namespace EthInapproximability.CurrentPaper.EntryUnaryCompare

open Turing BitMachineEncoding

inductive CL where
  | loop | drainA | drainB
  deriving DecidableEq, Fintype

abbrev CV := Option Bool × Option Bool

variable {K : Type*} [DecidableEq K]

def program (A B O : K) (lt eq gt : Bool) : CL → TM2.Stmt (fun _ : K => Bool) CL CV
  | .loop => .pop A (fun v x => (x, v.2)) (.pop B (fun v y => (v.1, y))
      (.branch (fun v => v.1.isSome && v.2.isSome) (.goto fun _ => .loop)
        (.branch (fun v => v.1.isSome)
          (.push O (fun _ => gt) (.goto fun _ => .drainA))
          (.branch (fun v => v.2.isSome)
            (.push O (fun _ => lt) (.goto fun _ => .drainB))
            (.push O (fun _ => eq) .halt)))))
  | .drainA => .pop A (fun v x => (x, v.2))
      (.branch (fun v => v.1.isSome) (.goto fun _ => .drainA) .halt)
  | .drainB => .pop B (fun v y => (v.1, y))
      (.branch (fun v => v.2.isSome) (.goto fun _ => .drainB) .halt)

def verdict (lt eq gt : Bool) (a b : ℕ) : Bool :=
  if a < b then lt else if a = b then eq else gt

theorem drainA_run (A B O : K) (lt eq gt : Bool) (S : K → List Bool) (v : CV) (n : ℕ)
    (hA : S A = List.replicate n true) :
    ∃ w, ((advance (program A B O lt eq gt))^[n + 1])
      (⟨some .drainA, v, S⟩ : TM2.Cfg (fun _ : K => Bool) CL CV) =
      ⟨none, w, Function.update S A []⟩ := by
  induction n generalizing S v with
  | zero =>
      refine ⟨(none, v.2), ?_⟩
      have hA0 : S A = [] := by simpa using hA
      have hu : Function.update S A [] = S := Function.update_eq_self_iff.mpr hA0.symm
      simp [advance, TM2.step, TM2.stepAux, program, hA0, hu]
  | succ n ih =>
      have h1 : advance (program A B O lt eq gt)
          (⟨some .drainA, v, S⟩ : TM2.Cfg (fun _ : K => Bool) CL CV) =
          ⟨some .drainA, (some true, v.2), Function.update S A (List.replicate n true)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, hA, List.replicate_succ]
      obtain ⟨w, hw⟩ := ih (Function.update S A (List.replicate n true)) (some true, v.2)
        (by simp)
      refine ⟨w, ?_⟩
      rw [Function.iterate_succ_apply, h1, hw, Function.update_idem]

theorem drainB_run (A B O : K) (lt eq gt : Bool) (S : K → List Bool) (v : CV) (n : ℕ)
    (hB : S B = List.replicate n true) :
    ∃ w, ((advance (program A B O lt eq gt))^[n + 1])
      (⟨some .drainB, v, S⟩ : TM2.Cfg (fun _ : K => Bool) CL CV) =
      ⟨none, w, Function.update S B []⟩ := by
  induction n generalizing S v with
  | zero =>
      refine ⟨(v.1, none), ?_⟩
      have hB0 : S B = [] := by simpa using hB
      have hu : Function.update S B [] = S := Function.update_eq_self_iff.mpr hB0.symm
      simp [advance, TM2.step, TM2.stepAux, program, hB0, hu]
  | succ n ih =>
      have h1 : advance (program A B O lt eq gt)
          (⟨some .drainB, v, S⟩ : TM2.Cfg (fun _ : K => Bool) CL CV) =
          ⟨some .drainB, (v.1, some true), Function.update S B (List.replicate n true)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, hB, List.replicate_succ]
      obtain ⟨w, hw⟩ := ih (Function.update S B (List.replicate n true)) (v.1, some true)
        (by simp)
      refine ⟨w, ?_⟩
      rw [Function.iterate_succ_apply, h1, hw, Function.update_idem]

theorem compare_run (A B O : K) (hAB : A ≠ B) (hAO : A ≠ O) (hBO : B ≠ O)
    (lt eq gt : Bool) (S : K → List Bool) (v : CV) (a b : ℕ)
    (hA : S A = List.replicate a true) (hB : S B = List.replicate b true) :
    ∃ t ≤ max a b + 2, ∃ w,
      ((advance (program A B O lt eq gt))^[t])
        (⟨some .loop, v, S⟩ : TM2.Cfg (fun _ : K => Bool) CL CV) =
      ⟨none, w, Function.update (Function.update (Function.update S A []) B [])
        O (verdict lt eq gt a b :: S O)⟩ := by
  have hBA : B ≠ A := Ne.symm hAB
  have hOA : O ≠ A := Ne.symm hAO
  have hOB : O ≠ B := Ne.symm hBO
  induction a generalizing S v b with
  | zero =>
      have hA0 : S A = [] := by simpa using hA
      have huA : Function.update S A [] = S := Function.update_eq_self_iff.mpr hA0.symm
      cases b with
      | zero =>
          have hB0 : S B = [] := by simpa using hB
          have huB : Function.update S B [] = S := Function.update_eq_self_iff.mpr hB0.symm
          refine ⟨1, by omega, (none, none), ?_⟩
          simp [advance, TM2.step, TM2.stepAux, program, hA0, hB0, verdict, huA, huB]
      | succ b =>
          have h1 : advance (program A B O lt eq gt)
              (⟨some .loop, v, S⟩ : TM2.Cfg (fun _ : K => Bool) CL CV) =
              ⟨some .drainB, (none, some true),
                Function.update (Function.update S B (List.replicate b true)) O
                  (lt :: S O)⟩ := by
            simp [advance, TM2.step, TM2.stepAux, program, hA0, hB, huA, List.replicate_succ,
              Function.update_of_ne hOB]
          obtain ⟨w, hw⟩ := drainB_run A B O lt eq gt
            (Function.update (Function.update S B (List.replicate b true)) O (lt :: S O))
            (none, some true) b
            (by rw [Function.update_of_ne hBO]; simp)
          refine ⟨b + 1 + 1, by omega, w, ?_⟩
          rw [Function.iterate_succ_apply, h1, hw]
          have hv : verdict lt eq gt 0 (b + 1) = lt := by simp [verdict]
          rw [hv, huA]
          congr 1
          funext k
          simp only [Function.update_apply]
          split_ifs <;> simp_all
  | succ a ih =>
      cases b with
      | zero =>
          have hB0 : S B = [] := by simpa using hB
          have h1 : advance (program A B O lt eq gt)
              (⟨some .loop, v, S⟩ : TM2.Cfg (fun _ : K => Bool) CL CV) =
              ⟨some .drainA, (some true, none),
                Function.update (Function.update S A (List.replicate a true)) O
                  (gt :: S O)⟩ := by
            have hu : Function.update (Function.update S A (List.replicate a true)) B [] =
                Function.update S A (List.replicate a true) := by
              apply Function.update_eq_self_iff.mpr
              rw [Function.update_of_ne hBA, hB0]
            simp [advance, TM2.step, TM2.stepAux, program, hA, hB0, hu, List.replicate_succ,
              Function.update_of_ne hOA, Function.update_of_ne hBA]
          obtain ⟨w, hw⟩ := drainA_run A B O lt eq gt
            (Function.update (Function.update S A (List.replicate a true)) O (gt :: S O))
            (some true, none) a
            (by rw [Function.update_of_ne hAO]; simp)
          refine ⟨a + 1 + 1, by omega, w, ?_⟩
          rw [Function.iterate_succ_apply, h1, hw]
          have hv : verdict lt eq gt (a + 1) 0 = gt := by simp [verdict]
          rw [hv]
          congr 1
          funext k
          simp only [Function.update_apply]
          split_ifs <;> simp_all
      | succ b =>
          have h1 : advance (program A B O lt eq gt)
              (⟨some .loop, v, S⟩ : TM2.Cfg (fun _ : K => Bool) CL CV) =
              ⟨some .loop, (some true, some true),
                Function.update (Function.update S A (List.replicate a true)) B
                  (List.replicate b true)⟩ := by
            simp [advance, TM2.step, TM2.stepAux, program, hA, hB, List.replicate_succ,
              Function.update_of_ne hBA]
          obtain ⟨t, ht, w, hw⟩ := ih
            (Function.update (Function.update S A (List.replicate a true)) B
              (List.replicate b true)) (some true, some true) b
            (by rw [Function.update_of_ne hAB]; simp) (by simp)
          refine ⟨t + 1, by omega, w, ?_⟩
          rw [Function.iterate_succ_apply, h1, hw]
          have hv : verdict lt eq gt (a + 1) (b + 1) = verdict lt eq gt a b := by
            simp [verdict]
          rw [hv]
          have hO : Function.update (Function.update S A (List.replicate a true)) B
              (List.replicate b true) O = S O := by
            rw [Function.update_of_ne hOB, Function.update_of_ne hOA]
          rw [hO]
          congr 1
          funext k
          simp only [Function.update_apply]
          split_ifs <;> simp_all

#print axioms drainA_run
#print axioms drainB_run
#print axioms compare_run

end EthInapproximability.CurrentPaper.EntryUnaryCompare
