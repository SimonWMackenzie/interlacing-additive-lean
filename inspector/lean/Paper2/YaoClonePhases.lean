import Paper2.YaoCloneProg

/-! Unit 5 segment Y10 (lane a-yao-clone-owner-1): the per-edge phases of the
physical clone machine and the edge loop.  Every run is stated on the whole
bank `bk ...` (all stacks named), with a charged transition bound. -/

namespace Paper2.YaoCloneMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoCloneSource
open Paper2.YaoSourceCodec

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

variable {K M : ℕ}

/-- All label/restore stacks empty. -/
abbrev E0 (K : ℕ) : Fin K → List Bool := fun _ => []

/-- The label stacks holding one edge's labels. -/
def labOf (l : Fin K → ℕ) : Fin K → List Bool := fun j => rep (l j)

theorem RIn.congr_bank {l : Lbl K M} {l' : Option (Lbl K M)} {S S₁ S₂ : Stk K → List Bool} {b : ℕ}
    (h : RIn l S l' S₁ b) (e : S₁ = S₂) : RIn l S l' S₂ b := e ▸ h

theorem rep_append_rep (a b : ℕ) : rep a ++ rep b = rep (a + b) := by
  simp only [rep, List.replicate_append_replicate]

theorem rep_append_cons (a : ℕ) (x : List Bool) : rep a ++ true :: x = rep (a + 1) ++ x := by
  simp [List.replicate_succ']

/-! ## Load one edge -/

section Load
variable (vm ec acc cnt out : List Bool) (res : Fin K → List Bool)

theorem tok_run (j : ℕ) (hj : j < K) (a : ℕ) : ∀ (R : List Bool) (lab : Fin K → List Bool),
    RIn (K := K) (M := M) (.load ⟨j, by omega⟩) (bk (rep a ++ false :: R) vm ec acc cnt out lab res)
      (some (.load ⟨j + 1, by omega⟩))
      (bk R vm ec acc cnt out (Function.update lab ⟨j, hj⟩ (rep a ++ lab ⟨j, hj⟩)) res) (a + 1) := by
  induction a with
  | zero =>
      intro R lab
      apply RIn.step
      intro σ
      simp [TM2.step, TM2.stepAux, program, hj]
  | succ a ih =>
      intro R lab
      have h := ih R (Function.update lab ⟨j, hj⟩ (true :: lab ⟨j, hj⟩))
      rw [Function.update_idem, Function.update_self, rep_append_cons] at h
      refine RIn.cons ?_ h
      intro σ
      simp [TM2.step, TM2.stepAux, program, hj, List.replicate_succ]

def labAt (l : Fin K → ℕ) (j : ℕ) : Fin K → List Bool :=
  fun j' => if j'.val < j then rep (l j') else []

theorem load_from (l : Fin K → ℕ) (V : ℕ) (hV : ∀ j, l j ≤ V) :
    ∀ (k j : ℕ) (hjk : j + k = K) (R : List Bool),
    RIn (K := K) (M := M) (.load ⟨j, by omega⟩)
      (bk (((List.ofFn fun j' : Fin K => field (l j')).drop j).flatten ++ R) vm ec acc cnt out
        (labAt l j) res)
      (some (.cmp (fun _ _ => false) 0)) (bk R vm ec acc cnt out (labOf l) res) (k * (V + 1) + 1) := by
  intro k
  induction k with
  | zero =>
      intro j hjk R
      have hj : j = K := by omega
      have hl : labAt l j = labOf l := by
        funext j'; simp [labAt, labOf, show j'.val < j by omega]
      have hd : (List.ofFn fun j' : Fin K => field (l j')).drop j = [] := by
        apply List.drop_of_length_le; simp; omega
      rw [hl, hd]
      refine (RIn.step ?_).mono (by omega)
      intro σ
      simp [TM2.step, TM2.stepAux, program, show ¬ j < K by omega]
  | succ k ih =>
      intro j hjk R
      have hj : j < K := by omega
      have hd : (List.ofFn fun j' : Fin K => field (l j')).drop j =
          field (l ⟨j, hj⟩) :: (List.ofFn fun j' : Fin K => field (l j')).drop (j + 1) := by
        rw [List.drop_eq_getElem_cons (by simp; omega)]
        simp
      have hlab : Function.update (labAt l j) ⟨j, hj⟩ (rep (l ⟨j, hj⟩) ++ labAt l j ⟨j, hj⟩) =
          labAt l (j + 1) := by
        funext j'
        by_cases hj' : j' = ⟨j, hj⟩
        · subst hj'; simp [labAt]
        · have hne : j'.val ≠ j := fun h => hj' (Fin.ext h)
          simp only [Function.update_apply, hj', if_false, labAt]
          by_cases hlt : j'.val < j
          · simp [hlt, show j'.val < j + 1 by omega]
          · simp [hlt, show ¬ j'.val < j + 1 by omega]
      rw [hd, List.flatten_cons, field, List.append_assoc, List.append_assoc, List.singleton_append]
      have h1 := tok_run (M := M) vm ec acc cnt out res j hj (l ⟨j, hj⟩)
        (((List.ofFn fun j' : Fin K => field (l j')).drop (j + 1)).flatten ++ R) (labAt l j)
      rw [hlab] at h1
      have h2 := ih (j + 1) (by omega) R
      refine (RIn.trans h1 h2).mono ?_
      have := hV ⟨j, hj⟩
      nlinarith

end Load

/-! ## Equality pattern: one pair -/

section Pair
variable (inp vm ec acc cnt out : List Bool)

theorem restI_run (P : Pat K) (q : Fin (K * K)) (i j : Fin K) (c : ℕ) :
    ∀ (lab res : Fin K → List Bool), res i = rep c →
    RIn (K := K) (M := M) (.restI P q i j) (bk inp vm ec acc cnt out lab res) (some (.restJ P q i j))
      (bk inp vm ec acc cnt out (Function.update lab i (rep c ++ lab i)) (Function.update res i []))
      (c + 1) := by
  induction c with
  | zero =>
      intro lab res hr
      apply RIn.step
      intro σ
      simp [TM2.step, TM2.stepAux, program, hr]
  | succ c ih =>
      intro lab res hr
      have h := ih (Function.update lab i (true :: lab i)) (Function.update res i (rep c)) (by simp)
      rw [Function.update_idem, Function.update_self, rep_append_cons, Function.update_idem] at h
      refine RIn.cons ?_ h
      intro σ
      simp [TM2.step, TM2.stepAux, program, hr, List.replicate_succ]

theorem restJ_run (P : Pat K) (q : Fin (K * K)) (i j : Fin K) (d : ℕ) :
    ∀ (lab res : Fin K → List Bool), res j = rep d →
    RIn (K := K) (M := M) (.restJ P q i j) (bk inp vm ec acc cnt out lab res)
      (some (.cmp P ⟨q.val + 1, by omega⟩))
      (bk inp vm ec acc cnt out (Function.update lab j (rep d ++ lab j)) (Function.update res j []))
      (d + 1) := by
  induction d with
  | zero =>
      intro lab res hr
      apply RIn.step
      intro σ
      simp [TM2.step, TM2.stepAux, program, hr]
  | succ d ih =>
      intro lab res hr
      have h := ih (Function.update lab j (true :: lab j)) (Function.update res j (rep d)) (by simp)
      rw [Function.update_idem, Function.update_self, rep_append_cons, Function.update_idem] at h
      refine RIn.cons ?_ h
      intro σ
      simp [TM2.step, TM2.stepAux, program, hr, List.replicate_succ]

macro "upd_ext" : tactic => `(tactic| (funext x; simp only [Function.update_apply]; split_ifs <;> simp_all [rep_append_rep, rep_append_cons, List.replicate_inj] <;> omega))

theorem cmpLoop_run (P : Pat K) (q : Fin (K * K)) (i j : Fin K) (hij : i ≠ j) (a : ℕ) :
    ∀ (b c d : ℕ) (lab res : Fin K → List Bool), lab i = rep a → lab j = rep b →
    res i = rep c → res j = rep d →
    RIn (K := K) (M := M) (.cmpLoop P q i j) (bk inp vm ec acc cnt out lab res)
      (some (.cmp (updP P i j (decide (a = b))) ⟨q.val + 1, by omega⟩))
      (bk inp vm ec acc cnt out (Function.update (Function.update lab i (rep (a + c))) j (rep (b + d)))
        (Function.update (Function.update res i []) j []))
      (3 * (a + b) + c + d + 3) := by
  have hji : j ≠ i := fun h => hij h.symm
  induction a with
  | zero =>
      intro b c d lab res hi hj hri hrj
      cases b with
      | zero =>
          have s1 : RIn (K := K) (M := M) (.cmpLoop P q i j) (bk inp vm ec acc cnt out lab res)
              (some (.restI (updP P i j true) q i j))
              (bk inp vm ec acc cnt out (Function.update (Function.update lab i []) j []) res) 1 := by
            apply RIn.step
            intro σ
            simp [TM2.step, TM2.stepAux, program, hi, hj, hij, hji]
          have s2 := restI_run (M := M) inp vm ec acc cnt out (updP P i j true) q i j c
            (Function.update (Function.update lab i []) j []) res hri
          have s3 := restJ_run (M := M) inp vm ec acc cnt out (updP P i j true) q i j d
            (Function.update (Function.update (Function.update lab i []) j []) i
              (rep c ++ Function.update (Function.update lab i []) j [] i))
            (Function.update res i []) (by simp [hji, hrj])
          have := (s1.trans s2).trans s3
          refine (RIn.congr_bank this ?_).mono (by omega)
          congr 1 <;> upd_ext
      | succ n =>
          have s1 : RIn (K := K) (M := M) (.cmpLoop P q i j) (bk inp vm ec acc cnt out lab res)
              (some (.restI (updP P i j false) q i j))
              (bk inp vm ec acc cnt out (Function.update (Function.update lab i []) j (rep n))
                (Function.update res j (true :: rep d))) 1 := by
            apply RIn.step
            intro σ
            simp [TM2.step, TM2.stepAux, program, hi, hj, hrj, hij, hji, List.replicate_succ]
          have s2 := restI_run (M := M) inp vm ec acc cnt out (updP P i j false) q i j c
            (Function.update (Function.update lab i []) j (rep n))
            (Function.update res j (true :: rep d)) (by simp [hij, hri])
          have s3 := restJ_run (M := M) inp vm ec acc cnt out (updP P i j false) q i j (d + 1)
            (Function.update (Function.update (Function.update lab i []) j (rep n)) i
              (rep c ++ Function.update (Function.update lab i []) j (rep n) i))
            (Function.update (Function.update res j (true :: rep d)) i []) (by
              simp [hji, List.replicate_succ])
          have := (s1.trans s2).trans s3
          have hd : decide (0 = n + 1) = false := by simp
          rw [hd]
          refine (RIn.congr_bank this ?_).mono (by omega)
          congr 1 <;> upd_ext
  | succ m ih =>
      intro b c d lab res hi hj hri hrj
      cases b with
      | zero =>
          have s1 : RIn (K := K) (M := M) (.cmpLoop P q i j) (bk inp vm ec acc cnt out lab res)
              (some (.restI (updP P i j false) q i j))
              (bk inp vm ec acc cnt out (Function.update (Function.update lab i (rep m)) j [])
                (Function.update res i (true :: rep c))) 1 := by
            apply RIn.step
            intro σ
            simp [TM2.step, TM2.stepAux, program, hi, hj, hri, hij, hji, List.replicate_succ]
          have s2 := restI_run (M := M) inp vm ec acc cnt out (updP P i j false) q i j (c + 1)
            (Function.update (Function.update lab i (rep m)) j [])
            (Function.update res i (true :: rep c)) (by simp [List.replicate_succ])
          have s3 := restJ_run (M := M) inp vm ec acc cnt out (updP P i j false) q i j d
            (Function.update (Function.update (Function.update lab i (rep m)) j []) i
              (rep (c + 1) ++ Function.update (Function.update lab i (rep m)) j [] i))
            (Function.update (Function.update res i (true :: rep c)) i []) (by simp [hji, hrj])
          have := (s1.trans s2).trans s3
          have hd : decide (m + 1 = 0) = false := by simp
          rw [hd]
          refine (RIn.congr_bank this ?_).mono (by omega)
          congr 1 <;> upd_ext
      | succ n =>
          have s1 : RIn (K := K) (M := M) (.cmpLoop P q i j) (bk inp vm ec acc cnt out lab res)
              (some (.cmpLoop P q i j))
              (bk inp vm ec acc cnt out (Function.update (Function.update lab i (rep m)) j (rep n))
                (Function.update (Function.update res i (true :: rep c)) j (true :: rep d))) 1 := by
            apply RIn.step
            intro σ
            simp [TM2.step, TM2.stepAux, program, hi, hj, hri, hrj, hij, hji, List.replicate_succ]
          have s2 := ih n (c + 1) (d + 1)
            (Function.update (Function.update lab i (rep m)) j (rep n))
            (Function.update (Function.update res i (true :: rep c)) j (true :: rep d))
            (by simp [hij]) (by simp) (by simp [hij, List.replicate_succ])
            (by simp [List.replicate_succ])
          have := s1.trans s2
          have hd : decide (m = n) = decide (m + 1 = n + 1) := by simp
          rw [hd] at this
          refine (RIn.congr_bank this ?_).mono (by omega)
          congr 1 <;> upd_ext

end Pair

end Paper2.YaoCloneMachine
