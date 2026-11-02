import Paper2.YaoClonePhases

/-! Unit 5 segment Y10 (lane a-yao-clone-owner-1): the equality-pattern loop,
the lift printing loop, the clearing loop and the edge loop of the physical
clone machine.  Whole-bank statements with charged transition bounds. -/

namespace Paper2.YaoCloneMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoCloneSource
open Paper2.YaoSourceCodec

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

variable {K M : ℕ}

/-! ## Equality pattern: all pairs -/

section Pattern
variable (inp vm ec acc cnt out : List Bool)

theorem pairAt_spec (q : Fin (K * K)) (i j : Fin K) :
    pairAt q = (i, j) ↔ (finProdFinEquiv (i, j)).val = q.val := by
  unfold pairAt
  rw [Equiv.symm_apply_eq]
  exact ⟨fun h => by rw [← h], fun h => Fin.ext h.symm⟩

theorem agree_step (l : Fin K → ℕ) (P : Pat K) (q : ℕ) (hq : q < K * K) (b : Bool)
    (hb : b = eqPat l (pairAt ⟨q, hq⟩).1 (pairAt ⟨q, hq⟩).2)
    (hP : ∀ i j, (finProdFinEquiv (i, j)).val < q → P i j = eqPat l i j) :
    ∀ i j, (finProdFinEquiv (i, j)).val < q + 1 →
      updP P (pairAt ⟨q, hq⟩).1 (pairAt ⟨q, hq⟩).2 b i j = eqPat l i j := by
  intro i j h
  by_cases hq' : (finProdFinEquiv (i, j)).val = q
  · have hp : pairAt ⟨q, hq⟩ = (i, j) := (pairAt_spec _ i j).2 hq'
    rw [hp] at hb ⊢
    simp [updP, hb]
  · have hlt : (finProdFinEquiv (i, j)).val < q := by omega
    have hne : ¬ (i = (pairAt ⟨q, hq⟩).1 ∧ j = (pairAt ⟨q, hq⟩).2) := by
      rintro ⟨h1, h2⟩
      apply hq'
      have hp : pairAt ⟨q, hq⟩ = (i, j) := by rw [h1, h2]
      exact (pairAt_spec _ i j).1 hp
    unfold updP
    by_cases h1 : i = (pairAt ⟨q, hq⟩).1
    · have h2 : j ≠ (pairAt ⟨q, hq⟩).2 := fun h2 => hne ⟨h1, h2⟩
      subst h1
      simp only [Function.update_self, Function.update_of_ne h2]
      exact hP _ _ hlt
    · simp only [Function.update_of_ne h1]
      exact hP _ _ hlt

theorem cmp_from (l : Fin K → ℕ) (V : ℕ) (hV : ∀ j, l j ≤ V) :
    ∀ (k q : ℕ) (hq : q + k = K * K) (P : Pat K),
    (∀ i j, (finProdFinEquiv (i, j)).val < q → P i j = eqPat l i j) →
    RIn (K := K) (M := M) (.cmp P ⟨q, by omega⟩) (bk inp vm ec acc cnt out (labOf l) (E0 K))
      (some (.lift (eqPat l) 0)) (bk inp vm ec acc cnt out (labOf l) (E0 K)) (k * (6 * V + 4) + 1) := by
  intro k
  induction k with
  | zero =>
      intro q hq P hP
      have hPe : P = eqPat l := by
        funext i j
        exact hP i j (by have := (finProdFinEquiv (i, j)).isLt; omega)
      subst hPe
      refine (RIn.step ?_).mono (by omega)
      intro σ
      simp [TM2.step, TM2.stepAux, program, show ¬ q < K * K by omega]
  | succ k ih =>
      intro q hq P hP
      have hqK : q < K * K := by omega
      by_cases hij : (pairAt ⟨q, hqK⟩).1 = (pairAt ⟨q, hqK⟩).2
      · have h1 : RIn (K := K) (M := M) (.cmp P ⟨q, by omega⟩)
            (bk inp vm ec acc cnt out (labOf l) (E0 K))
            (some (.cmp (updP P (pairAt ⟨q, hqK⟩).1 (pairAt ⟨q, hqK⟩).2 true) ⟨q + 1, by omega⟩))
            (bk inp vm ec acc cnt out (labOf l) (E0 K)) 1 := by
          apply RIn.step
          intro σ
          simp [TM2.step, TM2.stepAux, program, hqK, hij]
        have h2 := ih (q + 1) (by omega) _ (agree_step l P q hqK true
          (by simp [eqPat, hij]) hP)
        exact (h1.trans h2).mono (by nlinarith)
      · have h1 : RIn (K := K) (M := M) (.cmp P ⟨q, by omega⟩)
            (bk inp vm ec acc cnt out (labOf l) (E0 K))
            (some (.cmpLoop P ⟨q, hqK⟩ (pairAt ⟨q, hqK⟩).1 (pairAt ⟨q, hqK⟩).2))
            (bk inp vm ec acc cnt out (labOf l) (E0 K)) 1 := by
          apply RIn.step
          intro σ
          simp [TM2.step, TM2.stepAux, program, hqK, hij]
        have h2 := cmpLoop_run (M := M) inp vm ec acc cnt out P ⟨q, hqK⟩ _ _ hij
          (l (pairAt ⟨q, hqK⟩).1) (l (pairAt ⟨q, hqK⟩).2) 0 0 (labOf l) (E0 K) rfl rfl rfl rfl
        have e1 : Function.update (Function.update (labOf l) (pairAt ⟨q, hqK⟩).1
            (rep (l (pairAt ⟨q, hqK⟩).1 + 0))) (pairAt ⟨q, hqK⟩).2 (rep (l (pairAt ⟨q, hqK⟩).2 + 0))
            = labOf l := by
          funext x; simp only [Function.update_apply]; split_ifs <;> simp_all [labOf]
        have e2 : Function.update (Function.update (E0 K) (pairAt ⟨q, hqK⟩).1 [])
            (pairAt ⟨q, hqK⟩).2 [] = E0 K := by
          funext x; simp only [Function.update_apply]; split_ifs <;> rfl
        rw [e1, e2] at h2
        have h3 := ih (q + 1) (by omega) _ (agree_step l P q hqK
          (decide (l (pairAt ⟨q, hqK⟩).1 = l (pairAt ⟨q, hqK⟩).2)) rfl hP)
        have hb1 := hV (pairAt ⟨q, hqK⟩).1
        have hb2 := hV (pairAt ⟨q, hqK⟩).2
        exact ((h1.trans h2).trans h3).mono (by nlinarith)

end Pattern

/-! ## Printing one lift -/

section Print
variable (inp vm ec cnt out : List Bool)

theorem rs_run (P : Pat K) (n : Fin (M ^ K)) (r : Fin K → Fin M) (jj : Fin K) (acc : List Bool)
    (c : ℕ) : ∀ (lab res : Fin K → List Bool), res jj = rep c →
    RIn (K := K) (M := M) (.rs P n r jj) (bk inp vm ec acc cnt out lab res)
      (some (.pr P n r ⟨jj.val + 1, by omega⟩))
      (bk inp vm ec acc cnt out (Function.update lab jj (rep c ++ lab jj)) (Function.update res jj []))
      (c + 1) := by
  induction c with
  | zero =>
      intro lab res hr
      apply RIn.step
      intro σ
      simp [TM2.step, TM2.stepAux, program, hr]
  | succ c ih =>
      intro lab res hr
      have h := ih (Function.update lab jj (true :: lab jj)) (Function.update res jj (rep c)) (by simp)
      rw [Function.update_idem, Function.update_self, rep_append_cons, Function.update_idem] at h
      refine RIn.cons ?_ h
      intro σ
      simp [TM2.step, TM2.stepAux, program, hr, List.replicate_succ]

theorem field_run (P : Pat K) (n : Fin (M ^ K)) (r : Fin K → Fin M) (j : ℕ) (hj : j < K) (a : ℕ) :
    ∀ (c : ℕ) (acc : List Bool) (lab res : Fin K → List Bool),
    lab ⟨j, hj⟩ = rep a → res ⟨j, hj⟩ = rep c →
    RIn (K := K) (M := M) (.pr P n r ⟨j, by omega⟩) (bk inp vm ec acc cnt out lab res)
      (some (.pr P n r ⟨j + 1, by omega⟩))
      (bk inp vm ec (false :: (rep (a * M + (r ⟨j, hj⟩).val) ++ acc)) cnt out
        (Function.update lab ⟨j, hj⟩ (rep (a + c))) (Function.update res ⟨j, hj⟩ []))
      (2 * a + c + 2) := by
  induction a with
  | zero =>
      intro c acc lab res hl hr
      have s1 : RIn (K := K) (M := M) (.pr P n r ⟨j, by omega⟩) (bk inp vm ec acc cnt out lab res)
          (some (.rs P n r ⟨j, hj⟩))
          (bk inp vm ec (false :: (rep (r ⟨j, hj⟩).val ++ acc)) cnt out
            (Function.update lab ⟨j, hj⟩ []) res) 1 := by
        apply RIn.step
        intro σ
        simp [TM2.step, TM2.stepAux, program, hj, hl, pushN_stepAux]
      have s2 := rs_run (M := M) inp vm ec cnt out P n r ⟨j, hj⟩
        (false :: (rep (r ⟨j, hj⟩).val ++ acc)) c (Function.update lab ⟨j, hj⟩ []) res hr
      have := s1.trans s2
      refine (RIn.congr_bank this ?_).mono (by omega)
      simp [Function.update_idem]
  | succ m ih =>
      intro c acc lab res hl hr
      have s1 : RIn (K := K) (M := M) (.pr P n r ⟨j, by omega⟩) (bk inp vm ec acc cnt out lab res)
          (some (.pr P n r ⟨j, by omega⟩))
          (bk inp vm ec (rep M ++ acc) cnt out (Function.update lab ⟨j, hj⟩ (rep m))
            (Function.update res ⟨j, hj⟩ (rep (c + 1)))) 1 := by
        apply RIn.step
        intro σ
        simp [TM2.step, TM2.stepAux, program, hj, hl, hr, pushN_stepAux, List.replicate_succ,
          List.replicate_succ']
      have s2 := ih (c + 1) (rep M ++ acc) (Function.update lab ⟨j, hj⟩ (rep m))
        (Function.update res ⟨j, hj⟩ (rep (c + 1))) (by simp) (by simp)
      have := s1.trans s2
      refine (RIn.congr_bank this ?_).mono (by omega)
      have ha : rep (m * M + (r ⟨j, hj⟩).val) ++ (rep M ++ acc) =
          rep ((m + 1) * M + (r ⟨j, hj⟩).val) ++ acc := by
        rw [← List.append_assoc, rep_append_rep, Nat.succ_mul]
        congr 2
        omega
      rw [ha, Function.update_idem, Function.update_idem, show m + (c + 1) = m + 1 + c by omega]

theorem pr_from (l : Fin K → ℕ) (V : ℕ) (hV : ∀ j, l j ≤ V) (P : Pat K) (n : Fin (M ^ K))
    (r : Fin K → Fin M) :
    ∀ (k j : ℕ) (hjk : j + k = K) (acc : List Bool),
    RIn (K := K) (M := M) (.pr P n r ⟨j, by omega⟩) (bk inp vm ec acc cnt out (labOf l) (E0 K))
      (some (.lift P ⟨n.val + 1, by omega⟩))
      (bk inp vm ec
        ((((List.ofFn fun j' : Fin K => field (l j' * M + (r j').val)).drop j).flatten).reverse ++ acc)
        cnt out (labOf l) (E0 K)) (k * (2 * V + 2) + 1) := by
  intro k
  induction k with
  | zero =>
      intro j hjk acc
      have hd : (List.ofFn fun j' : Fin K => field (l j' * M + (r j').val)).drop j = [] := by
        apply List.drop_of_length_le; simp; omega
      rw [hd]
      refine (RIn.step ?_).mono (by omega)
      intro σ
      simp [TM2.step, TM2.stepAux, program, show ¬ j < K by omega]
  | succ k ih =>
      intro j hjk acc
      have hj : j < K := by omega
      have hd : (List.ofFn fun j' : Fin K => field (l j' * M + (r j').val)).drop j =
          field (l ⟨j, hj⟩ * M + (r ⟨j, hj⟩).val) ::
            (List.ofFn fun j' : Fin K => field (l j' * M + (r j').val)).drop (j + 1) := by
        rw [List.drop_eq_getElem_cons (by simp; omega)]
        simp
      have h1 := field_run (M := M) inp vm ec cnt out P n r j hj (l ⟨j, hj⟩) 0 acc (labOf l) (E0 K)
        rfl rfl
      have e1 : Function.update (labOf l) ⟨j, hj⟩ (rep (l ⟨j, hj⟩ + 0)) = labOf l := by
        funext x; simp only [Function.update_apply]; split_ifs <;> simp_all [labOf]
      have e2 : Function.update (E0 K) ⟨j, hj⟩ [] = E0 K := by
        funext x; simp only [Function.update_apply]; split_ifs <;> rfl
      rw [e1, e2] at h1
      have h2 := ih (j + 1) (by omega) (false :: (rep (l ⟨j, hj⟩ * M + (r ⟨j, hj⟩).val) ++ acc))
      rw [hd, List.flatten_cons, List.reverse_append, field]
      have hr : (rep (l ⟨j, hj⟩ * M + (r ⟨j, hj⟩).val) ++ [false]).reverse ++ acc =
          false :: (rep (l ⟨j, hj⟩ * M + (r ⟨j, hj⟩).val) ++ acc) := by
        simp [List.reverse_replicate]
      rw [List.append_assoc, hr]
      have := hV ⟨j, hj⟩
      exact (h1.trans h2).mono (by nlinarith)

end Print

/-! ## The lift loop -/

section Lifts
variable (inp vm ec out : List Bool)

theorem allFuns_drop (n : ℕ) (hn : n < M ^ K) :
    (allFuns M K).drop n = liftAt (K := K) (M := M) ⟨n, hn⟩ :: (allFuns M K).drop (n + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [length_allFuns]; exact hn)]
  rfl

theorem lift_from (l : Fin K → ℕ) (V : ℕ) (hV : ∀ j, l j ≤ V) :
    ∀ (k n : ℕ) (hn : n + k = M ^ K) (acc cnt : List Bool),
    RIn (K := K) (M := M) (.lift (eqPat l) ⟨n, by omega⟩) (bk inp vm ec acc cnt out (labOf l) (E0 K))
      (some (.clr 0))
      (bk inp vm ec (((((allFuns M K).drop n).filter (injB (eqPat l))).flatMap (liftBlock M l)).reverse
          ++ acc)
        (rep (((allFuns M K).drop n).filter (injB (eqPat l))).length ++ cnt) out (labOf l) (E0 K))
      (k * (K * (2 * V + 2) + 3) + 1) := by
  intro k
  induction k with
  | zero =>
      intro n hn acc cnt
      have hd : (allFuns M K).drop n = [] := by
        apply List.drop_of_length_le; rw [length_allFuns]; omega
      rw [hd]
      refine (RIn.step ?_).mono (by omega)
      intro σ
      simp [TM2.step, TM2.stepAux, program, show ¬ n < M ^ K by omega]
  | succ k ih =>
      intro n hn acc cnt
      have hnK : n < M ^ K := by omega
      rw [allFuns_drop n hnK]
      by_cases hinj : injB (eqPat l) (liftAt (K := K) (M := M) ⟨n, hnK⟩) = true
      · have h1 : RIn (K := K) (M := M) (.lift (eqPat l) ⟨n, by omega⟩)
            (bk inp vm ec acc cnt out (labOf l) (E0 K))
            (some (.pr (eqPat l) ⟨n, hnK⟩ (liftAt ⟨n, hnK⟩) 0))
            (bk inp vm ec acc (true :: cnt) out (labOf l) (E0 K)) 1 := by
          apply RIn.step
          intro σ
          simp [TM2.step, TM2.stepAux, program, hnK, hinj]
        have h2 := pr_from (M := M) inp vm ec (true :: cnt) out l V hV (eqPat l) ⟨n, hnK⟩
          (liftAt ⟨n, hnK⟩) K 0 (by omega) acc
        have := (h1.trans h2).trans (ih (n + 1) (by omega) _ (true :: cnt))
        refine (RIn.congr_bank this ?_).mono (by nlinarith)
        rw [List.filter_cons_of_pos hinj, List.flatMap_cons, List.length_cons]
        simp only [List.drop_zero, liftBlock, List.reverse_append, List.append_assoc]
        congr 1
        simp [List.replicate_succ']
      · have h1 : RIn (K := K) (M := M) (.lift (eqPat l) ⟨n, by omega⟩)
            (bk inp vm ec acc cnt out (labOf l) (E0 K))
            (some (.lift (eqPat l) ⟨n + 1, by omega⟩))
            (bk inp vm ec acc cnt out (labOf l) (E0 K)) 1 := by
          apply RIn.step
          intro σ
          simp [TM2.step, TM2.stepAux, program, hnK, hinj]
        have h3 := ih (n + 1) (by omega) acc cnt
        have := h1.trans h3
        refine (RIn.congr_bank this ?_).mono (by nlinarith)
        rw [List.filter_cons_of_neg hinj]

end Lifts

/-! ## Clearing the labels -/

section Clear
variable (inp vm ec acc cnt out : List Bool) (res : Fin K → List Bool)

theorem clrTok_run (j : ℕ) (hj : j < K) (a : ℕ) : ∀ (lab : Fin K → List Bool), lab ⟨j, hj⟩ = rep a →
    RIn (K := K) (M := M) (.clr ⟨j, by omega⟩) (bk inp vm ec acc cnt out lab res)
      (some (.clr ⟨j + 1, by omega⟩)) (bk inp vm ec acc cnt out (Function.update lab ⟨j, hj⟩ []) res)
      (a + 1) := by
  induction a with
  | zero =>
      intro lab hl
      apply RIn.step
      intro σ
      simp [TM2.step, TM2.stepAux, program, hj, hl]
  | succ a ih =>
      intro lab hl
      have h := ih (Function.update lab ⟨j, hj⟩ (rep a)) (by simp)
      rw [Function.update_idem] at h
      refine RIn.cons ?_ h
      intro σ
      simp [TM2.step, TM2.stepAux, program, hj, hl, List.replicate_succ]

def labFrom (l : Fin K → ℕ) (j : ℕ) : Fin K → List Bool :=
  fun j' => if j'.val < j then [] else rep (l j')

theorem clr_from (l : Fin K → ℕ) (V : ℕ) (hV : ∀ j, l j ≤ V) :
    ∀ (k j : ℕ) (hjk : j + k = K),
    RIn (K := K) (M := M) (.clr ⟨j, by omega⟩) (bk inp vm ec acc cnt out (labFrom l j) res)
      (some .edge) (bk inp vm ec acc cnt out (E0 K) res) (k * (V + 1) + 1) := by
  intro k
  induction k with
  | zero =>
      intro j hjk
      have hl : labFrom l j = E0 K := by
        funext j'; simp [labFrom, show j'.val < j by omega]
      rw [hl]
      refine (RIn.step ?_).mono (by omega)
      intro σ
      simp [TM2.step, TM2.stepAux, program, show ¬ j < K by omega]
  | succ k ih =>
      intro j hjk
      have hj : j < K := by omega
      have h1 := clrTok_run (M := M) inp vm ec acc cnt out res j hj (l ⟨j, hj⟩) (labFrom l j)
        (by simp [labFrom])
      have hlab : Function.update (labFrom l j) ⟨j, hj⟩ [] = labFrom l (j + 1) := by
        funext j'
        by_cases hj' : j' = ⟨j, hj⟩
        · subst hj'; simp [labFrom]
        · have hne : j'.val ≠ j := fun h => hj' (Fin.ext h)
          simp only [Function.update_apply, hj', if_false, labFrom]
          by_cases hlt : j'.val < j
          · simp [hlt, show j'.val < j + 1 by omega]
          · simp [hlt, show ¬ j'.val < j + 1 by omega]
      rw [hlab] at h1
      have h2 := ih (j + 1) (by omega)
      have := hV ⟨j, hj⟩
      exact (h1.trans h2).mono (by nlinarith)

end Clear

/-! ## One edge, and the edge loop -/

/-- Transition charge of one edge, for labels bounded by `V`. -/
def edgeCost (K M V : ℕ) : ℕ :=
  1 + (K * (V + 1) + 1) + (K * K * (6 * V + 4) + 1) + (M ^ K * (K * (2 * V + 2) + 3) + 1) +
    (K * (V + 1) + 1)

theorem edge_run (vm : List Bool) (V : ℕ) :
    ∀ (ls : List (Fin K → ℕ)), (∀ l ∈ ls, ∀ j, l j ≤ V) → ∀ (rest acc cnt : List Bool),
    RIn (K := K) (M := M) .edge
      (bk (ls.flatMap edgeInput ++ rest) vm (rep ls.length) acc cnt [] (E0 K) (E0 K))
      (some .fin1)
      (bk rest vm [] ((ls.flatMap (edgeBlock M)).reverse ++ acc)
        (rep (ls.map (fun l => (goodLifts M l).length)).sum ++ cnt) [] (E0 K) (E0 K))
      (ls.length * edgeCost K M V + 1)
  | [], _, rest, acc, cnt => by
      simp only [List.flatMap_nil, List.nil_append, List.length_nil, List.map_nil, List.sum_nil,
        List.reverse_nil, rep, List.replicate_zero, zero_mul, zero_add]
      apply RIn.step
      intro σ
      simp [TM2.step, TM2.stepAux, program]
  | l :: ls, hV, rest, acc, cnt => by
      have hl : ∀ j, l j ≤ V := hV l (by simp)
      have hls : ∀ l' ∈ ls, ∀ j, l' j ≤ V := fun l' h => hV l' (by simp [h])
      have h0 : RIn (K := K) (M := M) .edge
          (bk ((l :: ls).flatMap edgeInput ++ rest) vm (rep (l :: ls).length) acc cnt [] (E0 K) (E0 K))
          (some (.load 0))
          (bk (edgeInput l ++ (ls.flatMap edgeInput ++ rest)) vm (rep ls.length) acc cnt []
            (labAt l 0) (E0 K)) 1 := by
        have hz : labAt l 0 = E0 K := by funext j'; simp [labAt]
        rw [hz]
        apply RIn.step
        intro σ
        simp [TM2.step, TM2.stepAux, program, List.replicate_succ]
      have h1 := load_from (M := M) vm (rep ls.length) acc cnt [] (E0 K) l V hl K 0 (by omega)
        (ls.flatMap edgeInput ++ rest)
      simp only [List.drop_zero] at h1
      have h2 := cmp_from (M := M) (ls.flatMap edgeInput ++ rest) vm (rep ls.length) acc cnt [] l V hl
        (K * K) 0 (by omega) (fun _ _ => false) (fun i j h => by omega)
      have h3 := lift_from (M := M) (ls.flatMap edgeInput ++ rest) vm (rep ls.length) [] l V hl
        (M ^ K) 0 (by omega) acc cnt
      simp only [List.drop_zero] at h3
      have hlf : labOf l = labFrom l 0 := by funext j'; simp [labOf, labFrom]
      have h4 := clr_from (M := M) (ls.flatMap edgeInput ++ rest) vm (rep ls.length)
        ((((allFuns M K).filter (injB (eqPat l))).flatMap (liftBlock M l)).reverse ++ acc)
        (rep ((allFuns M K).filter (injB (eqPat l))).length ++ cnt) [] (E0 K) l V hl K 0 (by omega)
      rw [← hlf] at h4
      have h5 := edge_run vm V ls hls rest
        ((((allFuns M K).filter (injB (eqPat l))).flatMap (liftBlock M l)).reverse ++ acc)
        (rep ((allFuns M K).filter (injB (eqPat l))).length ++ cnt)
      have := ((((h0.trans h1).trans h2).trans h3).trans h4).trans h5
      refine (RIn.congr_bank this ?_).mono ?_
      · simp only [List.flatMap_cons, List.reverse_append, List.append_assoc, List.map_cons,
          List.sum_cons, edgeBlock, goodLifts]
        rw [← List.append_assoc (rep _) (rep _) cnt, rep_append_rep,
          Nat.add_comm (List.map _ ls).sum]
      · simp only [List.length_cons, edgeCost]
        nlinarith

end Paper2.YaoCloneMachine
