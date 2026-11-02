import Paper2.ThrProducer

/-! Unit 3, segment (5): the run of the threshold producer `ThrProducer.thrProg`. -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384

namespace Paper2.ThrProducer

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

def logBd (n : ℕ) : ℕ := 2 * n + 2 + (UnaryBinaryEncoding.coefficient + 6) * (n + 1) ^ 2

/-- The accumulated per-level word length. -/
def Xv (v : Fin 5 → ℕ) : ℕ :=
  Nat.clog 2 (v 4) + (Nat.clog 2 (v 3) + (Nat.clog 2 (v 1) + (Nat.clog 2 (v 2) +
    Nat.clog 2 (v 1))))

def thrBd (k : ℕ) (v : Fin 5 → ℕ) : ℕ :=
  logBd (v 0) + logBd (v 1) + logBd (v 2) + logBd (v 3) + logBd (v 4) +
    6 * (2 * (Nat.clog 2 (v 0) + Xv v) + 4) + 1 + (k * (2 * Xv v + 4 + 2) + 1) + 12

theorem thr_run (k : ℕ) (v : Fin 5 → ℕ) :
    ∃ t ≤ thrBd k v, ∃ vc, ∃ F : TK → List Bool,
      ((advance thrProg)^[t])
          (⟨some thrStart, thrCtl, T0 k v⟩ : TM2.Cfg (fun _ : TK => Bool) _ _) =
        ⟨none, vc, F⟩ ∧
      F thrC = u (k * Xv v + (Nat.clog 2 (v 0) + 1)) ∧ F xC = u (Xv v) ∧ F ctrC = [] ∧
      F scrC = [] ∧ (∀ i, F (outI i) = u (Nat.clog 2 (v i))) ∧ (∀ i, F (srcI i) = u (v i)) := by
  -- (1) five log runs
  obtain ⟨t1, ht1, e1, r1, o1, s1⟩ := log_lift 0 (T0 k v) (v 0) (fun x => rfl)
  let B1 := bank (ιR 0) (T0 k v) (ETHParameterScaleMachineLogCopy.afterLog (u (v 0)) e1).stk
  obtain ⟨t2, ht2, e2, r2, o2, s2⟩ := log_lift 1 B1 (v 1)
    (fun x => by simp only [B1]; rw [bank_ne _ _ _ _ _ (by decide)]; rfl)
  let B2 := bank (ιR 1) B1 (ETHParameterScaleMachineLogCopy.afterLog (u (v 1)) e2).stk
  obtain ⟨t3, ht3, e3, r3, o3, s3⟩ := log_lift 2 B2 (v 2)
    (fun x => by simp only [B2, B1]; rw [bank_ne _ _ _ _ _ (by decide), bank_ne _ _ _ _ _ (by decide)]; rfl)
  let B3 := bank (ιR 2) B2 (ETHParameterScaleMachineLogCopy.afterLog (u (v 2)) e3).stk
  obtain ⟨t4, ht4, e4, r4, o4, s4⟩ := log_lift 3 B3 (v 3)
    (fun x => by
      simp only [B3, B2, B1]
      rw [bank_ne _ _ _ _ _ (by decide), bank_ne _ _ _ _ _ (by decide),
        bank_ne _ _ _ _ _ (by decide)]; rfl)
  let B4 := bank (ιR 3) B3 (ETHParameterScaleMachineLogCopy.afterLog (u (v 3)) e4).stk
  obtain ⟨t5, ht5, e5, r5, o5, s5⟩ := log_lift 4 B4 (v 4)
    (fun x => by
      simp only [B4, B3, B2, B1]
      rw [bank_ne _ _ _ _ _ (by decide), bank_ne _ _ _ _ _ (by decide),
        bank_ne _ _ _ _ _ (by decide), bank_ne _ _ _ _ _ (by decide)]; rfl)
  let B5 := bank (ιR 4) B4 (ETHParameterScaleMachineLogCopy.afterLog (u (v 4)) e5).stk
  have hinl : ∀ a : Fin 4, B5 (.inl a) = T0 k v (.inl a) := by
    intro a
    simp only [B5, B4, B3, B2, B1, bank_inl]
  have hout : ∀ i : Fin 5, B5 (outI i) = u (Nat.clog 2 (v i)) := by
    intro i
    fin_cases i
    · change B5 (.inr (0, _)) = _
      simp only [B5, B4, B3, B2, bank_ne _ _ _ _ _ (by decide : (0 : Fin 5) ≠ 4),
        bank_ne _ _ _ _ _ (by decide : (0 : Fin 5) ≠ 3),
        bank_ne _ _ _ _ _ (by decide : (0 : Fin 5) ≠ 2),
        bank_ne _ _ _ _ _ (by decide : (0 : Fin 5) ≠ 1)]
      exact o1
    · change B5 (.inr (1, _)) = _
      simp only [B5, B4, B3, bank_ne _ _ _ _ _ (by decide : (1 : Fin 5) ≠ 4),
        bank_ne _ _ _ _ _ (by decide : (1 : Fin 5) ≠ 3),
        bank_ne _ _ _ _ _ (by decide : (1 : Fin 5) ≠ 2)]
      exact o2
    · change B5 (.inr (2, _)) = _
      simp only [B5, B4, bank_ne _ _ _ _ _ (by decide : (2 : Fin 5) ≠ 4),
        bank_ne _ _ _ _ _ (by decide : (2 : Fin 5) ≠ 3)]
      exact o3
    · change B5 (.inr (3, _)) = _
      simp only [B5, bank_ne _ _ _ _ _ (by decide : (3 : Fin 5) ≠ 4)]
      exact o4
    · exact o5
  have hsrc : ∀ i : Fin 5, B5 (srcI i) = u (v i) := by
    intro i
    fin_cases i
    · change B5 (.inr (0, _)) = _
      simp only [B5, B4, B3, B2, bank_ne _ _ _ _ _ (by decide : (0 : Fin 5) ≠ 4),
        bank_ne _ _ _ _ _ (by decide : (0 : Fin 5) ≠ 3),
        bank_ne _ _ _ _ _ (by decide : (0 : Fin 5) ≠ 2),
        bank_ne _ _ _ _ _ (by decide : (0 : Fin 5) ≠ 1)]
      exact s1
    · change B5 (.inr (1, _)) = _
      simp only [B5, B4, B3, bank_ne _ _ _ _ _ (by decide : (1 : Fin 5) ≠ 4),
        bank_ne _ _ _ _ _ (by decide : (1 : Fin 5) ≠ 3),
        bank_ne _ _ _ _ _ (by decide : (1 : Fin 5) ≠ 2)]
      exact s2
    · change B5 (.inr (2, _)) = _
      simp only [B5, B4, bank_ne _ _ _ _ _ (by decide : (2 : Fin 5) ≠ 4),
        bank_ne _ _ _ _ _ (by decide : (2 : Fin 5) ≠ 3)]
      exact s3
    · change B5 (.inr (3, _)) = _
      simp only [B5, bank_ne _ _ _ _ _ (by decide : (3 : Fin 5) ≠ 4)]
      exact s4
    · exact s5
  -- ne facts
  have tc : thrC ≠ ctrC := by simp [thrC, ctrC]
  have tx : thrC ≠ xC := by simp [thrC, xC]
  have cx : ctrC ≠ xC := by simp [ctrC, xC]
  have zx : scrC ≠ xC := by simp [scrC, xC]
  have zt : scrC ≠ thrC := by simp [scrC, thrC]
  have zc : scrC ≠ ctrC := by simp [scrC, ctrC]
  have ox : ∀ i, outI i ≠ xC := fun i => by simp [outI, xC]
  have ot : ∀ i, outI i ≠ thrC := fun i => by simp [outI, thrC]
  have oc' : ∀ i, outI i ≠ ctrC := fun i => by simp [outI, ctrC]
  have sx : ∀ i, srcI i ≠ xC := fun i => by simp [srcI, xC]
  have st : ∀ i, srcI i ≠ thrC := fun i => by simp [srcI, thrC]
  have sc : ∀ i, srcI i ≠ ctrC := fun i => by simp [srcI, ctrC]
  have hz5 : B5 scrC = [] := hinl 3
  have hx5 : B5 xC = [] := hinl 1
  have ht5 : B5 thrC = [] := hinl 0
  have hc5 : B5 ctrC = u k := hinl 2
  -- (2) five copies into X
  obtain ⟨u1, hu1, w1, q1⟩ := cp_run (outI 1) xC n01 (sO 1) sX B5 hz5
  let C1 := Function.update B5 xC (B5 (outI 1) ++ B5 xC)
  have hC1 : ∀ y, y ≠ xC → C1 y = B5 y := fun y hy => Function.update_of_ne hy _ _
  obtain ⟨u2, hu2, w2, q2⟩ := cp_run (outI 2) xC n02 (sO 2) sX C1
    (by rw [hC1 _ zx]; exact hz5)
  let C2 := Function.update C1 xC (C1 (outI 2) ++ C1 xC)
  have hC2 : ∀ y, y ≠ xC → C2 y = B5 y := fun y hy =>
    (Function.update_of_ne hy _ _).trans (hC1 y hy)
  obtain ⟨u3, hu3, w3, q3⟩ := cp_run (outI 1) xC n01 (sO 1) sX C2
    (by rw [hC2 _ zx]; exact hz5)
  let C3 := Function.update C2 xC (C2 (outI 1) ++ C2 xC)
  have hC3 : ∀ y, y ≠ xC → C3 y = B5 y := fun y hy =>
    (Function.update_of_ne hy _ _).trans (hC2 y hy)
  obtain ⟨u4, hu4, w4, q4⟩ := cp_run (outI 3) xC n03 (sO 3) sX C3
    (by rw [hC3 _ zx]; exact hz5)
  let C4 := Function.update C3 xC (C3 (outI 3) ++ C3 xC)
  have hC4 : ∀ y, y ≠ xC → C4 y = B5 y := fun y hy =>
    (Function.update_of_ne hy _ _).trans (hC3 y hy)
  obtain ⟨u5, hu5, w5, q5⟩ := cp_run (outI 4) xC n04 (sO 4) sX C4
    (by rw [hC4 _ zx]; exact hz5)
  let C5 := Function.update C4 xC (C4 (outI 4) ++ C4 xC)
  have hC5 : ∀ y, y ≠ xC → C5 y = B5 y := fun y hy =>
    (Function.update_of_ne hy _ _).trans (hC4 y hy)
  have x1 : C1 xC = u (Nat.clog 2 (v 1)) := by
    simp only [C1]
    rw [Function.update_self, hout 1, hx5, List.append_nil]
  have x2 : C2 xC = u (Nat.clog 2 (v 2) + Nat.clog 2 (v 1)) := by
    simp only [C2]
    rw [Function.update_self, hC1 _ (ox 2), hout 2, x1, u_app]
  have x3 : C3 xC = u (Nat.clog 2 (v 1) + (Nat.clog 2 (v 2) + Nat.clog 2 (v 1))) := by
    simp only [C3]
    rw [Function.update_self, hC2 _ (ox 1), hout 1, x2, u_app]
  have x4 : C4 xC =
      u (Nat.clog 2 (v 3) + (Nat.clog 2 (v 1) + (Nat.clog 2 (v 2) + Nat.clog 2 (v 1)))) := by
    simp only [C4]
    rw [Function.update_self, hC3 _ (ox 3), hout 3, x3, u_app]
  have hX5 : C5 xC = u (Xv v) := by
    simp only [C5]
    rw [Function.update_self, hC4 _ (ox 4), hout 4, x4, u_app]
    rfl
  -- (3) copy out 0 into thr, then push
  obtain ⟨u6, hu6, w6, q6⟩ := cp_run (outI 0) thrC n00 (sO 0) sT C5
    (by rw [hC5 _ zx]; exact hz5)
  let D := Function.update C5 thrC (C5 (outI 0) ++ C5 thrC)
  have hp := push_run D (none : Option Bool)
  let E := Function.update D thrC (true :: D thrC)
  have hEt : E thrC = u (Nat.clog 2 (v 0) + 1) := by
    simp only [E, D, Function.update_self]
    rw [hC5 _ (ox 0), hC5 _ tx, hout 0, ht5, List.append_nil]
    rfl
  have hEo : ∀ y, y ≠ thrC → y ≠ xC → E y = B5 y := fun y h1 h2 =>
    (Function.update_of_ne h1 _ _).trans ((Function.update_of_ne h1 _ _).trans (hC5 y h2))
  have hEx : E xC = u (Xv v) :=
    (Function.update_of_ne (Ne.symm tx) _ _).trans
      ((Function.update_of_ne (Ne.symm tx) _ _).trans hX5)
  -- (4) the counted loop
  let S : ℕ → TK → List Bool := fun i =>
    Function.update (Function.update E thrC (u (i * Xv v + (Nat.clog 2 (v 0) + 1)))) ctrC
      (u (k - i))
  have hS0 : S 0 = E := by
    simp only [S, Nat.zero_mul, Nat.zero_add, Nat.sub_zero]
    rw [← hEt, Function.update_eq_self, ← hc5, ← hEo ctrC (Ne.symm tc) cx,
      Function.update_eq_self]
  have hSo : ∀ i y, y ≠ thrC → y ≠ ctrC → S i y = E y := fun i y h1 h2 =>
    (Function.update_of_ne h2 _ _).trans (Function.update_of_ne h1 _ _)
  obtain ⟨tl, htl, cl, rl⟩ := CountedLoop.loop_run ctrC cL z0 (none : Option Bool) k
    (2 * Xv v + 4) S (fun i _ => Function.update_self _ _ _)
    (by
      intro i hi
      obtain ⟨R, hR⟩ : ∃ R, R = Function.update (S i) ctrC (List.replicate (k - i - 1) true) :=
        ⟨_, rfl⟩
      rw [← hR]
      have hRo : ∀ y, y ≠ thrC → y ≠ ctrC → R y = E y := by
        intro y h1 h2
        rw [hR, Function.update_of_ne h2]
        exact hSo i y h1 h2
      have hRz : R scrC = [] := by
        rw [hRo _ zt zc, hEo _ zt zx]
        exact hz5
      have hRx : R xC = u (Xv v) := by
        rw [hRo _ (Ne.symm tx) (Ne.symm cx)]
        exact hEx
      have hRt : R thrC = u (i * Xv v + (Nat.clog 2 (v 0) + 1)) := by
        rw [hR, Function.update_of_ne tc]
        exact (Function.update_of_ne tc _ _).trans (Function.update_self _ _ _)
      have hRc : R ctrC = List.replicate (k - i - 1) true := by
        rw [hR, Function.update_self]
      obtain ⟨t, ht, v', hr⟩ := cp_run xC thrC xT sX sT R hRz
      refine ⟨t, ?_, v', ?_⟩
      · rw [hRx, u, List.length_replicate] at ht
        omega
      · refine hr.trans ?_
        congr 1
        funext y
        by_cases h1 : y = ctrC
        · subst h1
          rw [Function.update_of_ne (Ne.symm tc), hRc]
          simp only [S, Function.update_self, u]
          congr 1
        · by_cases h2 : y = thrC
          · subst h2
            rw [Function.update_self, hRx, hRt, u_app]
            simp only [S]
            rw [Function.update_of_ne tc, Function.update_self, Nat.succ_mul]
            congr 1
            omega
          · rw [Function.update_of_ne h2, hRo y h2 h1, hSo (i + 1) y h2 h1])
    (none, none)
  rw [hS0] at rl
  -- (5) chain everything
  obtain ⟨a1, ha1, R1⟩ := BitMachineRawSequence.runs (logL 0) (logL 1) (.inl .scan) (.inl .scan)
    logCtl _ logCtl _ _ _ _ t1 t2 r1 r2
  obtain ⟨a2, ha2, R2⟩ := BitMachineRawSequence.runs p1 (logL 2) (leftLabel (.inl .scan))
    (.inl .scan) (logCtl, logCtl) _ logCtl _ _ _ _ a1 t3 R1 r3
  obtain ⟨a3, ha3, R3⟩ := BitMachineRawSequence.runs p2 (logL 3)
    (leftLabel (leftLabel (.inl .scan))) (.inl .scan) ((logCtl, logCtl), logCtl) _ logCtl _
    _ _ _ a2 t4 R2 r4
  obtain ⟨a4, ha4, R4⟩ := BitMachineRawSequence.runs p3 (logL 4)
    (leftLabel (leftLabel (leftLabel (.inl .scan)))) (.inl .scan) k3 _ logCtl _
    _ _ _ a3 t5 R3 r5
  obtain ⟨a5, ha5, R5⟩ := BitMachineRawSequence.runs p4 c1
    (leftLabel (leftLabel (leftLabel (leftLabel (.inl .scan))))) z0 k4 _ oc _
    _ _ _ a4 u1 R4 q1
  obtain ⟨a6, ha6, R6⟩ := BitMachineRawSequence.runs p5 c2
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (.inl .scan)))))) z0 k5 _ oc _
    _ _ _ a5 u2 R5 q2
  obtain ⟨a7, ha7, R7⟩ := BitMachineRawSequence.runs p6 c3
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (.inl .scan)))))))
    z0 k6 _ oc _ _ _ _ a6 u3 R6 q3
  obtain ⟨a8, ha8, R8⟩ := BitMachineRawSequence.runs p7 c4
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
      (.inl .scan)))))))) z0 k7 _ oc _ _ _ _ a7 u4 R7 q4
  obtain ⟨a9, ha9, R9⟩ := BitMachineRawSequence.runs p8 c5
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
      (.inl .scan))))))))) z0 k8 _ oc _ _ _ _ a8 u5 R8 q5
  obtain ⟨a10, ha10, R10⟩ := BitMachineRawSequence.runs p9 cT
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
      (leftLabel (.inl .scan)))))))))) z0 k9 _ oc _ _ _ _ a9 u6 R9 q6
  obtain ⟨a11, ha11, R11⟩ := BitMachineRawSequence.runs p10 pushT
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
      (leftLabel (leftLabel (.inl .scan))))))))))) () k10 _ oc _ _ _ _ a10 1 R10 hp
  obtain ⟨a12, ha12, R12⟩ := BitMachineRawSequence.runs p11 loopP
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
      (leftLabel (leftLabel (leftLabel (.inl .scan)))))))))))) (.inl ()) k11 _ (oc, oc) _
    _ _ _ a11 tl R11 rl
  -- source lengths of the copies
  have l1 : u1 ≤ 2 * (Nat.clog 2 (v 0) + Xv v) + 4 := by
    rw [hout 1, u, List.length_replicate] at hu1; unfold Xv; omega
  have l2 : u2 ≤ 2 * (Nat.clog 2 (v 0) + Xv v) + 4 := by
    rw [hC1 _ (ox 2), hout 2, u, List.length_replicate] at hu2; unfold Xv; omega
  have l3 : u3 ≤ 2 * (Nat.clog 2 (v 0) + Xv v) + 4 := by
    rw [hC2 _ (ox 1), hout 1, u, List.length_replicate] at hu3; unfold Xv; omega
  have l4 : u4 ≤ 2 * (Nat.clog 2 (v 0) + Xv v) + 4 := by
    rw [hC3 _ (ox 3), hout 3, u, List.length_replicate] at hu4; unfold Xv; omega
  have l5 : u5 ≤ 2 * (Nat.clog 2 (v 0) + Xv v) + 4 := by
    rw [hC4 _ (ox 4), hout 4, u, List.length_replicate] at hu5; unfold Xv; omega
  have l6 : u6 ≤ 2 * (Nat.clog 2 (v 0) + Xv v) + 4 := by
    rw [hC5 _ (ox 0), hout 0, u, List.length_replicate] at hu6; omega
  refine ⟨a12, ?_, _, S k, R12, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold thrBd logBd
    omega
  · exact (Function.update_of_ne tc _ _).trans (Function.update_self _ _ _)
  · rw [hSo k _ (Ne.symm tx) (Ne.symm cx)]; exact hEx
  · show u (k - k) = []
    rw [Nat.sub_self]; rfl
  · rw [hSo k _ zt zc, hEo _ zt zx]; exact hz5
  · intro i
    rw [hSo k _ (ot i) (oc' i), hEo _ (ot i) (ox i)]
    exact hout i
  · intro i
    rw [hSo k _ (st i) (sc i), hEo _ (st i) (sx i)]
    exact hsrc i

end

#print axioms thr_run

end Paper2.ThrProducer
