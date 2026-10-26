import Paper2.LRun

/-! Unit 3, segment (2), first part: the run of `LProducer.lProg`. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

namespace Paper2.LProducer

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

theorem rep_u (k : ℕ) : List.replicate k true = u k := rfl
theorem cons_u (k : ℕ) : true :: u k = u (k + 1) := rfl

def lBd (n : ℕ) : ℕ :=
  (2 * n + 2) + logBd n + (2 * Nat.clog 2 n + 2) + (2 * Nat.clog 2 n + 2) + 1 +
    (2 * (Nat.clog 2 n + 1) + 2) + logBd (Nat.clog 2 n + 1) +
    5 * (2 * Nat.clog 2 (Nat.clog 2 n + 1) + 2) + 1 +
    MatrixAddressMachine.exactTime (Nat.clog 2 (Nat.clog 2 n + 1)) (Nat.clog 2 (Nat.clog 2 n + 1)) 0 +
    (4 * 2 ^ (6 + Nat.clog 2 (Nat.clog 2 n + 1)) + 5 * (6 + Nat.clog 2 (Nat.clog 2 n + 1)) + 7) +
    (4 * 2 ^ (16 + Nat.clog 2 (Nat.clog 2 n + 1)) + 5 * (16 + Nat.clog 2 (Nat.clog 2 n + 1)) + 7) +
    (4 * 2 ^ (32 + (Nat.clog 2 (Nat.clog 2 n + 1) + (Nat.clog 2 (Nat.clog 2 n + 1) + Nat.clog 2 n))) +
      5 * (32 + (Nat.clog 2 (Nat.clog 2 n + 1) + (Nat.clog 2 (Nat.clog 2 n + 1) + Nat.clog 2 n))) + 7) +
    (4 * 2 ^ (Nat.clog 2 (Nat.clog 2 n + 1) * Nat.clog 2 (Nat.clog 2 n + 1)) +
      5 * (Nat.clog 2 (Nat.clog 2 n + 1) * Nat.clog 2 (Nat.clog 2 n + 1)) + 7) +
    (2 * 2 ^ (16 + Nat.clog 2 (Nat.clog 2 n + 1)) + 2) + 1 + 19

theorem l_run (n : ℕ) :
    let L := Nat.clog 2 n
    let e := Nat.clog 2 (L + 1)
    ∃ t ≤ lBd n, ∃ vc, ∃ F : LK → List Bool,
      ((advance lProg)^[t]) (⟨some lStart, lCtl, L0 n⟩ : TM2.Cfg (fun _ : LK => Bool) _ _) =
        ⟨none, vc, F⟩ ∧
      F nC = u n ∧ F c1 = u (L + 1) ∧ F oe = u (32 + (e + (e + L))) ∧ F ep = u (6 + e) ∧
      F es = u (16 + e) ∧ F dp = u e ∧ F dd = u (e * e) ∧ F pC = u (2 ^ (6 + e)) ∧
      F sC = u (2 ^ (16 + e)) ∧ F q2C = u (2 ^ (32 + (e + (e + L)))) ∧ F wC = u (2 ^ (e * e)) ∧
      F q1C = u (2 ^ (16 + e) - 2) ∧ F z = [] ∧ F x1 = [] ∧ F x2 = [] ∧ F x3 = [] ∧
      ∃ g0 g1 : ETHParameterScaleMachineLogCopy.logMachine.Config,
        (∀ y, F (.inr (0, y)) = (ETHParameterScaleMachineLogCopy.afterLog (u n) g0).stk y) ∧
        (∀ y, F (.inr (1, y)) = (ETHParameterScaleMachineLogCopy.afterLog (u (L + 1)) g1).stk y) ∧
        (ETHParameterScaleMachineLogCopy.afterLog (u n) g0).stk
          (ETHParameterScaleMachineLogCopy.logStack
            ETHParameterScaleMachineLogCopy.logMachine.output) = u L ∧
        (ETHParameterScaleMachineLogCopy.afterLog (u (L + 1)) g1).stk
          (ETHParameterScaleMachineLogCopy.logStack
            ETHParameterScaleMachineLogCopy.logMachine.output) = u e := by
  intro L e
  obtain ⟨S0, hS0⟩ : ∃ S, S = L0 n := ⟨_, rfl⟩
  have h1 := cp_run nC (srcR 0) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) S0 (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0] <;> (try rfl)))
  obtain ⟨S1, hS1⟩ : ∃ S, S = Function.update S0 (srcR 0) (S0 nC ++ S0 (srcR 0)) := ⟨_, rfl⟩
  rw [← hS1] at h1
  have l1 : (S0 nC).length = n := by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1] <;> (try rfl)); (try simp only [u, List.length_replicate, List.tail_replicate]); (try rfl)
  rw [l1] at h1
  obtain ⟨t2, ht2, g0, h2, ho0⟩ := log_lift 0 S1 n (by
    intro x
    by_cases hx : x = .inl 0
    · subst hx; (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1] <;> (try rfl)); (try simp only [u, List.length_replicate, List.tail_replicate]); (try rfl)
    · simp [hS0, hS1, L0, Function.update_apply, c, srcR, region, hx])
  obtain ⟨G0, hG0⟩ : ∃ G, G = (ETHParameterScaleMachineLogCopy.afterLog (u n) g0).stk := ⟨_, rfl⟩
  rw [← hG0] at h2 ho0
  obtain ⟨S2, hS2⟩ : ∃ S, S = bank (ιR 0) S1 G0 := ⟨_, rfl⟩
  rw [← hS2] at h2
  have h3 := cp_run (outR 0) c1 (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) S2 (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0] <;> (try rfl)))
  obtain ⟨S3, hS3⟩ : ∃ S, S = Function.update S2 c1 (S2 (outR 0) ++ S2 c1) := ⟨_, rfl⟩
  rw [← hS3] at h3
  have l3 : (S2 (outR 0)).length = L := by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3] <;> (try rfl)); (try simp only [u, List.length_replicate, List.tail_replicate]); (try rfl)
  rw [l3] at h3
  have h4 := cp_run (outR 0) oe (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) S3 (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3] <;> (try rfl)))
  obtain ⟨S4, hS4⟩ : ∃ S, S = Function.update S3 oe (S3 (outR 0) ++ S3 oe) := ⟨_, rfl⟩
  rw [← hS4] at h4
  have l4 : (S3 (outR 0)).length = L := by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4] <;> (try rfl)); (try simp only [u, List.length_replicate, List.tail_replicate]); (try rfl)
  rw [l4] at h4
  have h5 := push1_run S4 false
  obtain ⟨S5, hS5⟩ : ∃ S, S = Function.update S4 c1 (true :: S4 c1) := ⟨_, rfl⟩
  rw [← hS5] at h5
  have h6 := cp_run c1 (srcR 1) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) S5 (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5] <;> (try rfl)))
  obtain ⟨S6, hS6⟩ : ∃ S, S = Function.update S5 (srcR 1) (S5 c1 ++ S5 (srcR 1)) := ⟨_, rfl⟩
  rw [← hS6] at h6
  have l6 : (S5 c1).length = L + 1 := by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6] <;> (try rfl)); (try simp only [u, List.length_replicate, List.tail_replicate]); (try rfl)
  rw [l6] at h6
  obtain ⟨t7, ht7, g1, h7, ho1⟩ := log_lift 1 S6 (L + 1) (by
    intro x
    by_cases hx : x = .inl 0
    · subst hx; (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6] <;> (try rfl)); (try rw [region, if_pos rfl]); (try rfl)
    · simp [hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, L0, Function.update_apply, c, srcR, outR, region, hx, bank_ne, bank_inl])
  obtain ⟨G1, hG1⟩ : ∃ G, G = (ETHParameterScaleMachineLogCopy.afterLog (u (L + 1)) g1).stk := ⟨_, rfl⟩
  rw [← hG1] at h7 ho1
  obtain ⟨S7, hS7⟩ : ∃ S, S = bank (ιR 1) S6 G1 := ⟨_, rfl⟩
  rw [← hS7] at h7
  have h8 := cp_run (outR 1) ep (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) S7 (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1] <;> (try rfl)))
  obtain ⟨S8, hS8⟩ : ∃ S, S = Function.update S7 ep (S7 (outR 1) ++ S7 ep) := ⟨_, rfl⟩
  rw [← hS8] at h8
  have l8 : (S7 (outR 1)).length = e := by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8] <;> (try rfl)); (try simp only [u, List.length_replicate, List.tail_replicate]); (try rfl)
  rw [l8] at h8
  have h9 := cp_run (outR 1) es (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) S8 (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8] <;> (try rfl)))
  obtain ⟨S9, hS9⟩ : ∃ S, S = Function.update S8 es (S8 (outR 1) ++ S8 es) := ⟨_, rfl⟩
  rw [← hS9] at h9
  have l9 : (S8 (outR 1)).length = e := by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9] <;> (try rfl)); (try simp only [u, List.length_replicate, List.tail_replicate]); (try rfl)
  rw [l9] at h9
  have h10 := cp_run (outR 1) dp (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) S9 (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9] <;> (try rfl)))
  obtain ⟨S10, hS10⟩ : ∃ S, S = Function.update S9 dp (S9 (outR 1) ++ S9 dp) := ⟨_, rfl⟩
  rw [← hS10] at h10
  have l10 : (S9 (outR 1)).length = e := by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10] <;> (try rfl)); (try simp only [u, List.length_replicate, List.tail_replicate]); (try rfl)
  rw [l10] at h10
  have h11 := cp_run (outR 1) oe (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) S10 (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10] <;> (try rfl)))
  obtain ⟨S11, hS11⟩ : ∃ S, S = Function.update S10 oe (S10 (outR 1) ++ S10 oe) := ⟨_, rfl⟩
  rw [← hS11] at h11
  have l11 : (S10 (outR 1)).length = e := by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11] <;> (try rfl)); (try simp only [u, List.length_replicate, List.tail_replicate]); (try rfl)
  rw [l11] at h11
  have h12 := cp_run (outR 1) oe (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) S11 (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11] <;> (try rfl)))
  obtain ⟨S12, hS12⟩ : ∃ S, S = Function.update S11 oe (S11 (outR 1) ++ S11 oe) := ⟨_, rfl⟩
  rw [← hS12] at h12
  have l12 : (S11 (outR 1)).length = e := by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12] <;> (try rfl)); (try simp only [u, List.length_replicate, List.tail_replicate]); (try rfl)
  rw [l12] at h12
  have h13 := pushC_run S12 false
  obtain ⟨S13, hS13⟩ : ∃ S, S = pushK oe 32 (pushK es 16 (pushK ep 6 S12)) := ⟨_, rfl⟩
  rw [← hS13] at h13
  have h14 := MatrixStage4ScalarPreparationOps.multiply_run ιM S13 e e (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13] <;> (try rfl)))
    (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13] <;> (try rfl))) (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13] <;> (try rfl))) (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13] <;> (try rfl))) (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13] <;> (try rfl)))
  obtain ⟨S14, hS14⟩ : ∃ S, S = Function.update S13 dd (u (e * e)) := ⟨_, rfl⟩
  have e14 : Function.update S13 (ιM 5) (List.replicate (e * e) true ++ S13 (ιM 5)) = S14 := by
    have hdd : S13 dd = [] := by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13] <;> (try rfl))
    rw [hS14]
    show Function.update S13 dd (List.replicate (e * e) true ++ S13 dd) = _
    rw [hdd, List.append_nil]; rfl
  rw [e14] at h14
  obtain ⟨t15, ht15, h15⟩ := pw_run pC ep (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) S14 (6 + e) (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14] <;> (try rfl))) (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14] <;> (try rfl)))
    (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14] <;> (try rfl))) (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14] <;> (try rfl)))
  obtain ⟨S15, hS15⟩ : ∃ S, S = Function.update S14 pC (u (2 ^ (6 + e))) := ⟨_, rfl⟩
  rw [← hS15] at h15
  obtain ⟨t16, ht16, h16⟩ := pw_run sC es (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) S15 (16 + e) (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15] <;> (try rfl))) (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15] <;> (try rfl)))
    (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15] <;> (try rfl))) (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15] <;> (try rfl)))
  obtain ⟨S16, hS16⟩ : ∃ S, S = Function.update S15 sC (u (2 ^ (16 + e))) := ⟨_, rfl⟩
  rw [← hS16] at h16
  obtain ⟨t17, ht17, h17⟩ := pw_run q2C oe (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) S16 (32 + (e + (e + L))) (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16] <;> (try rfl))) (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16] <;> (try rfl)))
    (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16] <;> (try rfl))) (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16] <;> (try rfl)))
  obtain ⟨S17, hS17⟩ : ∃ S, S = Function.update S16 q2C (u (2 ^ (32 + (e + (e + L))))) := ⟨_, rfl⟩
  rw [← hS17] at h17
  obtain ⟨t18, ht18, h18⟩ := pw_run wC dd (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) S17 (e * e) (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17] <;> (try rfl))) (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17] <;> (try rfl)))
    (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17] <;> (try rfl))) (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17] <;> (try rfl)))
  obtain ⟨S18, hS18⟩ : ∃ S, S = Function.update S17 wC (u (2 ^ (e * e))) := ⟨_, rfl⟩
  rw [← hS18] at h18
  have h19 := cp_run sC q1C (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) S18 (by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18] <;> (try rfl)))
  obtain ⟨S19, hS19⟩ : ∃ S, S = Function.update S18 q1C (S18 sC ++ S18 q1C) := ⟨_, rfl⟩
  rw [← hS19] at h19
  have l19 : (S18 sC).length = 2 ^ (16 + e) := by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl)); (try simp only [u, List.length_replicate, List.tail_replicate]); (try rfl)
  rw [l19] at h19
  have h20 := pop2_run S19 false
  obtain ⟨S20, hS20⟩ : ∃ S, S = Function.update (Function.update S19 q1C (S19 q1C).tail) q1C
      ((Function.update S19 q1C (S19 q1C).tail) q1C).tail := ⟨_, rfl⟩
  rw [← hS20] at h20
  obtain ⟨a2, ha2, R2⟩ := BitMachineRawSequence.runs P1 P2 BitMachineCopy.Label.scan (.inl .scan)
    oc _ logCtl _ _ _ _ (2 * n + 2) t2 h1 h2
  obtain ⟨a3, ha3, R3⟩ := BitMachineRawSequence.runs s1 P3 (leftLabel BitMachineCopy.Label.scan) BitMachineCopy.Label.scan
    (oc, logCtl) _ oc _ _ _ _ a2 (2 * L + 2) R2 h3
  obtain ⟨a4, ha4, R4⟩ := BitMachineRawSequence.runs s2 P4 (leftLabel (leftLabel BitMachineCopy.Label.scan)) BitMachineCopy.Label.scan
    ((oc, logCtl), oc) _ oc _ _ _ _ a3 (2 * L + 2) R3 h4
  obtain ⟨a5, ha5, R5⟩ := BitMachineRawSequence.runs s3 P5 (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))) ()
    k3 _ false _ _ _ _ a4 1 R4 h5
  obtain ⟨a6, ha6, R6⟩ := BitMachineRawSequence.runs s4 P6 (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))) BitMachineCopy.Label.scan
    k4 _ oc _ _ _ _ a5 (2 * (L + 1) + 2) R5 h6
  obtain ⟨a7, ha7, R7⟩ := BitMachineRawSequence.runs s5 P7 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))) (.inl .scan)
    k5 _ logCtl _ _ _ _ a6 t7 R6 h7
  obtain ⟨a8, ha8, R8⟩ := BitMachineRawSequence.runs s6 P8 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))))) BitMachineCopy.Label.scan
    k6 _ oc _ _ _ _ a7 (2 * e + 2) R7 h8
  obtain ⟨a9, ha9, R9⟩ := BitMachineRawSequence.runs s7 P9 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))))) BitMachineCopy.Label.scan
    k7 _ oc _ _ _ _ a8 (2 * e + 2) R8 h9
  obtain ⟨a10, ha10, R10⟩ := BitMachineRawSequence.runs s8 P10 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))))))) BitMachineCopy.Label.scan
    k8 _ oc _ _ _ _ a9 (2 * e + 2) R9 h10
  obtain ⟨a11, ha11, R11⟩ := BitMachineRawSequence.runs s9 P11 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))))))) BitMachineCopy.Label.scan
    k9 _ oc _ _ _ _ a10 (2 * e + 2) R10 h11
  obtain ⟨a12, ha12, R12⟩ := BitMachineRawSequence.runs s10 P12 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))))))))) BitMachineCopy.Label.scan
    k10 _ oc _ _ _ _ a11 (2 * e + 2) R11 h12
  obtain ⟨a13, ha13, R13⟩ := BitMachineRawSequence.runs s11 P13 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))))))))) ()
    k11 _ false _ _ _ _ a12 1 R12 h13
  obtain ⟨a14, ha14, R14⟩ := BitMachineRawSequence.runs s12 P14 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))))))))))) MatrixAddressMachine.Label.outer
    k12 _ false _ _ _ _ a13 (MatrixAddressMachine.exactTime e e 0) R13 h14
  obtain ⟨a15, ha15, R15⟩ := BitMachineRawSequence.runs s13 P15 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))))))))))) (.inr false)
    k13 _ powCtl _ _ _ _ a14 t15 R14 h15
  obtain ⟨a16, ha16, R16⟩ := BitMachineRawSequence.runs s14 P16 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))))))))))))) (.inr false)
    k14 _ powCtl _ _ _ _ a15 t16 R15 h16
  obtain ⟨a17, ha17, R17⟩ := BitMachineRawSequence.runs s15 P17 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))))))))))))) (.inr false)
    k15 _ powCtl _ _ _ _ a16 t17 R16 h17
  obtain ⟨a18, ha18, R18⟩ := BitMachineRawSequence.runs s16 P18 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))))))))))))))) (.inr false)
    k16 _ powCtl _ _ _ _ a17 t18 R17 h18
  obtain ⟨a19, ha19, R19⟩ := BitMachineRawSequence.runs s17 P19 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))))))))))))))) BitMachineCopy.Label.scan
    k17 _ oc _ _ _ _ a18 (2 * 2 ^ (16 + e) + 2) R18 h19
  obtain ⟨a20, ha20, R20⟩ := BitMachineRawSequence.runs s18 P20 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))))))))))))))))) ()
    k18 _ false _ _ _ _ a19 1 R19 h20
  rw [hS0] at R20
  refine ⟨a20, ?_, _, S20, R20, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, g0, g1,
    ?_, ?_, ?_, ?_⟩
  · show a20 ≤ lBd n
    simp only [L, e, logBd] at *
    simp only [lBd, logBd]
    omega
  · (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · have hq : S20 q1C = u (2 ^ (16 + e) - 1 - 1) := by (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl)); (try simp only [u, List.length_replicate, List.tail_replicate]); (try rfl)
    rw [hq]; congr 1
  · (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · intro y; rw [← hG0]; (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · intro y; rw [← hG1]; (simp [Function.update_apply, c, srcR, outR, ιM, bank_inl, bank_ne, bank_same, L0, rep_u, u_app, cons_u, List.append_nil, pushK_eq, hS0, hS1, hS2, ho0, hS3, hS4, hS5, hS6, hS7, ho1, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20] <;> (try rfl))
  · rw [← hG0]; exact ho0
  · rw [← hG1]; exact ho1

end

#print axioms l_run

end Paper2.LProducer
