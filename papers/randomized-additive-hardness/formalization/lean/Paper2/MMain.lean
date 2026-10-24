import Paper2.MProducer

/-! Unit 3, segment (2), second part: the run of `MProducer.mProg`. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

namespace Paper2.MProducer

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

theorem rep_u (k : ℕ) : List.replicate k true = u k := rfl
theorem cons_u (k : ℕ) : true :: u k = u (k + 1) := rfl
theorem u_app (a b : ℕ) : u a ++ u b = u (a + b) := (List.replicate_add a b true).symm
theorem tail_u (a : ℕ) : (u a).tail = u (a - 1) := List.tail_replicate

def pushK (a : MK) : ℕ → (MK → List Bool) → MK → List Bool
  | 0, S => S
  | k + 1, S => Function.update (pushK a k S) a (true :: pushK a k S a)

theorem pushK_eq (a : MK) (k : ℕ) (S : MK → List Bool) :
    pushK a k S = Function.update S a (List.replicate k true ++ S a) := by
  induction k with
  | zero => simp [pushK]
  | succ k ih =>
      rw [pushK, ih, Function.update_self, Function.update_idem, List.replicate_succ,
        List.cons_append]

theorem cp_run (a b : MK) (hab : a ≠ b) (ha : a ≠ 14) (hb : b ≠ 14) (S : MK → List Bool)
    (hz : S 14 = []) :
    ((advance (cp a b hab ha hb))^[2 * (S a).length + 2])
        (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : MK => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update S b (S a ++ S b)⟩ :=
  MatrixStage4ScalarPreparationOps.copy_run (cpE a b hab ha hb) S hz

theorem pw_run (o e : MK) (h1 : o ≠ 15) (h2 : o ≠ 16) (h3 : o ≠ e) (h4 : e ≠ 15) (h5 : e ≠ 16)
    (S : MK → List Bool) (a : ℕ) (hs : S e = u a) (h0 : S o = []) (h6 : S 15 = [])
    (h7 : S 16 = []) :
    ∃ t ≤ 4 * 2 ^ a + 5 * a + 7,
      ((advance (pw o e h1 h2 h3 h4 h5))^[t])
          (⟨some (.inr false), powCtl, S⟩ : TM2.Cfg (fun _ : MK => Bool)
            MatrixUnaryPower.Label MatrixUnaryPower.Control) =
        ⟨none, powCtl, Function.update S o (u (2 ^ a))⟩ :=
  MatrixStage4ScalarPreparationOps.unary_power_run (powE o e h1 h2 h3 h4 h5) S a hs h0 h6 h7

def mBd (b k L : ℕ) : ℕ :=
  (2 * b + 2) + 1 + (4 * 2 ^ (b - 1) + 5 * (b - 1) + 7) + (2 * b + 2) + (2 * k + 2) + 1 +
    (4 * 2 ^ (k + b - 1) + 5 * (k + b - 1) + 7) + (2 * 2 ^ (b - 1) + 2) + 1 +
    MatrixAddressMachine.exactTime (2 ^ (b - 1)) ((2 ^ (b - 1)) + 1) 0 + 1 +
    MatrixAddressMachine.exactTime (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) (2 ^ (k + b - 1)) 0 + 1 +
    (2 * (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) + 2) + (2 * (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) + 2) + (2 * (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) + 2) + (2 * L + 2) + 1 +
    MatrixUnaryDivision.totalTime (L + (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) - 1) L + 18

theorem m_run (b k L : ℕ) :
    ∃ t ≤ mBd b k L, ∃ vc, ∃ F : MK → List Bool,
      ((advance mProg)^[t]) (⟨some mStart, mCtl, M0 b k L⟩ : TM2.Cfg (fun _ : MK => Bool) _ _) =
        ⟨none, vc, F⟩ ∧
      F 0 = u b ∧ F 1 = u k ∧ F 2 = u L ∧ F 3 = u (b - 1) ∧ F 4 = u (2 ^ (b - 1)) ∧ F 5 = u (k + b - 1) ∧
      F 6 = u (2 ^ (k + b - 1)) ∧ F 7 = u ((2 ^ (b - 1)) + 1) ∧ F 8 = u (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) ∧ F 9 = u (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) ∧
      F 10 = u ((12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) + (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1)))) ∧ F 11 = [] ∧ F 12 = u ((L + (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) - 1) % L) ∧
      F 13 = u ((L + (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) - 1) / L) ∧ F 14 = [] ∧ F 15 = [] ∧ F 16 = [] ∧ F 17 = [] := by
  obtain ⟨S0, hS0⟩ : ∃ S, S = M0 b k L := ⟨_, rfl⟩
  have h1 := cp_run 0 3 (by decide) (by decide) (by decide) S0 (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0] <;> (try rfl) <;> (try (congr 1; omega))))
  obtain ⟨S1, hS1⟩ : ∃ S, S = Function.update S0 3 (S0 0 ++ S0 3) := ⟨_, rfl⟩
  rw [← hS1] at h1
  have l1 : (S0 0).length = b := by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0] <;> (try rfl) <;> (try (congr 1; omega))); (try simp only [u, List.length_replicate]); (try rfl)
  rw [l1] at h1
  have h2 : ((advance P2)^[1]) (⟨some (), false, S1⟩ : TM2.Cfg (fun _ : MK => Bool) Unit Bool) =
      ⟨none, false, Function.update S1 3 (S1 3).tail⟩ := rfl
  obtain ⟨S2, hS2⟩ : ∃ S, S = Function.update S1 3 (S1 3).tail := ⟨_, rfl⟩
  rw [← hS2] at h2
  obtain ⟨t3, ht3, h3⟩ := pw_run 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    S2 (b - 1) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2] <;> (try rfl) <;> (try (congr 1; omega))))
  obtain ⟨S3, hS3⟩ : ∃ S, S = Function.update S2 4 (u (2 ^ (b - 1))) := ⟨_, rfl⟩
  rw [← hS3] at h3
  have h4 := cp_run 0 5 (by decide) (by decide) (by decide) S3 (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3] <;> (try rfl) <;> (try (congr 1; omega))))
  obtain ⟨S4, hS4⟩ : ∃ S, S = Function.update S3 5 (S3 0 ++ S3 5) := ⟨_, rfl⟩
  rw [← hS4] at h4
  have l4 : (S3 0).length = b := by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3] <;> (try rfl) <;> (try (congr 1; omega))); (try simp only [u, List.length_replicate]); (try rfl)
  rw [l4] at h4
  have h5 := cp_run 1 5 (by decide) (by decide) (by decide) S4 (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4] <;> (try rfl) <;> (try (congr 1; omega))))
  obtain ⟨S5, hS5⟩ : ∃ S, S = Function.update S4 5 (S4 1 ++ S4 5) := ⟨_, rfl⟩
  rw [← hS5] at h5
  have l5 : (S4 1).length = k := by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4] <;> (try rfl) <;> (try (congr 1; omega))); (try simp only [u, List.length_replicate]); (try rfl)
  rw [l5] at h5
  have h6 : ((advance P6)^[1]) (⟨some (), false, S5⟩ : TM2.Cfg (fun _ : MK => Bool) Unit Bool) =
      ⟨none, false, Function.update S5 5 (S5 5).tail⟩ := rfl
  obtain ⟨S6, hS6⟩ : ∃ S, S = Function.update S5 5 (S5 5).tail := ⟨_, rfl⟩
  rw [← hS6] at h6
  obtain ⟨t7, ht7, h7⟩ := pw_run 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    S6 (k + b - 1) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6] <;> (try rfl) <;> (try (congr 1; omega))))
  obtain ⟨S7, hS7⟩ : ∃ S, S = Function.update S6 6 (u (2 ^ (k + b - 1))) := ⟨_, rfl⟩
  rw [← hS7] at h7
  have h8 := cp_run 4 7 (by decide) (by decide) (by decide) S7 (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7] <;> (try rfl) <;> (try (congr 1; omega))))
  obtain ⟨S8, hS8⟩ : ∃ S, S = Function.update S7 7 (S7 4 ++ S7 7) := ⟨_, rfl⟩
  rw [← hS8] at h8
  have l8 : (S7 4).length = (2 ^ (b - 1)) := by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7] <;> (try rfl) <;> (try (congr 1; omega))); (try simp only [u, List.length_replicate]); (try rfl)
  rw [l8] at h8
  have h9 : ((advance P9)^[1]) (⟨some (), false, S8⟩ : TM2.Cfg (fun _ : MK => Bool) Unit Bool) =
      ⟨none, false, pushK 7 1 S8⟩ := rfl
  obtain ⟨S9, hS9⟩ : ∃ S, S = pushK 7 1 S8 := ⟨_, rfl⟩
  rw [← hS9] at h9
  have h10 := MatrixStage4ScalarPreparationOps.multiply_run ιM1 S9 (2 ^ (b - 1)) ((2 ^ (b - 1)) + 1) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9] <;> (try rfl) <;> (try (congr 1; omega))))
    (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9] <;> (try rfl) <;> (try (congr 1; omega))))
  obtain ⟨S10, hS10⟩ : ∃ S, S = Function.update S9 8 (u ((2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1))) := ⟨_, rfl⟩
  have e10 : Function.update S9 (ιM1 5) (List.replicate ((2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) true ++ S9 (ιM1 5)) =
      S10 := by
    have hd : S9 8 = [] := by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9] <;> (try rfl) <;> (try (congr 1; omega)))
    rw [hS10]
    show Function.update S9 8 (List.replicate ((2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) true ++ S9 8) = _
    rw [hd, List.append_nil]; rfl
  rw [e10] at h10
  have h11 : ((advance P11)^[1]) (⟨some (), false, S10⟩ : TM2.Cfg (fun _ : MK => Bool) Unit Bool) =
      ⟨none, false, pushK 8 2 S10⟩ := rfl
  obtain ⟨S11, hS11⟩ : ∃ S, S = pushK 8 2 S10 := ⟨_, rfl⟩
  rw [← hS11] at h11
  have h12 := MatrixStage4ScalarPreparationOps.multiply_run ιM2 S11 (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) (2 ^ (k + b - 1)) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11] <;> (try rfl) <;> (try (congr 1; omega))))
    (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11] <;> (try rfl) <;> (try (congr 1; omega))))
  obtain ⟨S12, hS12⟩ : ∃ S, S = Function.update S11 9 (u ((2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1)))) := ⟨_, rfl⟩
  have e12 : Function.update S11 (ιM2 5) (List.replicate ((2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) true ++ S11 (ιM2 5)) =
      S12 := by
    have hd : S11 9 = [] := by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11] <;> (try rfl) <;> (try (congr 1; omega)))
    rw [hS12]
    show Function.update S11 9 (List.replicate ((2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) true ++ S11 9) = _
    rw [hd, List.append_nil]; rfl
  rw [e12] at h12
  have h13 : ((advance P13)^[1]) (⟨some (), false, S12⟩ : TM2.Cfg (fun _ : MK => Bool) Unit Bool) =
      ⟨none, false, pushK 9 12 S12⟩ := rfl
  obtain ⟨S13, hS13⟩ : ∃ S, S = pushK 9 12 S12 := ⟨_, rfl⟩
  rw [← hS13] at h13
  have h14 := cp_run 9 10 (by decide) (by decide) (by decide) S13 (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13] <;> (try rfl) <;> (try (congr 1; omega))))
  obtain ⟨S14, hS14⟩ : ∃ S, S = Function.update S13 10 (S13 9 ++ S13 10) := ⟨_, rfl⟩
  rw [← hS14] at h14
  have l14 : (S13 9).length = (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) := by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13] <;> (try rfl) <;> (try (congr 1; omega))); (try simp only [u, List.length_replicate]); (try rfl)
  rw [l14] at h14
  have h15 := cp_run 9 10 (by decide) (by decide) (by decide) S14 (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14] <;> (try rfl) <;> (try (congr 1; omega))))
  obtain ⟨S15, hS15⟩ : ∃ S, S = Function.update S14 10 (S14 9 ++ S14 10) := ⟨_, rfl⟩
  rw [← hS15] at h15
  have l15 : (S14 9).length = (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) := by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14] <;> (try rfl) <;> (try (congr 1; omega))); (try simp only [u, List.length_replicate]); (try rfl)
  rw [l15] at h15
  have h16 := cp_run 9 11 (by decide) (by decide) (by decide) S15 (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15] <;> (try rfl) <;> (try (congr 1; omega))))
  obtain ⟨S16, hS16⟩ : ∃ S, S = Function.update S15 11 (S15 9 ++ S15 11) := ⟨_, rfl⟩
  rw [← hS16] at h16
  have l16 : (S15 9).length = (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) := by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15] <;> (try rfl) <;> (try (congr 1; omega))); (try simp only [u, List.length_replicate]); (try rfl)
  rw [l16] at h16
  have h17 := cp_run 2 11 (by decide) (by decide) (by decide) S16 (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16] <;> (try rfl) <;> (try (congr 1; omega))))
  obtain ⟨S17, hS17⟩ : ∃ S, S = Function.update S16 11 (S16 2 ++ S16 11) := ⟨_, rfl⟩
  rw [← hS17] at h17
  have l17 : (S16 2).length = L := by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16] <;> (try rfl) <;> (try (congr 1; omega))); (try simp only [u, List.length_replicate]); (try rfl)
  rw [l17] at h17
  have h18 : ((advance P18)^[1]) (⟨some (), false, S17⟩ : TM2.Cfg (fun _ : MK => Bool) Unit Bool) =
      ⟨none, false, Function.update S17 11 (S17 11).tail⟩ := rfl
  obtain ⟨S18, hS18⟩ : ∃ S, S = Function.update S17 11 (S17 11).tail := ⟨_, rfl⟩
  rw [← hS18] at h18
  have h19 := div_run ιD S18 (L + (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) - 1) L (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18] <;> (try rfl) <;> (try (congr 1; omega))))
    (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18] <;> (try rfl) <;> (try (congr 1; omega)))) (by (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18] <;> (try rfl) <;> (try (congr 1; omega))))
  obtain ⟨S19, hS19⟩ : ∃ S, S = Function.update (Function.update (Function.update S18 (ιD 0) []) (ιD 3)
      (u ((L + (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) - 1) % L))) (ιD 4) (u ((L + (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) - 1) / L)) := ⟨_, rfl⟩
  rw [← hS19] at h19
  obtain ⟨a2, ha2, R2⟩ := BitMachineRawSequence.runs P1 P2 BitMachineCopy.Label.scan ()
    oc _ false _ _ _ _ (2 * b + 2) 1 h1 h2
  obtain ⟨a3, ha3, R3⟩ := BitMachineRawSequence.runs s1 P3 (leftLabel BitMachineCopy.Label.scan) (.inr false)
    (oc, false) _ powCtl _ _ _ _ a2 t3 R2 h3
  obtain ⟨a4, ha4, R4⟩ := BitMachineRawSequence.runs s2 P4 (leftLabel (leftLabel BitMachineCopy.Label.scan)) BitMachineCopy.Label.scan
    k2 _ oc _ _ _ _ a3 (2 * b + 2) R3 h4
  obtain ⟨a5, ha5, R5⟩ := BitMachineRawSequence.runs s3 P5 (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))) BitMachineCopy.Label.scan
    k3 _ oc _ _ _ _ a4 (2 * k + 2) R4 h5
  obtain ⟨a6, ha6, R6⟩ := BitMachineRawSequence.runs s4 P6 (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))) ()
    k4 _ false _ _ _ _ a5 1 R5 h6
  obtain ⟨a7, ha7, R7⟩ := BitMachineRawSequence.runs s5 P7 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))) (.inr false)
    k5 _ powCtl _ _ _ _ a6 t7 R6 h7
  obtain ⟨a8, ha8, R8⟩ := BitMachineRawSequence.runs s6 P8 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))))) BitMachineCopy.Label.scan
    k6 _ oc _ _ _ _ a7 (2 * (2 ^ (b - 1)) + 2) R7 h8
  obtain ⟨a9, ha9, R9⟩ := BitMachineRawSequence.runs s7 P9 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))))) ()
    k7 _ false _ _ _ _ a8 1 R8 h9
  obtain ⟨a10, ha10, R10⟩ := BitMachineRawSequence.runs s8 P10 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))))))) MatrixAddressMachine.Label.outer
    k8 _ false _ _ _ _ a9 (MatrixAddressMachine.exactTime (2 ^ (b - 1)) ((2 ^ (b - 1)) + 1) 0) R9 h10
  obtain ⟨a11, ha11, R11⟩ := BitMachineRawSequence.runs s9 P11 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))))))) ()
    k9 _ false _ _ _ _ a10 1 R10 h11
  obtain ⟨a12, ha12, R12⟩ := BitMachineRawSequence.runs s10 P12 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))))))))) MatrixAddressMachine.Label.outer
    k10 _ false _ _ _ _ a11 (MatrixAddressMachine.exactTime (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) (2 ^ (k + b - 1)) 0) R11 h12
  obtain ⟨a13, ha13, R13⟩ := BitMachineRawSequence.runs s11 P13 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))))))))) ()
    k11 _ false _ _ _ _ a12 1 R12 h13
  obtain ⟨a14, ha14, R14⟩ := BitMachineRawSequence.runs s12 P14 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))))))))))) BitMachineCopy.Label.scan
    k12 _ oc _ _ _ _ a13 (2 * (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) + 2) R13 h14
  obtain ⟨a15, ha15, R15⟩ := BitMachineRawSequence.runs s13 P15 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))))))))))) BitMachineCopy.Label.scan
    k13 _ oc _ _ _ _ a14 (2 * (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) + 2) R14 h15
  obtain ⟨a16, ha16, R16⟩ := BitMachineRawSequence.runs s14 P16 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))))))))))))) BitMachineCopy.Label.scan
    k14 _ oc _ _ _ _ a15 (2 * (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) + 2) R15 h16
  obtain ⟨a17, ha17, R17⟩ := BitMachineRawSequence.runs s15 P17 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))))))))))))) BitMachineCopy.Label.scan
    k15 _ oc _ _ _ _ a16 (2 * L + 2) R16 h17
  obtain ⟨a18, ha18, R18⟩ := BitMachineRawSequence.runs s16 P18 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))))))))))))))) ()
    k16 _ false _ _ _ _ a17 1 R17 h18
  obtain ⟨a19, ha19, R19⟩ := BitMachineRawSequence.runs s17 P19 (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))))))))))))))) MatrixUnaryDivision.Label.start
    k17 _ false _ _ _ _ a18 (MatrixUnaryDivision.totalTime (L + (12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))) - 1) L) R18 h19
  rw [hS0] at R19
  refine ⟨a19, ?_, _, S19, R19, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold mBd
    omega
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))
  · (simp [Function.update_apply, ιM1, ιM2, ιD, M0, rep_u, u_app, cons_u, tail_u, List.append_nil, pushK_eq, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19] <;> (try rfl) <;> (try (congr 1; omega)))

end

#print axioms div_run
#print axioms pushK_eq
#print axioms m_run

end Paper2.MProducer
