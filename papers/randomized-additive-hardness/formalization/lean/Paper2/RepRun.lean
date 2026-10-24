import Paper2.RepProducer

/-! Unit 3, segment (1): the run of the repetition-factor producer `RepProducer.repProg`. -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384

namespace Paper2.RepProducer

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

/-- `N = 12 * s * m`, `c = clog 2 N`. -/
def repBd (s q₂ m : ℕ) : ℕ :=
  1 + MatrixAddressMachine.exactTime 12 s 0 + 1 + MatrixAddressMachine.exactTime (12 * s) m 0 + 1 + 1 +
    logBd (12 * s * m) + 1 +
    (4 * 2 ^ Nat.clog 2 (12 * s * m) + 5 * Nat.clog 2 (12 * s * m) + 7) + 1 +
    (2 * q₂ + 2) + 1 + MatrixUnaryDivision.exactTime q₂ (2 ^ Nat.clog 2 (12 * s * m))

theorem bank_inl (W : RK → List Bool) (G : LS → List Bool) (i : Fin 13) :
    bank ιL W G (.inl i) = W (.inl i) :=
  bank_outside ιL W G (.inl i) (by rintro ⟨k, hk⟩; cases hk)

theorem bank_inr (W : RK → List Bool) (G : LS → List Bool) (x : LS) :
    bank ιL W G (.inr x) = G x := bank_at ιL W G x

theorem rep_run (s q₂ m : ℕ) :
    ∃ t ≤ repBd s q₂ m, ∃ vc, ∃ c : ETHParameterScaleMachineLogCopy.logMachine.Config,
      ((advance repProg)^[t])
          (⟨some repStart, repCtl, R0 s q₂ m⟩ : TM2.Cfg (fun _ : RK => Bool) _ _) =
        ⟨none, vc, Sum.elim (fin1 s q₂ m)
          (ETHParameterScaleMachineLogCopy.afterLog (u (12 * s * m)) c).stk⟩ ∧
      (ETHParameterScaleMachineLogCopy.afterLog (u (12 * s * m)) c).stk
          (ETHParameterScaleMachineLogCopy.logStack
            ETHParameterScaleMachineLogCopy.logMachine.output) =
        u (Nat.clog 2 (12 * s * m)) ∧
      (ETHParameterScaleMachineLogCopy.afterLog (u (12 * s * m)) c).stk (.inl 0) =
        u (12 * s * m) := by
  -- (1) twelve marks
  have h1 := push12_run (R0 s q₂ m) false rfl
  obtain ⟨S1, hS1⟩ : ∃ S, S = Function.update (R0 s q₂ m) tC (u 12) := ⟨_, rfl⟩
  rw [← hS1] at h1
  -- (2) u (12 * s)
  have h2 := MatrixStage4ScalarPreparationOps.multiply_run ιM1 S1 12 s
    (by rw [hS1]; rfl) (by rw [hS1]; rfl) (by rw [hS1]; rfl) (by rw [hS1]; rfl)
    (by rw [hS1]; rfl)
  obtain ⟨S2, hS2⟩ : ∃ S, S = Function.update S1 wC (u (12 * s)) := ⟨_, rfl⟩
  have e2 : Function.update S1 (ιM1 5) (List.replicate (12 * s) true ++ S1 (ιM1 5)) = S2 := by
    rw [show S1 (ιM1 5) = [] by rw [hS1]; rfl, List.append_nil, hS2]; rfl
  rw [e2] at h2
  -- (3) u (12 * s * m) into the log source
  have h3 := MatrixStage4ScalarPreparationOps.multiply_run ιM2 S2 (12 * s) m
    (by rw [hS2]; rfl) (by rw [hS2, hS1]; rfl) (by rw [hS2, hS1]; rfl)
    (by rw [hS2, hS1]; rfl) (by rw [hS2, hS1]; rfl)
  obtain ⟨S3, hS3⟩ : ∃ S, S = Function.update S2 srcL (u (12 * s * m)) := ⟨_, rfl⟩
  have e3 : Function.update S2 (ιM2 5) (List.replicate (12 * s * m) true ++ S2 (ιM2 5)) = S3 := by
    rw [show S2 (ιM2 5) = [] by rw [hS2, hS1]; rfl, List.append_nil, hS3]; rfl
  rw [e3] at h3
  -- (4) the log call
  have hW : ∀ x : LS, S3 (.inr x) = region (12 * s * m) x := by
    intro x
    rw [hS3, hS2, hS1]
    by_cases hx : x = .inl 0
    · subst hx
      rw [show (Sum.inr (Sum.inl 0) : RK) = srcL from rfl, Function.update_self, region, if_pos rfl]
    · have hne : (Sum.inr x : RK) ≠ srcL := by
        intro h; exact hx (Sum.inr_injective h)
      rw [Function.update_of_ne hne, Function.update_of_ne (by simp [wC]),
        Function.update_of_ne (by simp [tC]), region, if_neg hx]
      rfl
  obtain ⟨t4, ht4, c, h4, ho4, hs4⟩ := log_lift S3 (12 * s * m) hW
  obtain ⟨G, hG⟩ : ∃ G, G = (ETHParameterScaleMachineLogCopy.afterLog (u (12 * s * m)) c).stk :=
    ⟨_, rfl⟩
  rw [← hG] at h4 ho4 hs4
  obtain ⟨S4, hS4⟩ : ∃ S, S = bank ιL S3 G := ⟨_, rfl⟩
  rw [← hS4] at h4
  have s4l : ∀ i : Fin 13, S4 (.inl i) = S3 (.inl i) := fun i => by rw [hS4, bank_inl]
  have s4r : ∀ x : LS, S4 (.inr x) = G x := fun x => by rw [hS4, bank_inr]
  -- (5) the power call
  have h5 := MatrixStage4ScalarPreparationOps.unary_power_run ιP S4 (Nat.clog 2 (12 * s * m))
    (by show S4 outL = _; rw [outL, s4r]; exact ho4)
    (by show S4 (.inl 9) = _; rw [s4l, hS3, hS2, hS1]; rfl)
    (by show S4 (.inl 6) = _; rw [s4l, hS3, hS2, hS1]; rfl)
    (by show S4 (.inl 7) = _; rw [s4l, hS3, hS2, hS1]; rfl)
  obtain ⟨t5, ht5, h5⟩ := h5
  obtain ⟨S5, hS5⟩ : ∃ S, S = Function.update S4 pC (u (2 ^ Nat.clog 2 (12 * s * m))) :=
    ⟨_, rfl⟩
  have e5 : Function.update S4 (ιP (.inl 0))
      (List.replicate (2 ^ Nat.clog 2 (12 * s * m)) true) = S5 := by rw [hS5]; rfl
  rw [e5] at h5
  -- (6) copy u q₂ into the dividend
  have hz5 : S5 (ιC 2) = [] := by
    show S5 (.inl 5) = []
    rw [hS5, Function.update_of_ne (by simp [pC]), s4l, hS3, hS2, hS1]; rfl
  have h6 := MatrixStage4ScalarPreparationOps.copy_run ιC S5 hz5
  have q5 : S5 (ιC 0) = u q₂ := by
    show S5 (.inl 1) = _
    rw [hS5, Function.update_of_ne (by simp [pC]), s4l, hS3, hS2, hS1]; rfl
  have d5 : S5 (ιC 1) = [] := by
    show S5 (.inl 10) = _
    rw [hS5, Function.update_of_ne (by simp [pC]), s4l, hS3, hS2, hS1]; rfl
  rw [q5, d5, List.append_nil, u, List.length_replicate] at h6
  obtain ⟨S6, hS6⟩ : ∃ S, S = Function.update S5 dC (u q₂) := ⟨_, rfl⟩
  have e6 : Function.update S5 (ιC 1) (List.replicate q₂ true) = S6 := by rw [hS6]; rfl
  rw [e6] at h6
  -- (7) the division
  have hpos : 0 < 2 ^ Nat.clog 2 (12 * s * m) := Nat.two_pow_pos _
  have s6 : ∀ i : Fin 13, i ≠ 9 → i ≠ 10 → S6 (.inl i) = S3 (.inl i) := by
    intro i h9 h10
    rw [hS6, Function.update_of_ne (by simpa [dC] using h10), hS5,
      Function.update_of_ne (by simpa [pC] using h9), s4l]
  have h7 := div_run ιD S6 q₂ (2 ^ Nat.clog 2 (12 * s * m)) hpos
    (by show S6 (.inl 10) = _; rw [hS6]; simp [dC])
    (by show S6 (.inl 9) = _; rw [hS6, Function.update_of_ne (by simp [dC, pC]), hS5]; simp [pC])
    (by show S6 (.inl 6) = _; rw [s6 _ (by decide) (by decide), hS3, hS2, hS1]; rfl)
    (by show S6 (.inl 11) = _; rw [s6 _ (by decide) (by decide), hS3, hS2, hS1]; rfl)
    (by show S6 (.inl 12) = _; rw [s6 _ (by decide) (by decide), hS3, hS2, hS1]; rfl)
    (by show S6 (.inl 7) = _; rw [s6 _ (by decide) (by decide), hS3, hS2, hS1]; rfl)
  -- the exit bank
  have r0 : ∀ i : Fin 13, i ≠ 3 → i ≠ 4 → i ≠ 9 → i ≠ 10 → S6 (.inl i) = R0 s q₂ m (.inl i) := by
    intro i h3 h4 h9 h10
    rw [s6 i h9 h10, hS3, Function.update_of_ne (by simp [srcL]), hS2,
      Function.update_of_ne (by simpa [wC] using h4), hS1, Function.update_of_ne (by simpa [tC] using h3)]
  have v3 : S6 (.inl 3) = fin1 s q₂ m 3 := by
    rw [s6 3 (by decide) (by decide), hS3, Function.update_of_ne (by simp [srcL]), hS2,
      Function.update_of_ne (by simp [wC]), hS1, Function.update_apply]; exact (if_pos rfl).trans rfl
  have v4 : S6 (.inl 4) = fin1 s q₂ m 4 := by
    rw [s6 4 (by decide) (by decide), hS3, Function.update_of_ne (by simp [srcL]), hS2,
      Function.update_apply]; exact (if_pos rfl).trans rfl
  have v9 : S6 (.inl 9) = fin1 s q₂ m 9 := by
    rw [hS6, Function.update_of_ne (by simp [dC]), hS5, Function.update_apply]; exact (if_pos rfl).trans rfl
  have hfin : Function.update (Function.update (Function.update S6 (ιD 0) []) (ιD 3)
      (u (q₂ % 2 ^ Nat.clog 2 (12 * s * m)))) (ιD 4) (u (q₂ / 2 ^ Nat.clog 2 (12 * s * m))) =
      Sum.elim (fin1 s q₂ m) G := by
    funext x
    rcases x with i | x
    · change Function.update (Function.update (Function.update S6 (.inl 10) []) (.inl 11) _)
        (.inl 12) _ (.inl i) = fin1 s q₂ m i
      fin_cases i
      · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; rw [r0 _ (by decide) (by decide) (by decide) (by decide)]; rfl
      · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; rw [r0 _ (by decide) (by decide) (by decide) (by decide)]; rfl
      · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; rw [r0 _ (by decide) (by decide) (by decide) (by decide)]; rfl
      · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; exact v3
      · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; exact v4
      · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; rw [r0 _ (by decide) (by decide) (by decide) (by decide)]; rfl
      · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; rw [r0 _ (by decide) (by decide) (by decide) (by decide)]; rfl
      · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; rw [r0 _ (by decide) (by decide) (by decide) (by decide)]; rfl
      · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; rw [r0 _ (by decide) (by decide) (by decide) (by decide)]; rfl
      · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; exact v9
      · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_apply]; exact (if_pos rfl).trans rfl
      · rw [Function.update_of_ne (by simp), Function.update_apply]; exact (if_pos rfl).trans rfl
      · rw [Function.update_apply]; exact (if_pos rfl).trans rfl
    · change Function.update (Function.update (Function.update S6 (.inl 10) []) (.inl 11) _)
        (.inl 12) _ (.inr x) = G x
      rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp),
        Function.update_of_ne (by simp), hS6, Function.update_of_ne (by simp [dC]), hS5,
        Function.update_of_ne (by simp [pC]), s4r]
  rw [hfin] at h7
  -- chain
  obtain ⟨a1, ha1, R1⟩ := BitMachineRawSequence.runs push12 mul1 () MatrixAddressMachine.Label.outer
    false false false false _ _ _ 1 _ h1 h2
  obtain ⟨a2, ha2, R2⟩ := BitMachineRawSequence.runs r1 mul2 (leftLabel ())
    MatrixAddressMachine.Label.outer k1 _ false _ _ _ _ a1 _ R1 h3
  obtain ⟨a3, ha3, R3⟩ := BitMachineRawSequence.runs r2 logP (leftLabel (leftLabel ()))
    (.inl .scan) k2 _ logCtl _ _ _ _ a2 t4 R2 h4
  obtain ⟨a4, ha4, R4⟩ := BitMachineRawSequence.runs r3 powP (leftLabel (leftLabel (leftLabel ())))
    (.inr false) k3 _ powCtl _ _ _ _ a3 t5 R3 h5
  obtain ⟨a5, ha5, R5⟩ := BitMachineRawSequence.runs r4 cpQ
    (leftLabel (leftLabel (leftLabel (leftLabel ())))) BitMachineCopy.Label.scan k4 _
    (none : Option Bool) _ _ _ _ a4 _ R4 h6
  obtain ⟨a6, ha6, R6⟩ := BitMachineRawSequence.runs r5 divP
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel ())))))
    MatrixUnaryDivision.Label.start k5 _ false _ _ _ _ a5 _ R5 h7
  refine ⟨a6, ?_, (k5, false), c, ?_, ?_, ?_⟩
  · unfold repBd
    omega
  · rw [← hG]; exact R6
  · rw [← hG]; exact ho4
  · rw [← hG]; exact hs4

end

#print axioms div_run
#print axioms log_lift
#print axioms push12_run
#print axioms rep_run

end Paper2.RepProducer
