import Paper2.LProducer

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

/-! ### Part lemmas -/

theorem cp_run (a b : LK) (hab : a ≠ b) (ha : a ≠ z) (hb : b ≠ z) (S : LK → List Bool)
    (hz : S z = []) :
    ((advance (cp a b hab ha hb))^[2 * (S a).length + 2])
        (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : LK => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update S b (S a ++ S b)⟩ :=
  MatrixStage4ScalarPreparationOps.copy_run (cpE a b hab ha hb) S hz

theorem pw_run (o e : LK) (h1 : o ≠ x1) (h2 : o ≠ x2) (h3 : o ≠ e) (h4 : e ≠ x1) (h5 : e ≠ x2)
    (S : LK → List Bool) (a : ℕ) (hs : S e = u a) (h0 : S o = []) (h6 : S x1 = [])
    (h7 : S x2 = []) :
    ∃ t ≤ 4 * 2 ^ a + 5 * a + 7,
      ((advance (pw o e h1 h2 h3 h4 h5))^[t])
          (⟨some (.inr false), powCtl, S⟩ : TM2.Cfg (fun _ : LK => Bool)
            MatrixUnaryPower.Label MatrixUnaryPower.Control) =
        ⟨none, powCtl, Function.update S o (u (2 ^ a))⟩ :=
  MatrixStage4ScalarPreparationOps.unary_power_run (powE o e h1 h2 h3 h4 h5) S a hs h0 h6 h7

def pushK (a : LK) : ℕ → (LK → List Bool) → LK → List Bool
  | 0, S => S
  | k + 1, S => Function.update (pushK a k S) a (true :: pushK a k S a)

theorem pushK_eq (a : LK) (k : ℕ) (S : LK → List Bool) :
    pushK a k S = Function.update S a (List.replicate k true ++ S a) := by
  induction k with
  | zero => simp [pushK]
  | succ k ih =>
      rw [pushK, ih, Function.update_self, Function.update_idem, List.replicate_succ,
        List.cons_append]

theorem push1_run (S : LK → List Bool) (v : Bool) :
    ((advance push1)^[1]) (⟨some (), v, S⟩ : TM2.Cfg (fun _ : LK => Bool) Unit Bool) =
      ⟨none, v, Function.update S c1 (true :: S c1)⟩ := rfl

theorem pushC_run (S : LK → List Bool) (v : Bool) :
    ((advance pushC)^[1]) (⟨some (), v, S⟩ : TM2.Cfg (fun _ : LK => Bool) Unit Bool) =
      ⟨none, v, pushK oe 32 (pushK es 16 (pushK ep 6 S))⟩ := rfl

theorem pop2_run (S : LK → List Bool) (v : Bool) :
    ((advance pop2)^[1]) (⟨some (), v, S⟩ : TM2.Cfg (fun _ : LK => Bool) Unit Bool) =
      ⟨none, v, Function.update (Function.update S q1C (S q1C).tail) q1C
        ((Function.update S q1C (S q1C).tail) q1C).tail⟩ := rfl

def region (n : ℕ) : LS → List Bool := fun x => if x = .inl 0 then u n else []

theorem start_stk (q : List Bool) :
    (ETHParameterScaleMachineLogCopy.start q).stk = fun x => if x = .inl 0 then q else [] := by
  change BitMachineStackEmbedding.bank ETHParameterScaleMachineLogCopy.copyStack (fun _ => [])
    (BitMachineCopy.cfg (some .scan) none q [] []).stk = _
  funext k
  by_cases hk : ∃ p : Fin 3, ETHParameterScaleMachineLogCopy.copyStack p = k
  · obtain ⟨p, rfl⟩ := hk
    rw [BitMachineStackEmbedding.bank_at]
    fin_cases p <;> simp [ETHParameterScaleMachineLogCopy.copyStack, BitMachineCopy.cfg]
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hk]
    have hne : k ≠ (.inl (0 : Fin 1) : LS) := by
      intro he
      exact hk ⟨0, by simpa [ETHParameterScaleMachineLogCopy.copyStack] using he.symm⟩
    simp [hne]

def logBd (n : ℕ) : ℕ := 2 * n + 2 + (UnaryBinaryEncoding.coefficient + 6) * (n + 1) ^ 2

theorem log_lift (i : Fin 2) (W : LK → List Bool) (n : ℕ)
    (hW : ∀ x : LS, W (.inr (i, x)) = region n x) :
    ∃ t ≤ logBd n, ∃ g : ETHParameterScaleMachineLogCopy.logMachine.Config,
      ((advance (logL i))^[t])
          (⟨some (.inl .scan), logCtl, W⟩ : TM2.Cfg (fun _ : LK => Bool) _ _) =
        ⟨none, (none, g.var),
          bank (ιR i) W (ETHParameterScaleMachineLogCopy.afterLog (u n) g).stk⟩ ∧
      (ETHParameterScaleMachineLogCopy.afterLog (u n) g).stk
          (ETHParameterScaleMachineLogCopy.logStack
            ETHParameterScaleMachineLogCopy.logMachine.output) = u (Nat.clog 2 n) := by
  obtain ⟨t, g, ht, hr, hh, ho⟩ := ETHParameterScaleMachineLogCopy.copied_log_run n
  have hs := BitMachineStackRun.run (ιR i) W ETHParameterScaleMachineLogCopy.program
    (ETHParameterScaleMachineLogCopy.start (u n)) t
  change _ = stackCfg (ιR i) W (ETHParameterScaleMachineLogCopy.run t _) at hs
  have hr' : ETHParameterScaleMachineLogCopy.run t (ETHParameterScaleMachineLogCopy.start (u n)) =
      ETHParameterScaleMachineLogCopy.afterLog (u n) g := hr
  rw [hr'] at hs
  have hb : bank (ιR i) W (ETHParameterScaleMachineLogCopy.start (u n)).stk = W := by
    apply bank_eq_self
    intro x
    rw [start_stk]
    show (if x = .inl 0 then u n else []) = W (.inr (i, x))
    rw [hW]
    rfl
  have hst : stackCfg (ιR i) W (ETHParameterScaleMachineLogCopy.start (u n)) =
      (⟨some (.inl .scan), logCtl, W⟩ : TM2.Cfg (fun _ : LK => Bool) _ _) := by
    simp only [stackCfg]
    rw [hb]
    rfl
  rw [hst] at hs
  have hl : (ETHParameterScaleMachineLogCopy.afterLog (u n) g).l = none := by
    simp [ETHParameterScaleMachineLogCopy.afterLog, BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, hh]
  refine ⟨t, by unfold logBd; exact ht, g, ?_, ?_⟩
  · refine hs.trans ?_
    simp only [stackCfg]
    rw [hl]
    rfl
  · exact (ETHParameterScaleMachineLogCopy.afterLog_output n g).trans ho

theorem u_app (a b : ℕ) : u a ++ u b = u (a + b) := (List.replicate_add a b true).symm

end

end Paper2.LProducer
