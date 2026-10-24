import EthInapproximability.CurrentPaper.SourceOriginalListPacketizerInit

/-! Physical embedded binary counter in the original-n packetizer. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalListPacketizer

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

noncomputable section

theorem run_succ {c d : Config} (h : advance program c = d) (t : ℕ) :
    run (t+1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, h]

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def counterFrame (S : Stack → List Bool)
    (c : SourceListMachineCounter.Config) : Config :=
  BitMachineStackEmbedding.cfg counterStack S counterLabel counterControl
    (some (adminLabel .afterCounter)) c

def loopCfg (S : Stack → List Bool) : Config :=
  ⟨some (counterLabel (.inr .scan)),
    counterControl SourceListMachineCounter.initialControl,S⟩

theorem counterFrame_initial (S : Stack → List Bool) (q : List Bool)
    (hq : S (.inr 2) = q) (hw : S (.inr 3) = []) :
    counterFrame S (SourceListMachineCounter.cfg (some (.inr .scan))
      SourceListMachineCounter.initialControl q []) = loopCfg S := by
  have h : ∀ k : SourceListMachineCounter.Stack,
      (SourceListMachineCounter.cfg (some (.inr .scan))
        SourceListMachineCounter.initialControl q []).stk k = S (counterStack k) := by
    intro k
    fin_cases k
    · exact hq.symm
    · exact hw.symm
  unfold counterFrame loopCfg BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg
  simp only [BitMachineInline.cfg]
  rw [BitMachineStackEmbedding.bank_eq_self counterStack _ _ h]
  rfl

theorem afterInit_step (S : Stack → List Bool) :
    advance program
      ⟨some (adminLabel .afterInit),
        initControl (SourceListMachineInitialize.doneControl true),S⟩ =
      loopCfg S := by
  simp only [advance, adminLabel, program, TM2.step, TM2.stepAux,
    Option.getD_some, loopCfg]
  simp [initControl, SourceListMachineInitialize.doneControl]

theorem counterFrame_halted (S : Stack → List Bool)
    (v : SourceListMachineCounter.Control) (q : List Bool) :
    counterFrame S (SourceListMachineCounter.cfg none v q []) =
      ⟨some (adminLabel .afterCounter),counterControl v,
        BitMachineStackEmbedding.bank counterStack S
          (SourceListMachineCounter.cfg none v q []).stk⟩ := rfl

theorem counter_embedded (S : Stack → List Bool) (q : List Bool) :
    ∃ t ≤ 4*q.length+5,
      run t (counterFrame S (SourceListMachineCounter.cfg
        (some (.inr .scan)) SourceListMachineCounter.initialControl q [])) =
      counterFrame S
        (match ProtocolBinaryCounter.subOne q with
          | none => SourceListMachineCounter.cfg none
              (SourceListMachineCounter.doneControl false) q []
          | some q' => SourceListMachineCounter.cfg none
              (SourceListMachineCounter.doneControl true) q' []) := by
  obtain ⟨t, ht, he⟩ := SourceListMachineCounter.counter_run q
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs counterStack S
    counterLabel counterControl (fun v => v.1.1.1.2)
    (by intro v; rfl) (some (adminLabel .afterCounter))
    SourceListMachineCounter.program program (fun _ => rfl)
    (SourceListMachineCounter.cfg (some (.inr .scan))
      SourceListMachineCounter.initialControl q []) t
    (by change (SourceListMachineCounter.run t _).l = none
        rw [he]
        cases ProtocolBinaryCounter.subOne q <;> rfl)
  change run u (counterFrame S _) =
    counterFrame S (SourceListMachineCounter.run t _) at hr
  rw [he] at hr
  exact ⟨u,hu.trans ht,hr⟩

theorem init_to_counter (n : ℕ) (xs : List (List Bool)) :
    ∃ t ≤ 5*xs.length.bits.length+7,
      run t (startCfg n (SourceListEncoding.encode xs)) =
        loopCfg (initBanks n (SourceListEncoding.encode xs)
          {input := SourceListEncoding.fields xs,
           count := xs.length.bits,
           output := (natField xs.length).reverse}) := by
  obtain ⟨t, ht, he⟩ := init_from_start n xs
  let d : SourceListMachineInitialize.Data :=
    {input := SourceListEncoding.fields xs,
     count := xs.length.bits,
     output := (natField xs.length).reverse}
  let S := initBanks n (SourceListEncoding.encode xs) d
  have hf := initFrame_halted n (SourceListEncoding.encode xs) d
  change run t _ = initFrame n _
    (SourceListMachineInitialize.cfg none
      (SourceListMachineInitialize.doneControl true) d) at he
  rw [hf] at he
  have hs := afterInit_step S
  refine ⟨t+1, by omega, ?_⟩
  rw [run_add he 1, run_succ hs 0]
  rfl

end

end EthInapproximability.CurrentPaper.SourceOriginalListPacketizer
