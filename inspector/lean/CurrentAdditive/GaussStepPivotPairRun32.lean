import CurrentAdditive.GaussStepPivotSplitRun32

/-! The fixed controller serializes the old `(r,c)` pivot pair. -/

namespace CurrentAdditive.GaussStepPivotPairRun32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

private theorem start_frame {m k : Nat}
    (p : Fin m × Fin k) (S : Stack → List Bool)
    (h17 : S 17 = List.replicate p.1.val true)
    (h18 : S 18 = List.replicate p.2.val true)
    (h29 : S 29 = []) (h30 : S 30 = []) (h28 : S 28 = []) :
    GaussPivotPairEmit32.frame S
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (GaussPivotPairEmit32.pairBank p.1.val p.2.val) [] [] []) =
      ⟨some (.inl (.emit 0)),none,S⟩ := by
  simp only [GaussPivotPairEmit32.frame,
    BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg]
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro j
  cases j with
  | inl j => fin_cases j <;>
      simp [BitMachineBankSerialize.cfg,
        BitMachineBankSerialize.contents,
        GaussPivotPairEmit32.locate,
        GaussPivotPairEmit32.pairBank,h17,h18]
  | inr j => fin_cases j <;>
      simp [BitMachineBankSerialize.cfg,
        BitMachineBankSerialize.contents,
        GaussPivotPairEmit32.locate,h29,h30,h28]

def result {m k : Nat} (p : Fin m × Fin k)
    (S : Stack → List Bool)
    (S' : BitMachineBankSerialize.Bank 2) : Config :=
  let c := GaussPivotPairEmit32.frame S
    (BitMachineBankSerialize.cfg none none S' [] []
      (GaussControlTrace.pivotPacket p))
  ⟨some .afterPair,ePair none,c.stk⟩

theorem pair_phase {m k : Nat}
    (p : Fin m × Fin k) (S : Stack → List Bool)
    (h17 : S 17 = List.replicate p.1.val true)
    (h18 : S 18 = List.replicate p.2.val true)
    (h29 : S 29 = []) (h30 : S 30 = []) (h28 : S 28 = []) :
    ∃ t ≤ 2*(GaussControlTrace.pivotPacket p).length+3,
      ∃ S' : BitMachineBankSerialize.Bank 2,
        run t ⟨some (.pair (.inl (.emit 0))),ePair none,S⟩ =
          result p S S' := by
  obtain ⟨a,ha,S',hpair⟩ := GaussPivotPairEmit32.physical_pair p S
  have hhalt : GaussPivotPairEmit32.run (a+1)
      (GaussPivotPairEmit32.frame S
        (BitMachineBankSerialize.cfg (some (.emit 0)) none
          (GaussPivotPairEmit32.pairBank p.1.val p.2.val) [] [] [])) =
      ⟨none,none,
        (GaussPivotPairEmit32.frame S
          (BitMachineBankSerialize.cfg none none S' [] []
            (GaussControlTrace.pivotPacket p))).stk⟩ := by
    change ((advance GaussPivotPairEmit32.program)^[a+1]) _ = _
    rw [Function.iterate_succ_apply',
      ← GaussPivotPairEmit32.run,hpair]
    rfl
  obtain ⟨u,hu,hglobal⟩ :=
    GaussStepPhaseLift32.pair_lift
      (GaussPivotPairEmit32.frame S
        (BitMachineBankSerialize.cfg (some (.emit 0)) none
          (GaussPivotPairEmit32.pairBank p.1.val p.2.val) [] [] []))
      (a+1) (by rw [hhalt])
  refine ⟨u, by omega, S', ?_⟩
  rw [start_frame p S h17 h18 h29 h30 h28] at hglobal
  have hh : GaussPivotPairEmit32.run (a+1)
      ⟨some (.inl (.emit 0)),none,S⟩ =
      ⟨none,none,
        (GaussPivotPairEmit32.frame S
          (BitMachineBankSerialize.cfg none none S' [] []
            (GaussControlTrace.pivotPacket p))).stk⟩ := by
    simpa [start_frame p S h17 h18 h29 h30 h28] using hhalt
  rw [hh] at hglobal
  simpa [BitMachineInline.cfg,result] using hglobal

theorem result_pair {m k : Nat}
    (p : Fin m × Fin k) (S : Stack → List Bool)
    (S' : BitMachineBankSerialize.Bank 2) :
    (result p S S').stk 28 = GaussControlTrace.pivotPacket p := by
  simpa [result] using GaussPivotPairEmit32.output_28 p S S'

theorem result_preserves {m k : Nat}
    (p : Fin m × Fin k) (S : Stack → List Bool)
    (S' : BitMachineBankSerialize.Bank 2)
    (j : Stack) (h17 : j ≠ 17) (h18 : j ≠ 18)
    (h28 : j ≠ 28) (h29 : j ≠ 29) (h30 : j ≠ 30) :
    (result p S S').stk j = S j := by
  change (BitMachineStackEmbedding.bank
    GaussPivotPairEmit32.locate S
    (BitMachineBankSerialize.cfg none none S' [] []
      (GaussControlTrace.pivotPacket p)).stk) j = S j
  exact BitMachineStackEmbedding.bank_outside
    GaussPivotPairEmit32.locate S _ j (by
      rintro ⟨q,hq⟩
      cases q with
      | inl q => fin_cases q <;>
          simp [GaussPivotPairEmit32.locate] at hq <;> simp_all
      | inr q => fin_cases q <;>
          simp [GaussPivotPairEmit32.locate] at hq <;> simp_all)

theorem result29_empty {m k : Nat}
    (p : Fin m × Fin k) (S : Stack → List Bool)
    (S' : BitMachineBankSerialize.Bank 2) :
    (result p S S').stk 29 = [] := by
  change (BitMachineStackEmbedding.bank
    GaussPivotPairEmit32.locate S
    (BitMachineBankSerialize.cfg none none S' [] []
      (GaussControlTrace.pivotPacket p)).stk)
      (GaussPivotPairEmit32.locate (.inr (0:Fin 3))) = []
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem result30_empty {m k : Nat}
    (p : Fin m × Fin k) (S : Stack → List Bool)
    (S' : BitMachineBankSerialize.Bank 2) :
    (result p S S').stk 30 = [] := by
  change (BitMachineStackEmbedding.bank
    GaussPivotPairEmit32.locate S
    (BitMachineBankSerialize.cfg none none S' [] []
      (GaussControlTrace.pivotPacket p)).stk)
      (GaussPivotPairEmit32.locate (.inr (1:Fin 3))) = []
  rw [BitMachineStackEmbedding.bank_at]
  rfl

#print axioms pair_phase
#print axioms result_pair
#print axioms result_preserves
#print axioms result29_empty
#print axioms result30_empty

end
end CurrentAdditive.GaussStepPivotPairRun32
