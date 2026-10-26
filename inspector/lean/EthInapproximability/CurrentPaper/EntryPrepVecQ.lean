import EthInapproximability.CurrentPaper.VectorsFromGraphQ
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-!
# Segment 5b (part 1): the admitted q/vectors controller with a growth bound on its scratch

Lane owner:b-stage4-entry-program-7 (Paper B, unit 2, map item 3).

`vectors_growth` is the admitted `VectorsFromGraphQ.vectors_from_graph_bytes` (same fixed
program, same start bank, same exact `Z` exit bank, same stated `QProduct` cells), with ONE
additional conjunct: every cell of the existential `QProduct` scratch `F` has length at most
its start length plus `perStep QArithmeticJoined.program * QArithmeticJoined.cost s |E|`
(admitted `BitMachineStackGrowth.run_growth` applied to the arithmetic phase, the only phase
that writes that region). This is what a charged clear of the region needs for a public clock.
The proof re-runs the admitted phase theorems `phA1`, `phA2`, `phA3`, `phA5`, `pB` and
re-proves `phA4` with the growth conjunct (`phA4g`).
-/

namespace EthInapproximability.CurrentPaper.EntryPrepVec

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open VectorsFromGraphQ
open VectorsProducer (Z b inp)

noncomputable section

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The growth allowance of the arithmetic scratch. -/
def growQ (s e : ℕ) : ℕ :=
  BitMachineStackGrowth.perStep QArithmeticJoined.program * QArithmeticJoined.cost s e

theorem phA4g (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ∃ t ≤ QArithmeticJoined.cost s (Fintype.card E),
      ∃ F : QS → List Bool,
        ((advance arithQ)^[t])
          (⟨some (BitMachineRawSequence.leftLabel QProductJoined.start),
            QArithmeticJoined.initial, Sum.elim (Z0 G s output) (Qa G s)⟩ :
            TM2.Cfg (fun _ : Z2 => Bool) _ _) =
          ⟨none, QArithmeticJoined.initial, Sum.elim (Z0 G s output) F⟩ ∧
        F QProduct.q = List.replicate (q2 G s) true ∧
        (∀ j : GraphCountBridge.Stack,
          j ≠ (.inr (56 : Fin 64)) → F (.inl j) = Qa G s (.inl j)) ∧
        (∀ j : QS, (F j).length ≤ (Qa G s j).length + growQ s (Fintype.card E)) := by
  obtain ⟨t, ht, F, hrun, hq, hframe⟩ := QArithmeticJoined.run (Qa G s) s (Fintype.card E)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl
  refine ⟨t, ht, F, ?_, hq, hframe, ?_⟩
  · have hl := BitMachineStackRun.run qInj (Sum.elim (Z0 G s output) (Qa G s))
      QArithmeticJoined.program
      (⟨some (BitMachineRawSequence.leftLabel QProductJoined.start),
        QArithmeticJoined.initial, Qa G s⟩ : TM2.Cfg (fun _ : QS => Bool) _ _) t
    rw [hrun] at hl
    have hs : bank qInj (Sum.elim (Z0 G s output) (Qa G s)) (Qa G s) =
        Sum.elim (Z0 G s output) (Qa G s) :=
      bank_eq_self _ _ _ (fun _ => rfl)
    have hf : bank qInj (Sum.elim (Z0 G s output) (Qa G s)) F =
        Sum.elim (Z0 G s output) F := by
      funext j
      rcases j with z | k
      · rw [bank_outside]
        · rfl
        · rintro ⟨k, hk⟩
          cases hk
      · exact bank_at qInj _ F k
    simp only [stackCfg, hs, hf] at hl
    exact hl
  · intro j
    have hg := BitMachineStackGrowth.run_growth QArithmeticJoined.program
      (⟨some (BitMachineRawSequence.leftLabel QProductJoined.start),
        QArithmeticJoined.initial, Qa G s⟩ : TM2.Cfg (fun _ : QS => Bool) _ _) t j
    rw [hrun] at hg
    have hm : BitMachineStackGrowth.perStep QArithmeticJoined.program * t ≤
        growQ s (Fintype.card E) := Nat.mul_le_mul_left _ ht
    exact le_trans hg (Nat.add_le_add_left hm _)

theorem vectors_growth (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ∃ t ≤ fullBound G s, ∃ v, ∃ F : QS → List Bool,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), initial,
          Sum.elim (Z0 G s output) Q0⟩ : TM2.Cfg (fun _ : Z2 => Bool) _ _) =
        ⟨none, v, Sum.elim (VectorsProducer.exitBank G s output) F⟩ ∧
      F QProduct.q = List.replicate (q2 G s) true ∧
      (∀ j : GraphCountBridge.Stack,
        j ≠ (.inr (56 : Fin 64)) → F (.inl j) = Qa G s (.inl j)) ∧
      (∀ j : QS, (F j).length ≤ (Qa G s j).length + growQ s (Fintype.card E)) := by
  obtain ⟨t4, ht4, F, h4, hq, hframe, hgrow⟩ := phA4g G s output
  obtain ⟨tB, htB, vB, hB⟩ := pB G s output F
  obtain ⟨u5, hu5, r5⟩ := BitMachineRawSequence.runs (copyProgram sA5) prodZ
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none j5 vB (Sum.elim (Z0 G s output) F) (Sum.elim (VectorsProducer.B0 G s output) F)
    (Sum.elim (VectorsProducer.exitBank G s output) F) (2 * q2 G s + 2) tB
    (phA5 G s output F hq) hB
  obtain ⟨u4, hu4, r4⟩ := BitMachineRawSequence.runs arithQ a5
    (BitMachineRawSequence.leftLabel QProductJoined.start)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    QArithmeticJoined.initial QArithmeticJoined.initial j4 (none, vB)
    (Sum.elim (Z0 G s output) (Qa G s)) (Sum.elim (Z0 G s output) F)
    (Sum.elim (VectorsProducer.exitBank G s output) F) t4 u5 h4 r5
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs (copyProgram sA3) a4
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel QProductJoined.start))
    none none j3 (QArithmeticJoined.initial, (none, vB))
    (Sum.elim (Z0 G s output) (Qd G)) (Sum.elim (Z0 G s output) (Qa G s))
    (Sum.elim (VectorsProducer.exitBank G s output) F) (2 * s + 2) u4 (phA3 G s output) r4
  obtain ⟨t2, ht2, h2⟩ := phA2 G s output
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs decQ a3
    (Sum.inr SourceNormalizationMachineDecode.Admin.gate)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    VectorsProducer.ctl0 (SourceNormalizationMachineDecode.doneControl true) j2
    (none, (QArithmeticJoined.initial, (none, vB)))
    (Sum.elim (Z0 G s output) (Q1 G)) (Sum.elim (Z0 G s output) (Qd G))
    (Sum.elim (VectorsProducer.exitBank G s output) F) t2 u3 h2 r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs (copyProgram sA1) a2
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel
      (Sum.inr SourceNormalizationMachineDecode.Admin.gate :
        SourceNormalizationMachineDecode.Label))
    none none j1 (VectorsProducer.ctl0, (none, (QArithmeticJoined.initial, (none, vB))))
    (Sum.elim (Z0 G s output) Q0) (Sum.elim (Z0 G s output) (Q1 G))
    (Sum.elim (VectorsProducer.exitBank G s output) F) _ u2 (phA1 G s output) r2
  refine ⟨u1, ?_, _, F, r1, hq, hframe, hgrow⟩
  unfold fullBound
  omega

#print axioms phA4g
#print axioms vectors_growth

end
end EthInapproximability.CurrentPaper.EntryPrepVec
