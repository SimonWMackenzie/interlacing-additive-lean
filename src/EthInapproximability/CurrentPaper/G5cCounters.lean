import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
# The two unary `2^p` counters PRODUCED from unary `p` (private lane owner:b-g5-3, segment 2)

Audit F3a/F3b: the pad writer's start bank `MatrixTableWriter.ready bank (2^p) (2^p) ..` holds unary
`2^p` row/column counters that were INSERTED. Here ONE fixed program (two copies of the admitted
`MatrixStage4ScalarPreparationOps.unaryPowerProgram`, sequenced by the admitted
`BitMachineRawSequence.program`) produces both counters from unary `p`, on ANY bank type `K`, with
the exit bank stated exactly (both counters written, unary `p` and every other cell unchanged, the
shared scratch cells blank again) within `2 (4 * 2^p + 5 p + 7) + 1` steps.

NOT claimed: the join of this bank with the pad writer's bank layout (`MatrixTableWriter.ready`) or
with the shell exit bank; parsing `p` from an encoded input.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5cCounters

open Turing BitMachineEncoding BitMachineStackEmbedding

variable {K : Type} [DecidableEq K]

/-- Counter `i`'s embedding: target cell `tgt`, shared scratch `s1 s2`, shared exponent `e`. -/
def emb (tgt s1 s2 e : K) (h : [tgt, s1, s2, e].Nodup) : MatrixUnaryPower.Stack ↪ K where
  toFun
    | .inl 0 => tgt
    | .inl 1 => s1
    | .inl _ => s2
    | .inr () => e
  inj' := by
    intro a b hab
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at h
    obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := h
    rcases a with a | a <;> rcases b with b | b
    · fin_cases a <;> fin_cases b <;> simp_all
    · cases b; fin_cases a <;> simp_all
    · cases a; fin_cases b <;> simp_all
    · cases a; cases b; rfl

/-- ONE fixed program writing both counters. -/
def countersProgram (r c s1 s2 e : K) (hr : [r, s1, s2, e].Nodup) (hc : [c, s1, s2, e].Nodup) :=
  BitMachineRawSequence.program
    (MatrixStage4ScalarPreparationOps.unaryPowerProgram (emb r s1 s2 e hr))
    (MatrixStage4ScalarPreparationOps.unaryPowerProgram (emb c s1 s2 e hc))
    (.inr false) ((false, false), none) ((false, false), none)

theorem counters_run (r c s1 s2 e : K) (hr : [r, s1, s2, e].Nodup) (hc : [c, s1, s2, e].Nodup)
    (hrc : r ≠ c) (S : K → List Bool) (p : ℕ)
    (he : S e = List.replicate p true) (hR : S r = []) (hC : S c = [])
    (h1 : S s1 = []) (h2 : S s2 = []) :
    ∃ t ≤ 2 * (4 * 2 ^ p + 5 * p + 7) + 1,
      ((advance (countersProgram r c s1 s2 e hr hc))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inr false)),
          (((false, false), none), ((false, false), none)), S⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, (((false, false), none), ((false, false), none)),
          Function.update (Function.update S r (List.replicate (2 ^ p) true)) c
            (List.replicate (2 ^ p) true)⟩ := by
  have hr' := hr
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hr'
  obtain ⟨⟨hr1, hr2, hr3⟩, -, -, -⟩ := hr'
  obtain ⟨t1, ht1, q1⟩ := MatrixStage4ScalarPreparationOps.unary_power_run
    (emb r s1 s2 e hr) S p he hR h1 h2
  let S1 := Function.update S r (List.replicate (2 ^ p) true)
  have he1 : S1 e = List.replicate p true := by
    simp only [S1]; rw [Function.update_of_ne (Ne.symm hr3)]; exact he
  have hC1 : S1 c = [] := by
    simp only [S1]; rw [Function.update_of_ne (Ne.symm hrc)]; exact hC
  have h11 : S1 s1 = [] := by
    simp only [S1]; rw [Function.update_of_ne (Ne.symm hr1)]; exact h1
  have h21 : S1 s2 = [] := by
    simp only [S1]; rw [Function.update_of_ne (Ne.symm hr2)]; exact h2
  obtain ⟨t2, ht2, q2⟩ := MatrixStage4ScalarPreparationOps.unary_power_run
    (emb c s1 s2 e hc) S1 p he1 hC1 h11 h21
  obtain ⟨t, ht, q⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.unaryPowerProgram (emb r s1 s2 e hr))
    (MatrixStage4ScalarPreparationOps.unaryPowerProgram (emb c s1 s2 e hc))
    (.inr false) (.inr false) _ _ _ _ _ _ _ t1 t2 q1 q2
  exact ⟨t, by omega, q⟩

#print axioms counters_run

end EthInapproximability.CurrentPaper.G5cCounters
