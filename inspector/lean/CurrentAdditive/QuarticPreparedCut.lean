import Paper2.SamplerParameterJoin
import Paper2.SuccessOrient

/-! A schedule-parametric physical prefix cutter. It consumes literal public
numeric counts and an arbitrary raw word; no v12 schedule is substituted. -/

set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticPreparedCut

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

noncomputable local instance : DecidableEq SuccessOrient.Stack := Classical.decEq _
noncomputable local instance : DecidableEq SamplerParameterBank.Stack := Classical.decEq _

private theorem advance_irrel {K Λ σ : Type} (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (i j : DecidableEq K) :
    @advance K Λ σ i P = @advance K Λ σ j P := by
  have hij : i = j := by
    funext a b
    exact Subsingleton.elim _ _
  subst j
  rfl

noncomputable def program := by
  exact fun l => stackStmt SuccessOrient.preSlots
    (SamplerParameterJoin.preparedCleanupProgram l)

def count (n p s q₁ q₂ w Q k mX mY : ℕ) : ℕ :=
  let B := SamplerParameterJoin.B n p s q₁ q₂ w Q
  let R := SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY
  let N := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
  N * (R * B)

noncomputable def clock (n p s q₁ q₂ w Q k mX mY : ℕ) (raw : List Bool) : ℕ :=
  let B := SamplerParameterJoin.B n p s q₁ q₂ w Q
  let R := SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY
  let N := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
  let D := N * (R * B)
  SamplerParameterJoin.clock n p s q₁ q₂ w Q k mX mY +
    MatrixAddressMachine.exactTime R B 0 +
    MatrixAddressMachine.exactTime N (R * B) 0 +
    D + raw.length + R * B + D +
    (D + raw.length + 4) * BitMachineStackGrowth.perStep SamplerParameterJoin.cutProgram +
    (D + raw.length + 4) * BitMachineStackGrowth.perStep SamplerParameterJoin.cutProgram + 14

theorem run (n p s q₁ q₂ w Q k mX mY : ℕ) (raw : List Bool) :
    ∃ t ≤ clock n p s q₁ q₂ w Q k mX mY raw,
      ∃ H : SamplerParameterBank.Stack → List Bool,
      ((advance program)^[t])
        (⟨some (.inl (.inl (.inl SamplerParameterJoin.startLabel))),
          (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none)),
          SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY raw⟩ :
          TM2.Cfg (fun _ : SuccessOrient.Stack => Bool) _ _) =
        ⟨none,
          (((SamplerParameterJoin.finalControl, (false, false)), (none, ())), ((), none)),
          bank SuccessOrient.preSlots
            (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY raw) H⟩ ∧
      H (SamplerParameterJoin.bitCountSlot 0) =
        raw.take (count n p s q₁ q₂ w Q k mX mY) := by
  obtain ⟨t, F, H, ht, hr, -, hCut, -, -, -, -, -⟩ :=
    SamplerParameterJoin.prepared_cleanup_run n p s q₁ q₂ w Q k mX mY raw
  have h := BitMachineStackRun.run SuccessOrient.preSlots
    (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY raw)
    SamplerParameterJoin.preparedCleanupProgram
    (⟨some (.inl (.inl (.inl SamplerParameterJoin.startLabel))),
      (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none)),
      SamplerParameterJoin.startBank n p s q₁ q₂ w Q k mX mY raw⟩ :
      TM2.Cfg (fun _ : SamplerParameterBank.Stack => Bool) _ _) t
  have hr' : ((advance SamplerParameterJoin.preparedCleanupProgram)^[t])
      (⟨some (.inl (.inl (.inl SamplerParameterJoin.startLabel))),
        (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none)),
        SamplerParameterJoin.startBank n p s q₁ q₂ w Q k mX mY raw⟩ :
        TM2.Cfg (fun _ : SamplerParameterBank.Stack => Bool) _ _) =
      ⟨none, (((SamplerParameterJoin.finalControl, (false, false)), (none, ())), ((), none)), H⟩ := by
    convert hr using 1
    congr 1
    exact advance_irrel _ _ _
  have h' := h.trans (congrArg
    (stackCfg SuccessOrient.preSlots
      (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY raw)) hr')
  have hStart : bank SuccessOrient.preSlots
      (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY raw)
      (SamplerParameterJoin.startBank n p s q₁ q₂ w Q k mX mY raw) =
      SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY raw := by
    apply bank_eq_self
    intro x
    rfl
  simp only [stackCfg, hStart] at h'
  refine ⟨t, ?_, H, ?_, ?_⟩
  · simpa only [clock] using ht
  · exact h'
  · simpa only [count] using hCut

#print axioms run

end Paper2.CurrentAdditive.QuarticPreparedCut
