import CurrentAdditive.YaoCutScanLoop
import EthInapproximability.CurrentPaper.SourceAffineUnary
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

/-! Embed the checked fixed-coefficient unary machine into a Fin16 bank. -/

namespace CurrentAdditive.SmallBias.YaoThresholdAffine

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding

def affineProgram (p : Nat × Nat) (ι : Fin 3 ↪ Fin 16) :=
  fun l => stackStmt ι (SourceAffineUnary.program p l)

theorem affine_run (p : Nat × Nat) (ι : Fin 3 ↪ Fin 16)
    (S : Fin 16 → List Bool) (n : ℕ)
    (h0 : S (ι 0) = List.replicate n true)
    (h1 : S (ι 1) = []) (h2 : S (ι 2) = []) :
    ((advance (affineProgram p ι))^[
      ((SourceAffineUnary.vertexCoefficient p + 1) * n + 1) +
      ((SourceAffineUnary.rowCoefficient p + 1) * 0 + 1)])
      (⟨some .vertexScan, none, S⟩ : TM2.Cfg (fun _ : Fin 16 => Bool)
        (SourceAffineUnary.Label p) (Option Bool)) =
      ⟨none, none,
        Function.update (Function.update S (ι 0) []) (ι 2)
          (List.replicate (SourceAffineUnary.vertexCoefficient p * n) true)⟩ := by
  let c : SourceAffineUnary.Config p := SourceAffineUnary.cfg (some .vertexScan) none
    (List.replicate n true) [] []
  have hstart : stackCfg ι S c =
      (⟨some .vertexScan, none, S⟩ : TM2.Cfg (fun _ : Fin 16 => Bool)
        (SourceAffineUnary.Label p) (Option Bool)) := by
    dsimp [stackCfg, c, SourceAffineUnary.cfg]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [SourceAffineUnary.contents, h0, h1, h2]
  have hr := BitMachineStackRun.run ι S (SourceAffineUnary.program p) c
    (((SourceAffineUnary.vertexCoefficient p + 1) * n + 1) +
      ((SourceAffineUnary.rowCoefficient p + 1) * 0 + 1))
  rw [hstart] at hr
  change _ = stackCfg ι S (SourceAffineUnary.run p _ c) at hr
  have hlocal : SourceAffineUnary.run p
      (((SourceAffineUnary.vertexCoefficient p + 1) * n + 1) +
        ((SourceAffineUnary.rowCoefficient p + 1) * 0 + 1)) c =
      SourceAffineUnary.cfg none none [] []
        (List.replicate (SourceAffineUnary.vertexCoefficient p * n) true) := by
    simpa only [c, List.replicate_zero, Nat.mul_zero, Nat.add_zero] using
      SourceAffineUnary.run_correct p n 0
  rw [hlocal] at hr
  have hfinish : stackCfg ι S
      (SourceAffineUnary.cfg none none [] []
        (List.replicate (SourceAffineUnary.vertexCoefficient p * n) true)) =
      (⟨none, none,
        Function.update (Function.update S (ι 0) []) (ι 2)
          (List.replicate (SourceAffineUnary.vertexCoefficient p * n) true)⟩ :
        TM2.Cfg (fun _ : Fin 16 => Bool)
          (SourceAffineUnary.Label p) (Option Bool)) := by
    dsimp [stackCfg, SourceAffineUnary.cfg]
    congr 1
    have hloc : SourceAffineUnary.contents [] []
        (List.replicate (SourceAffineUnary.vertexCoefficient p * n) true) =
        Function.update
          (Function.update (fun k : Fin 3 => S (ι k)) 0 []) 2
          (List.replicate (SourceAffineUnary.vertexCoefficient p * n) true) := by
      funext k
      fin_cases k <;> simp [SourceAffineUnary.contents, h1]
    rw [hloc, bank_update, bank_update, bank_restrict]
  exact hr.trans hfinish

#print axioms affine_run

end CurrentAdditive.SmallBias.YaoThresholdAffine
