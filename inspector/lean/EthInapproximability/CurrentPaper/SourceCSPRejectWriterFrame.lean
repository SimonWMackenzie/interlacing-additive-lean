import EthInapproximability.CurrentPaper.SourceCSPRejectWriter
import EthInapproximability.CurrentPaper.SourceCSPGuardDispatch
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Rejecting-CNF output on the guarded CSP bank

The fixed rejecting writer clears and reuses the former unary-count cell.
All other input-side stacks, including the dispatch status and source suffix,
are foreign to this local output machine and remain unchanged.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRejectWriterFrame

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceCSPInputFrame.Stack

def outputSlot : Stack := .inr 6

def embedding : SourceCSPRejectWriter.Stack ↪ Stack where
  toFun := fun _ => outputSlot
  inj' := by intro x y _; fin_cases x; fin_cases y; rfl

def program (l : SourceCSPRejectWriter.Label) :
    TM2.Stmt (fun _ : Stack => Bool) SourceCSPRejectWriter.Label
      (Option Bool) :=
  stmt embedding id id id none (SourceCSPRejectWriter.program l)

theorem reject_run (before : Stack → List Bool) :
    ∃ t S, t ≤ (before outputSlot).length + 3 ∧
      ((advance program)^[t])
        (⟨some .clear, none, before⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            SourceCSPRejectWriter.Label (Option Bool)) =
        ⟨none, none, S⟩ ∧
      S outputSlot = SourceCSPRejectFormula.bits ∧
      (∀ k : Stack, k ≠ outputSlot → S k = before k) := by
  let localCfg : SourceCSPRejectWriter.Config :=
    ⟨some .clear, none,
      SourceCSPRejectWriter.contents (before outputSlot)⟩
  let n := (before outputSlot).length + 2
  have hr : ((advance SourceCSPRejectWriter.program)^[n]) localCfg =
      ⟨none, none,
        SourceCSPRejectWriter.contents SourceCSPRejectFormula.bits⟩ := by
    simpa only [n, localCfg] using
      SourceCSPRejectWriter.run_exact (before outputSlot)
  have hhalt : (((advance SourceCSPRejectWriter.program)^[n])
      localCfg).l = none := by rw [hr]
  obtain ⟨t, ht, hrun⟩ := outputs embedding before id id id
    (fun _ => rfl) none SourceCSPRejectWriter.program program
    (fun _ => rfl) localCfg n hhalt
  have hstart : cfg embedding before id id none localCfg =
      (⟨some .clear, none, before⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          SourceCSPRejectWriter.Label (Option Bool)) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k
    rfl
  rw [hstart, hr] at hrun
  let S : Stack → List Bool := bank embedding before
    (SourceCSPRejectWriter.contents SourceCSPRejectFormula.bits)
  refine ⟨t, S, by omega, ?_, ?_, ?_⟩
  · simpa only [program, S, cfg, stackCfg, BitMachineInline.cfg,
      id_eq, Option.map_none] using hrun
  · change bank embedding before _ (embedding 0) = _
    rw [bank_at]
    rfl
  · intro k hk
    apply bank_outside
    rintro ⟨i, hi⟩
    fin_cases i
    exact hk hi.symm

end EthInapproximability.CurrentPaper.SourceCSPRejectWriterFrame
