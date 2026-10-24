import CurrentAdditive.GaussPivotPrepHigh64
import CurrentAdditive.GaussPivotGuardRun
import CurrentAdditive.GaussPivotPrepClock
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! The literal preparation and preserving row guard, joined on one bank.
No row/height word is supplied initially: both come from the raw Gauss packet.
The original packet remains in bank31 even when m=0. -/

namespace CurrentAdditive.GaussPreparedGuard64

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1500000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Bank := Fin 64
abbrev PrepControl := GaussPivotPrepController32.Control
abbrev GuardControl := GaussPivotGuard32.Control
abbrev Control := PrepControl × GuardControl
abbrev Label := BitMachineRawSequence.Label
  GaussPivotPrepController32.Label GaussPivotGuard32.Label

def prepInit : PrepControl := .copy ((),none)
def guardInit : GuardControl := .copy ((),none)

def guardProgram (l : GaussPivotGuard32.Label) :=
  BitMachineStackEmbedding.stackStmt GaussPivotPrepHigh64.low
    (GaussPivotGuard32.program l)

def program := BitMachineRawSequence.program
  GaussPivotPrepHigh64.program guardProgram (.rowCopy .scan)
  prepInit guardInit

abbrev Config := TM2.Cfg (fun _ : Bank => Bool) Label Control

def initial {m k : Nat} (s : GaussControlTrace.State m k) : Config :=
  ⟨some (BitMachineRawSequence.leftLabel (.copy .scan)),
    (prepInit,guardInit),(GaussPivotPrepHigh64.start s).stk⟩

def clock {m k : Nat} (s : GaussControlTrace.State m k) : Nat :=
  GaussPivotPrepRun.clock s + 1 + GaussPivotGuardRun.clock s.r m + 1 + 1

private theorem inline_id {K L V : Type*} [DecidableEq K]
    (q : TM2.Stmt (fun _ : K => Bool) L V) :
    BitMachineInline.stmt id id id none q = q := by
  induction q <;> simp [BitMachineInline.stmt, *]

theorem guard_preserves_prepared {m k : Nat}
    (s : GaussControlTrace.State m k) :
    ∃ t ≤ GaussPivotGuardRun.clock s.r m + 1,
      ((advance guardProgram)^[t])
        (⟨some (.rowCopy .scan),guardInit,GaussPivotPrepHigh64.prepared s⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none,.choose (some (decide (s.r < m))),
          GaussPivotPrepHigh64.prepared s⟩ := by
  let S := GaussPivotPrepBank.prepared s
  have hr : S 30 = List.replicate s.r true := GaussPivotPrepBank.prepared_row s
  have hm : S 13 = List.replicate m true := GaussPivotPrepBank.prepared_count s
  obtain ⟨t,ht,he⟩ := GaussPivotGuardRun.outputs S s.r m hr hm
    (GaussPivotPrepBank.prepared_other s 20 (by decide))
    (GaussPivotPrepBank.prepared_other s 21 (by decide))
    (GaussPivotPrepBank.prepared_other s 22 (by decide))
    (GaussPivotPrepBank.prepared_other s 29 (by decide))
  have hhalt : GaussPivotGuard32.run (t+1) (GaussPivotGuard32.initial S) =
      ⟨none,.choose (some (decide (s.r < m))),S⟩ := by
    rw [GaussPivotGuard32.run_add he 1]
    by_cases h : s.r < m <;> simp [GaussPivotGuard32.run,
      GaussPivotGuard32.program, advance, TM2.step, TM2.stepAux, h]
  obtain ⟨u,hu,he'⟩ := BitMachineStackEmbedding.outputs
    GaussPivotPrepHigh64.low (GaussPivotPrepHigh64.prepared s)
    id id id (by intro v; rfl) none
    GaussPivotGuard32.program guardProgram
    (by intro l; simp [guardProgram,BitMachineStackEmbedding.stmt,inline_id])
    (GaussPivotGuard32.initial S) (t+1)
    (by change (GaussPivotGuard32.run (t+1) _).l = none; rw [hhalt])
  have hbank : BitMachineStackEmbedding.bank GaussPivotPrepHigh64.low
      (GaussPivotPrepHigh64.prepared s) S = GaussPivotPrepHigh64.prepared s := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro j
    exact (GaussPivotPrepHigh64.prepared_low s j).symm
  change ((advance guardProgram)^[u])
      (BitMachineStackEmbedding.cfg GaussPivotPrepHigh64.low
        (GaussPivotPrepHigh64.prepared s) id id none (GaussPivotGuard32.initial S)) =
      BitMachineStackEmbedding.cfg GaussPivotPrepHigh64.low
        (GaussPivotPrepHigh64.prepared s) id id none
        (GaussPivotGuard32.run (t+1) (GaussPivotGuard32.initial S)) at he'
  rw [hhalt] at he'
  refine ⟨u, by omega, ?_⟩
  simpa only [BitMachineStackEmbedding.cfg,BitMachineInline.cfg,
    BitMachineStackEmbedding.stackCfg,GaussPivotGuard32.initial,
    hbank,guardInit] using he'

/-- The fixed guard actually selects r<m and restores every prepared bank.
This theorem includes m=0, every k, and arbitrary Gauss states. -/
theorem physical_prepared_guard {m k : Nat}
    (s : GaussControlTrace.State m k) :
    ∃ t ≤ clock s,
      ((advance program)^[t]) (initial s) =
        ⟨none,(prepInit,.choose (some (decide (s.r < m)))),
          GaussPivotPrepHigh64.prepared s⟩ := by
  obtain ⟨a,ha,hprep⟩ := GaussPivotPrepHigh64.physical_prep s
  obtain ⟨b,hb,hguard⟩ := guard_preserves_prepared s
  obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs
    GaussPivotPrepHigh64.program guardProgram
    (.copy .scan) (.rowCopy .scan)
    prepInit (.fields ((),none)) guardInit (.choose (some (decide (s.r < m))))
    (GaussPivotPrepHigh64.start s).stk (GaussPivotPrepHigh64.prepared s)
    (GaussPivotPrepHigh64.prepared s) a b
    (by simpa [GaussPivotPrepHigh64.start,prepInit] using hprep) hguard
  refine ⟨t, by dsimp [clock]; omega, ?_⟩
  simpa only [program,initial] using he

#print axioms guard_preserves_prepared
#print axioms physical_prepared_guard

end
end CurrentAdditive.GaussPreparedGuard64
