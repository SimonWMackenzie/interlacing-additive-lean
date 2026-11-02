import CurrentAdditive.FeaturePreparedCallback
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! A fixed 64-bank placement for the prepared feature callback.  Its 22
local banks occupy 16--37, leaving the scheduler's context banks untouched. -/

namespace CurrentAdditive.FeatureContext64

open EthInapproximability.CurrentPaper
open CurrentAdditive.FeaturePreparedCallback
open Turing BitMachineEncoding

noncomputable section

abbrev Bank := Fin (32 + 32)

private theorem frame_count :
    (SourceListMachineWriter.framingMachine true).stackCount = 8 := rfl

def locateMap : FeaturePreparedCallback.Stack → Bank
  | .inl (.inl i) => ⟨16 + i.val, by omega⟩
  | .inl (.inr i) => ⟨18 + i.val, by omega⟩
  | .inr (.inl i) => ⟨21 + i.val, by omega⟩
  | .inr (.inr (.inl i)) => ⟨24 + i.val, by
      have h : i.val < 8 := by simpa only [frame_count] using i.isLt
      omega⟩
  | .inr (.inr (.inr (.inl i))) => ⟨32 + i.val, by omega⟩
  | .inr (.inr (.inr (.inr i))) => ⟨37 + i.val, by omega⟩

theorem locateMap_injective : Function.Injective locateMap := by decide

def locate : FeaturePreparedCallback.Stack ↪ Bank :=
  ⟨locateMap, locateMap_injective⟩

theorem locate_range (k : FeaturePreparedCallback.Stack) :
    16 ≤ (locate k).val ∧ (locate k).val ≤ 37 := by
  fin_cases k <;> decide

def program (l : FeaturePreparedCallback.Label) :
    TM2.Stmt (fun _ : Bank => Bool) FeaturePreparedCallback.Label
      FeaturePreparedCallback.Control :=
  BitMachineStackEmbedding.stackStmt locate (FeaturePreparedCallback.program l)

def frame (foreign : Bank → List Bool)
    (c : FeaturePreparedCallback.Config) :
    TM2.Cfg (fun _ : Bank => Bool) FeaturePreparedCallback.Label
      FeaturePreparedCallback.Control :=
  BitMachineStackEmbedding.stackCfg locate foreign c

def run (t : Nat)
    (c : TM2.Cfg (fun _ : Bank => Bool) FeaturePreparedCallback.Label
      FeaturePreparedCallback.Control) := ((advance program)^[t]) c

theorem advance_frame (foreign : Bank → List Bool)
    (c : FeaturePreparedCallback.Config) :
    advance program (frame foreign c) =
      frame foreign (advance FeaturePreparedCallback.program c) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => rfl
  | some l =>
      change TM2.stepAux (program l) v
          (BitMachineStackEmbedding.bank locate foreign S) =
        BitMachineStackEmbedding.stackCfg locate foreign
          (TM2.stepAux (FeaturePreparedCallback.program l) v S)
      exact BitMachineStackEmbedding.stack_stepAux locate foreign
        (FeaturePreparedCallback.program l) v S

theorem run_frame (foreign : Bank → List Bool)
    (c : FeaturePreparedCallback.Config) (t : Nat) :
    run t (frame foreign c) =
      frame foreign (FeaturePreparedCallback.run t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      calc
        run (t+1) (frame foreign c) =
            advance program (run t (frame foreign c)) := by
              simp only [run, Function.iterate_succ_apply']
        _ = advance program
            (frame foreign (FeaturePreparedCallback.run t c)) := by rw [ih]
        _ = frame foreign
            (advance FeaturePreparedCallback.program
              (FeaturePreparedCallback.run t c)) := advance_frame foreign _
        _ = frame foreign (FeaturePreparedCallback.run (t+1) c) := by
              simp only [FeaturePreparedCallback.run,
                Function.iterate_succ_apply']

def Ready (S : Bank → List Bool) (j y : Nat)
    (c : List (Nat × Nat)) : Prop :=
  ∀ k, S (locate k) = FeaturePreparedCallback.initialBank j y c k

theorem prepared_run (S : Bank → List Bool) (j y : Nat)
    (c : List (Nat × Nat)) (hready : Ready S j y c) :
    ∃ t ≤ FeaturePreparedCallback.preparedClock j y c,
      let z := run t
        (⟨some (.pair (.emit 0)), (.inl none, none), S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _)
      z.l = none ∧ z.stk (locate FeaturePreparedCallback.joinOutput) =
        CylinderFeatureCodec.encodeFeature ((j,y)::c) := by
  obtain ⟨t, ht, hhalt, hout⟩ :=
    FeaturePreparedCallback.pair_prepend_prepared_run j y c
  have hinit :
      (⟨some (.pair (.emit 0)), (.inl none, none), S⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) =
      frame S (FeaturePreparedCallback.initialCfg j y c) := by
    have hbank := BitMachineStackEmbedding.bank_eq_self locate S
      (FeaturePreparedCallback.initialBank j y c)
      (fun k => (hready k).symm)
    simp only [frame, BitMachineStackEmbedding.stackCfg,
      FeaturePreparedCallback.initialCfg, hbank]
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hinit, run_frame]
    simpa only [frame, BitMachineStackEmbedding.stackCfg] using hhalt
  · rw [hinit, run_frame]
    simpa only [frame, BitMachineStackEmbedding.stackCfg,
      BitMachineStackEmbedding.bank_at] using hout

theorem prepared_clock_poly (j y : Nat) (c : List (Nat × Nat)) :
    FeaturePreparedCallback.preparedClock j y c ≤
      (10 * (UnaryBinaryEncoding.coefficient + 100)) *
        (FeaturePreparedCallback.preparedSize j y c)^2 :=
  FeaturePreparedCallback.prepared_clock_poly j y c

#print axioms prepared_run
#print axioms prepared_clock_poly

end
end CurrentAdditive.FeatureContext64
