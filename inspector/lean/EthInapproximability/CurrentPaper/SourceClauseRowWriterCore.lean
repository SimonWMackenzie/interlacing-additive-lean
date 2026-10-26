import EthInapproximability.CurrentPaper.SourceClauseSharedCore
import EthInapproximability.CurrentPaper.SourceClauseRowGateCleanup
import EthInapproximability.CurrentPaper.SourceClauseRowUnitFrame

/-!
# One physical row and accumulator for OR-gate and unit writers

The source row, reversed CNF payload, output suffix, and unary clause count
are shared cells. The two writers retain their separately typed arithmetic
scratch banks. This is the exact physical layout on which a tuple callback
must run before it can alternate opening/closing units with OR gates.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterCore

open scoped Classical

abbrev Core (q : ℕ) := SourceCSPRowQueryFrame.Stack q ⊕ Fin 3
abbrev Gate (q : ℕ) := SourceClauseRowIndexedGate.Stack q
abbrev UnitBank (q : ℕ) := SourceClauseRowUnitFrame.Stack q

def gateCoreCell {q : ℕ} : Core q → Gate q
  | .inl x => SourceClauseRowGateCleanup.rowCell x
  | .inr 0 => SourceClauseRowGateCleanup.savedCell
  | .inr 1 => SourceClauseRowGateCleanup.outputCell
  | .inr 2 => SourceClauseRowGateCleanup.countCell

def unitCoreCell {q : ℕ} : Core q → UnitBank q
  | .inl x => .inl x
  | .inr 0 => .inr SourceClauseRowUnitMachine.savedSlot
  | .inr 1 => .inr SourceClauseRowUnitMachine.outputSlot
  | .inr 2 => .inr SourceClauseRowUnitMachine.countSlot

def gateCore {q : ℕ} : Core q ↪ Gate q where
  toFun := gateCoreCell
  inj' := by
    intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            have hh : x = y := by
              have hu := SourceClauseRowIndexedGate.gateEmbedding.injective h
              exact Sum.inl.inj (Sum.inl.inj hu)
            simp [hh]
        | inr y =>
            fin_cases y <;>
              have hu := SourceClauseRowIndexedGate.gateEmbedding.injective h <;>
              simp [SourceClauseRowGate.gateEmbedding] at hu
    | inr x =>
        cases y with
        | inl y =>
            fin_cases x <;>
              have hu := SourceClauseRowIndexedGate.gateEmbedding.injective h <;>
              simp [SourceClauseRowGate.gateEmbedding] at hu
        | inr y => fin_cases x <;> fin_cases y <;>
            simp [gateCoreCell, SourceClauseRowGateCleanup.savedCell,
              SourceClauseRowGateCleanup.outputCell,
              SourceClauseRowGateCleanup.countCell] at h ⊢

def unitCore {q : ℕ} : Core q ↪ UnitBank q where
  toFun := unitCoreCell
  inj' := by
    intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (Sum.inl.inj h)
        | inr y => fin_cases y <;> cases h
    | inr x =>
        cases y with
        | inl y => fin_cases x <;> cases h
        | inr y => fin_cases x <;> fin_cases y <;>
            simp [unitCoreCell, SourceClauseRowUnitMachine.savedSlot,
              SourceClauseRowUnitMachine.outputSlot,
              SourceClauseRowUnitMachine.countSlot] at h ⊢

noncomputable abbrev Stack (q : ℕ) :=
  SourceClauseSharedCore.Stack (gateCore (q := q)) (unitCore (q := q))

noncomputable def gateEmbedding {q : ℕ} : Gate q ↪ Stack q :=
  SourceClauseSharedCore.left gateCore unitCore
noncomputable def unitEmbedding {q : ℕ} : UnitBank q ↪ Stack q :=
  SourceClauseSharedCore.right gateCore unitCore

theorem gate_cell {q : ℕ} (c : Core q) :
    gateEmbedding (gateCore c) = (.inl c : Stack q) :=
  SourceClauseSharedCore.left_core gateCore unitCore c

theorem unit_cell {q : ℕ} (c : Core q) :
    unitEmbedding (unitCore c) = (.inl c : Stack q) :=
  SourceClauseSharedCore.right_core gateCore unitCore c

end EthInapproximability.CurrentPaper.SourceClauseRowWriterCore
