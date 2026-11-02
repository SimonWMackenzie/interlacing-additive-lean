import CurrentAdditive.GaussPivotSemanticBridge
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! Lift the raw-state preparation to Fin64. High banks remain available for
physical backups before the destructive pivot search. -/

namespace CurrentAdditive.GaussPivotPrepHigh64

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Bank := Fin 64

def low : Fin 32 ↪ Bank where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun x : Bank => x.val) h

private theorem stmt_id {K L V : Type*} [DecidableEq K]
    (q : TM2.Stmt (fun _ : K => Bool) L V) :
    BitMachineInline.stmt id id id none q = q := by
  induction q <;> simp [BitMachineInline.stmt, *]

def program (l : GaussPivotPrepController32.Label) :
    TM2.Stmt (fun _ : Bank => Bool)
      GaussPivotPrepController32.Label
      GaussPivotPrepController32.Control :=
  BitMachineStackEmbedding.stackStmt low
    (GaussPivotPrepController32.program l)

def blank : Bank → List Bool := fun _ => []

noncomputable def start {m k : Nat}
    (s : GaussControlTrace.State m k) :
    TM2.Cfg (fun _ : Bank => Bool)
      GaussPivotPrepController32.Label
      GaussPivotPrepController32.Control :=
  BitMachineStackEmbedding.stackCfg low blank
    (GaussPivotPrepController32.initial
      (GaussControlTrace.statePacket s))

noncomputable def prepared {m k : Nat}
    (s : GaussControlTrace.State m k) : Bank → List Bool :=
  BitMachineStackEmbedding.bank low blank
    (GaussPivotPrepBank.prepared s)

theorem prepared_low {m k : Nat}
    (s : GaussControlTrace.State m k) (i : Fin 32) :
    prepared s (low i) = GaussPivotPrepBank.prepared s i := by
  exact BitMachineStackEmbedding.bank_at low blank _ i

theorem prepared_high {m k : Nat}
    (s : GaussControlTrace.State m k) (j : Bank)
    (hj : 32 ≤ j.val) : prepared s j = [] := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨i,hi⟩
  have hv : i.val = j.val := by
    simpa [low] using congrArg (fun x : Bank => x.val) hi
  omega

theorem prepared_row {m k : Nat}
    (s : GaussControlTrace.State m k) :
    prepared s 30 = List.replicate s.r true := by
  simpa only [low] using
    (prepared_low s (30 : Fin 32)).trans
      (GaussPivotPrepBank.prepared_row s)

theorem prepared_column {m k : Nat}
    (s : GaussControlTrace.State m k) :
    prepared s 12 = List.replicate s.c true := by
  simpa only [low] using
    (prepared_low s (12 : Fin 32)).trans
      (GaussPivotPrepBank.prepared_column s)

theorem prepared_original {m k : Nat}
    (s : GaussControlTrace.State m k) :
    prepared s 31 = GaussControlTrace.statePacket s := by
  simpa only [low, GaussPivotPrepBank.packet] using
    (prepared_low s (31 : Fin 32)).trans
      (GaussPivotPrepBank.prepared_original s)

theorem prepared_count {m k : Nat}
    (s : GaussControlTrace.State m k) :
    prepared s 13 = List.replicate m true := by
  simpa only [low] using
    (prepared_low s (13 : Fin 32)).trans
      (GaussPivotPrepBank.prepared_count s)

theorem physical_prep {m k : Nat}
    (s : GaussControlTrace.State m k) :
    ∃ t ≤ GaussPivotPrepRun.clock s + 1,
      ((advance program)^[t]) (start s) =
        ⟨none, .fields ((),none), prepared s⟩ := by
  obtain ⟨a, ha, hp⟩ := GaussPivotPrepRun.outputs s
  have hp' : GaussPivotPrepController32.run (a+1)
      (GaussPivotPrepController32.initial
        (GaussControlTrace.statePacket s)) =
      ⟨none, .fields ((),none), GaussPivotPrepBank.prepared s⟩ := by
    have hbase : GaussPivotPrepController32.run (a+1)
        (GaussPivotPrepController32.initial
          (GaussPivotPrepBank.packet s)) =
        ⟨none, .fields ((),none), GaussPivotPrepBank.prepared s⟩ := by
      rw [GaussPivotPrepController32.run_add hp 1]
      rfl
    simpa only [GaussPivotPrepBank.packet] using hbase
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs
    low blank id id id (by intro v; rfl) none
    GaussPivotPrepController32.program program
    (by intro l; simp [program, BitMachineStackEmbedding.stmt, stmt_id])
    (GaussPivotPrepController32.initial
      (GaussControlTrace.statePacket s)) (a+1)
    (by change (GaussPivotPrepController32.run (a+1)
      (GaussPivotPrepController32.initial
        (GaussControlTrace.statePacket s))).l = none
        rw [hp'])
  refine ⟨t, by omega, ?_⟩
  rw [show ((advance GaussPivotPrepController32.program)^[a+1])
    (GaussPivotPrepController32.initial
      (GaussControlTrace.statePacket s)) =
    ⟨none, .fields ((),none), GaussPivotPrepBank.prepared s⟩
      from hp'] at he
  simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    start, prepared] using he

#print axioms physical_prep

end
end CurrentAdditive.GaussPivotPrepHigh64
