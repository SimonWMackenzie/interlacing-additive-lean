import CurrentAdditive.GaussGetterChain
import CurrentAdditive.GaussNestedGetterClock

set_option maxHeartbeats 1000000

/-! One fixed finite program combines the checked nested selector and
cell transfer. -/

namespace CurrentAdditive.GaussGetterIntegrated

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext
open Turing Turing.TM2.Stmt BitMachineEncoding

theorem nested_final_halt (foreign : Fin 22 → List Bool)
    (c : PreservingV2Program.Config) (hc : c.l = none) :
    GaussNestedGetter.run 2 (GaussNestedGetter.secondFrame foreign c) =
      ⟨none,
       (GaussNestedGetter.secondFrame foreign c).var,
       (GaussNestedGetter.secondFrame foreign c).stk⟩ := by
  cases c with
  | mk l v S =>
      cases l with
      | none =>
          rfl
      | some l =>
          cases hc

abbrev Stack := Fin 22

inductive Admin where
  | afterNested | done
  deriving DecidableEq, Fintype

abbrev Label := GaussNestedGetter.Label ⊕
  (GaussCellTransfer.Label ⊕ Admin)
abbrev Control := GaussNestedGetter.Control × GaussCellTransfer.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def baseControl : GaussNestedGetter.Control :=
  GaussNestedGetter.firstControl
    (CylinderContextScanStep.copyControl ((), none))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineInline.stmt Sum.inl
      (fun v => (v, ((), none))) Prod.fst
      (some (.inr (.inr .afterNested))) (GaussNestedGetter.program l)
  | .inr (.inl l) => BitMachineInline.stmt
      (fun l => .inr (.inl l))
      (fun v => (baseControl, v)) Prod.snd
      (some (.inr (.inr .done))) (GaussCellTransfer.program l)
  | .inr (.inr .afterNested) =>
      load (fun _ => (baseControl, ((), none)))
        (goto (fun _ => .inr (.inl .clear6)))
  | .inr (.inr .done) => halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c c' : Config} {n : Nat}
    (h : run n c = c') (m : Nat) : run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

noncomputable def firstFrame (c : GaussNestedGetter.Config) : Config :=
  BitMachineInline.cfg Sum.inl (fun v => (v, ((), none)))
    (some (.inr (.inr .afterNested))) c

noncomputable def transferFrame (c : GaussCellTransfer.Config) : Config :=
  BitMachineInline.cfg (fun l => .inr (.inl l))
    (fun v => (baseControl, v)) (some (.inr (.inr .done))) c

theorem afterNested_step (v : Control) (S : Stack → List Bool) :
    advance program ⟨some (.inr (.inr .afterNested)), v, S⟩ =
      transferFrame ⟨some .clear6, ((), none), S⟩ := by
  rfl

theorem transfer_final_halt (S : Stack → List Bool) :
    GaussCellTransfer.run 1 ⟨some .done, ((), none), S⟩ =
      ⟨none, ((), none), S⟩ := by
  rfl

theorem first_run (c : GaussNestedGetter.Config) (t : Nat)
    (hhalt : (GaussNestedGetter.run t c).l = none) :
    ∃ u ≤ t, run u (firstFrame c) =
      firstFrame (GaussNestedGetter.run t c) := by
  obtain ⟨u, hu, he⟩ := BitMachineInline.outputs
    Sum.inl (fun v => (v, ((), none))) Prod.fst
    (by intro v; rfl) (some (.inr (.inr .afterNested)))
    GaussNestedGetter.program program (by intro l; rfl)
    c t hhalt
  exact ⟨u, hu, he⟩

theorem transfer_run (c : GaussCellTransfer.Config) (t : Nat)
    (hhalt : (GaussCellTransfer.run t c).l = none) :
    ∃ u ≤ t, run u (transferFrame c) =
      transferFrame (GaussCellTransfer.run t c) := by
  obtain ⟨u, hu, he⟩ := BitMachineInline.outputs
    (fun l => .inr (.inl l)) (fun v => (baseControl, v)) Prod.snd
    (by intro v; rfl) (some (.inr (.inr .done)))
    GaussCellTransfer.program program (by intro l; rfl)
    c t hhalt
  exact ⟨u, hu, he⟩

theorem compose_halted (c : GaussNestedGetter.Config)
    (tCore : Nat) (hCore : (GaussNestedGetter.run tCore c).l = none)
    (tTransfer : Nat) (S' : Stack → List Bool)
    (hTransfer : GaussCellTransfer.run tTransfer
      ⟨some .clear6, ((), none), (GaussNestedGetter.run tCore c).stk⟩ =
        ⟨some .done, ((), none), S'⟩) :
    ∃ t ≤ tCore + 1 + (tTransfer + 1) + 1,
      run t (firstFrame c) =
        ⟨none, (baseControl, ((), none)), S'⟩ := by
  let coreFinal := GaussNestedGetter.run tCore c
  let transferInitial : GaussCellTransfer.Config :=
    ⟨some .clear6, ((), none), coreFinal.stk⟩
  obtain ⟨u, hu, hFirst⟩ := first_run c tCore hCore
  have hBridge : run (u + 1) (firstFrame c) =
      transferFrame transferInitial := by
    rw [run_add hFirst]
    simpa [run, firstFrame, BitMachineInline.cfg,
      coreFinal, transferInitial, hCore] using
      (afterNested_step (coreFinal.var, ((), none)) coreFinal.stk)
  have hTransferHalt :
      GaussCellTransfer.run (tTransfer + 1) transferInitial =
        ⟨none, ((), none), S'⟩ := by
    rw [GaussCellTransfer.run_add hTransfer]
    exact transfer_final_halt S'
  obtain ⟨v, hv, hSecond⟩ := transfer_run transferInitial
    (tTransfer + 1) (by rw [hTransferHalt])
  have hJoined : run (u + 1 + v) (firstFrame c) =
      transferFrame ⟨none, ((), none), S'⟩ := by
    exact (run_add hBridge v).trans (hSecond.trans
      (by rw [hTransferHalt]))
  refine ⟨u + 1 + v + 1, by omega, ?_⟩
  rw [run_add hJoined]
  rfl

theorem after_second_halt (v : GaussNestedGetter.Control)
    (S : Stack → List Bool) :
    GaussNestedGetter.run 2
      ⟨some (.inr (.inr .afterSecond)), v, S⟩ =
      ⟨none, v, S⟩ := by
  rfl

theorem cfg_eq_of_label (c : GaussNestedGetter.Config)
    (l : Option GaussNestedGetter.Label) (h : c.l = l) :
    c = ⟨l, c.var, c.stk⟩ := by
  cases c with
  | mk label v S =>
      cases h
      rfl

theorem canonical_getter_bank6
    (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) :
    let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
    let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
    let initial := firstFrame
      (GaussNestedGetter.firstFrame
        (GaussNestedGetter.inputForeign cellPre.length)
        (CylinderContextScanStep.initial matrix rowPre.length))
    ∃ t ≤ GaussNestedGetterClock.clock
        rowPre rowSuffix cellPre cellSuffix cell + 2 + 1 +
        (row.length + 1 + (2 * cell.length + 3) + 1) + 1,
      (run t initial).l = none ∧
      (run t initial).stk 6 = cell ∧
      (run t initial).stk 18 = cell ∧
      (run t initial).stk 8 = matrix := by
  dsimp only
  let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
  let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
  let c : GaussNestedGetter.Config :=
    GaussNestedGetter.firstFrame
      (GaussNestedGetter.inputForeign cellPre.length)
      (CylinderContextScanStep.initial matrix rowPre.length)
  obtain ⟨tSelect, hSelectBound, hLabel, tTransfer,
    hTransferBound, S', hTransfer, hout, hrestore, hmatrix⟩ :=
      GaussGetterChain.selected_transfer
        rowPre rowSuffix cellPre cellSuffix cell
  let selected := GaussNestedGetter.run tSelect c
  have hLabel' : selected.l = some (.inr (.inr .afterSecond)) := hLabel
  have hSelectedShape : selected =
      ⟨some (.inr (.inr .afterSecond)), selected.var, selected.stk⟩ :=
    cfg_eq_of_label selected _ hLabel'
  have hTwo : GaussNestedGetter.run 2 selected =
      ⟨none, selected.var, selected.stk⟩ := by
    rw [hSelectedShape]
    exact after_second_halt selected.var selected.stk
  have hCoreRun : GaussNestedGetter.run (tSelect + 2) c =
      ⟨none, selected.var, selected.stk⟩ := by
    exact (GaussNestedGetter.run_add (by rfl :
      GaussNestedGetter.run tSelect c = selected) 2).trans hTwo
  have hCoreHalt :
      (GaussNestedGetter.run (tSelect + 2) c).l = none := by
    rw [hCoreRun]
  have hTransfer' : GaussCellTransfer.run tTransfer
      ⟨some .clear6, ((), none),
        (GaussNestedGetter.run (tSelect + 2) c).stk⟩ =
      ⟨some .done, ((), none), S'⟩ := by
    rw [hCoreRun]
    exact hTransfer
  obtain ⟨t, ht, hr⟩ := compose_halted c (tSelect + 2)
    hCoreHalt tTransfer S' hTransfer'
  refine ⟨t, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [GaussNestedGetterClock.clock]
    omega
  · rw [hr]
  · rw [hr]
    exact hout
  · rw [hr]
    exact hrestore
  · rw [hr]
    exact hmatrix

#print axioms nested_final_halt
#print axioms first_run
#print axioms transfer_run
#print axioms compose_halted
#print axioms canonical_getter_bank6

end CurrentAdditive.GaussGetterIntegrated
