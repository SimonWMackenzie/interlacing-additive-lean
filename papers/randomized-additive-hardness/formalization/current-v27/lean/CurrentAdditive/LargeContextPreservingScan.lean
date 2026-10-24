import CurrentAdditive.CylinderContextScanRun

/-!
A charged lookup subroutine for a contextual list loop.  The inherited
Fin-12 indexed selector is placed inside Fin-32 with its copy scratch moved
from bank 9 to bank 14.  Thus bank 9 can retain an output accumulator, while
banks 12 and 13 retain caller context and loop fuel, and banks 15 through 31
remain available for the callback. The source list stays on bank 8 and the unary
index stays on bank 10. This file proves one lookup, not
the repeated callback/serializer loop.
-/

namespace CurrentAdditive.LargeContextPreservingScan

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderContextScanStep
open Turing BitMachineEncoding

abbrev Stack := Fin 32
abbrev Label := CylinderContextScanStep.Label ⊕ Unit
abbrev Control := CylinderContextScanStep.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def locate : CylinderContextScanStep.Stack ↪ Stack where
  toFun j := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 14, 10, 11] j
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt locate Sum.inl id id
      (some (.inr ())) (CylinderContextScanStep.program l)
  | .inr () => .halt

def run (t : Nat) (c : Config) := ((advance program)^[t]) c

noncomputable def frame (foreign : Stack → List Bool)
    (c : CylinderContextScanStep.Config) : Config :=
  BitMachineStackEmbedding.cfg locate foreign Sum.inl id
    (some (.inr ())) c

theorem frame_bank (foreign : Stack → List Bool)
    (c : CylinderContextScanStep.Config)
    (j : CylinderContextScanStep.Stack) :
    (frame foreign c).stk (locate j) = c.stk j := by
  exact BitMachineStackEmbedding.bank_at _ _ _ _

theorem frame_foreign (foreign : Stack → List Bool)
    (c : CylinderContextScanStep.Config) (j : Stack)
    (h : ¬ ∃ k, locate k = j) :
    (frame foreign c).stk j = foreign j := by
  exact BitMachineStackEmbedding.bank_outside _ _ _ _ h

theorem output_preserved (foreign : Stack → List Bool)
    (c : CylinderContextScanStep.Config) :
    (frame foreign c).stk 9 = foreign 9 := by
  apply frame_foreign
  rintro ⟨k, hk⟩
  fin_cases k <;> cases hk

theorem context_preserved (foreign : Stack → List Bool)
    (c : CylinderContextScanStep.Config) :
    (frame foreign c).stk 12 = foreign 12 ∧
    (frame foreign c).stk 13 = foreign 13 := by
  constructor <;> apply frame_foreign <;>
    rintro ⟨k, hk⟩ <;> fin_cases k <;> cases hk

theorem finite_program : Finite Stack ∧ Finite Label ∧ Finite Control :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem run_succ {c c' : Config} (h : advance program c = c') (n : Nat) :
    run (n + 1) c = run n c' := by
  exact (Function.iterate_succ_apply _ _ _).trans (congrArg (run n) h)

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (m : Nat) :
    run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

theorem embedded_lookup (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (foreign : Stack → List Bool) :
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    ∃ t ≤ 2 * pre.length + 5 +
        (2 * source.length + 5 +
          (4 * (pre ++ word :: suffix).length.bits.length + 6 +
            IndexedFieldProgram.fieldCost (pre ++ [word]))),
      run t (frame foreign
        (CylinderContextScanStep.initial source pre.length)) =
        frame foreign
          ⟨none,
           CylinderContextScanStep.getterControl
             (PreservingV2Program.v2Control
               (IndexedV2Program.indexControl
                 (SourceListMachineFields.coreControl (some true, false), none))),
           CylinderContextScanStep.selectedBank source
             (SourceListEncoding.fields suffix) word pre.length⟩ := by
  dsimp only
  obtain ⟨t, ht, hr⟩ := CylinderContextScanStep.scan_step pre word suffix
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    locate foreign Sum.inl id id (by intro v; rfl)
    (some (.inr ())) CylinderContextScanStep.program program
    (by intro l; rfl)
    (CylinderContextScanStep.initial
      (SourceListEncoding.encode (pre ++ word :: suffix)) pre.length)
    t (by change (CylinderContextScanStep.run t _).l = none; rw [hr])
  change run u (frame foreign _) = frame foreign
    (CylinderContextScanStep.run t _) at he
  rw [hr] at he
  exact ⟨u, by omega, he⟩

theorem selected_word (source suffix word : List Bool) (index : Nat)
    (foreign : Stack → List Bool) :
    (frame foreign
      ⟨none,
       CylinderContextScanStep.getterControl
         (PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
       CylinderContextScanStep.selectedBank source suffix word index⟩).stk 6 =
      word := by
  simpa [CylinderContextScanStep.selectedBank] using
    frame_bank foreign
      (⟨none,
       CylinderContextScanStep.getterControl
         (PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
       CylinderContextScanStep.selectedBank source suffix word index⟩ :
        CylinderContextScanStep.Config) 6

theorem selected_source (source suffix word : List Bool) (index : Nat)
    (foreign : Stack → List Bool) :
    (frame foreign
      ⟨none,
       CylinderContextScanStep.getterControl
         (PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
       CylinderContextScanStep.selectedBank source suffix word index⟩).stk 8 =
      source := by
  simpa [CylinderContextScanStep.selectedBank] using
    frame_bank foreign
      (⟨none,
       CylinderContextScanStep.getterControl
         (PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
       CylinderContextScanStep.selectedBank source suffix word index⟩ :
        CylinderContextScanStep.Config) 8

theorem terminal_step (source suffix word : List Bool) (index : Nat)
    (foreign : Stack → List Bool) :
    advance program
      (frame foreign
        ⟨none,
         CylinderContextScanStep.getterControl
           (PreservingV2Program.v2Control
             (IndexedV2Program.indexControl
               (SourceListMachineFields.coreControl (some true, false), none))),
         CylinderContextScanStep.selectedBank source suffix word index⟩) =
      ⟨none,
       CylinderContextScanStep.getterControl
         (PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
       (frame foreign
         ⟨none,
          CylinderContextScanStep.getterControl
            (PreservingV2Program.v2Control
              (IndexedV2Program.indexControl
                (SourceListMachineFields.coreControl (some true, false), none))),
          CylinderContextScanStep.selectedBank source suffix word index⟩).stk⟩ := by
  rfl

theorem lookup_halt (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (foreign : Stack → List Bool) :
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    ∃ t ≤ 2 * pre.length + 5 +
        (2 * source.length + 5 +
          (4 * (pre ++ word :: suffix).length.bits.length + 6 +
            IndexedFieldProgram.fieldCost (pre ++ [word]))) + 1,
      run t (frame foreign
        (CylinderContextScanStep.initial source pre.length)) =
        ⟨none,
         CylinderContextScanStep.getterControl
           (PreservingV2Program.v2Control
             (IndexedV2Program.indexControl
               (SourceListMachineFields.coreControl (some true, false), none))),
         (frame foreign
           ⟨none,
            CylinderContextScanStep.getterControl
              (PreservingV2Program.v2Control
                (IndexedV2Program.indexControl
                  (SourceListMachineFields.coreControl (some true, false), none))),
            CylinderContextScanStep.selectedBank source
              (SourceListEncoding.fields suffix) word pre.length⟩).stk⟩ := by
  dsimp only
  obtain ⟨t, ht, hr⟩ := embedded_lookup pre word suffix foreign
  refine ⟨t + 1, by omega, ?_⟩
  exact (run_add hr 1).trans
    (run_succ (terminal_step _ _ _ _ foreign) 0)

#print axioms lookup_halt

#print axioms embedded_lookup
#print axioms selected_word
#print axioms selected_source

end CurrentAdditive.LargeContextPreservingScan
