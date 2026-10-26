import CurrentAdditive.GaussGetterIntegratedClock

/-!
The checked 22-bank getter embedded in 64 banks away from a list scheduler's
live banks. Matrix bank 8 is shared and preserved. Getter row/column input
banks move to 41/42; the selected cell lands on banks 38/49. The scheduler
and backup banks outside 32..52 are foreign and remain untouched.
-/

namespace CurrentAdditive.GaussGetterSafe64

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 64
abbrev Label := CurrentAdditive.GaussGetterIntegrated.Label
abbrev Control := CurrentAdditive.GaussGetterIntegrated.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def slot : Fin 22 ↪ Stack where
  toFun j := ![32, 33, 34, 35, 36, 37, 38, 39, 8, 40, 41, 42,
    43, 44, 45, 46, 47, 48, 49, 50, 51, 52] j
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def program (l : Label) : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineStackEmbedding.stmt slot id id id none
    (CurrentAdditive.GaussGetterIntegrated.program l)

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

noncomputable def frame (foreign : Stack → List Bool)
    (c : CurrentAdditive.GaussGetterIntegrated.Config) : Config :=
  BitMachineStackEmbedding.cfg slot foreign id id none c

theorem lifted_run (foreign : Stack → List Bool)
    (c : CurrentAdditive.GaussGetterIntegrated.Config) (t : Nat)
    (hhalt : (CurrentAdditive.GaussGetterIntegrated.run t c).l = none) :
    ∃ u ≤ t, run u (frame foreign c) =
      frame foreign (CurrentAdditive.GaussGetterIntegrated.run t c) := by
  simpa only [run, CurrentAdditive.GaussGetterIntegrated.run, frame] using
    BitMachineStackEmbedding.outputs slot foreign id id id
      (by intro v; rfl) none
      CurrentAdditive.GaussGetterIntegrated.program program
      (by intro l; rfl) c t hhalt

theorem frame_inner (foreign : Stack → List Bool)
    (c : CurrentAdditive.GaussGetterIntegrated.Config) (j : Fin 22) :
    (frame foreign c).stk (slot j) = c.stk j := by
  exact BitMachineStackEmbedding.bank_at slot foreign c.stk j

theorem frame_eq_of_ready (S : Stack → List Bool)
    (c : CurrentAdditive.GaussGetterIntegrated.Config)
    (hready : ∀ j : Fin 22, c.stk j = S (slot j)) :
    frame S c = ⟨c.l, c.var, S⟩ := by
  have hb := BitMachineStackEmbedding.bank_eq_self
    slot S c.stk hready
  cases c with
  | mk l v T =>
      cases l <;>
        simp [frame, BitMachineStackEmbedding.cfg,
          BitMachineStackEmbedding.stackCfg,
          BitMachineInline.cfg, hb]

theorem slot_range (i : Fin 22) :
    slot i = 8 ∨ (32 ≤ (slot i).val ∧ (slot i).val < 53) := by
  fin_cases i <;> decide

theorem frame_foreign (foreign : Stack → List Bool)
    (c : CurrentAdditive.GaussGetterIntegrated.Config)
    (j : Stack) (hj : (j.val < 32 ∧ j ≠ 8) ∨ 53 ≤ j.val) :
    (frame foreign c).stk j = foreign j := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  rcases slot_range i with hi8 | hiwide
  · have hj8 : j = 8 := hi.symm.trans hi8
    rcases hj with ⟨_, hn⟩ | hlarge
    · exact hn hj8
    · have hjv := congrArg Fin.val hj8
      omega
  · rcases hj with ⟨hsmall, _⟩ | hlarge <;> omega

theorem canonical_getter_with_context
    (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) (foreign : Stack → List Bool) :
    let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
    let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
    let init := CurrentAdditive.GaussGetterIntegrated.firstFrame
      (CurrentAdditive.GaussNestedGetter.firstFrame
        (CurrentAdditive.GaussNestedGetter.inputForeign cellPre.length)
        (CurrentAdditive.CylinderContextScanStep.initial
          matrix rowPre.length))
    ∃ t ≤ 140 * (matrix.length + 1)^3,
      (run t (frame foreign init)).l = none ∧
      (run t (frame foreign init)).stk 38 = cell ∧
      (run t (frame foreign init)).stk 49 = cell ∧
      (run t (frame foreign init)).stk 8 = matrix ∧
      (∀ j : Stack, (j.val < 32 ∧ j ≠ 8) ∨ 53 ≤ j.val →
        (run t (frame foreign init)).stk j = foreign j) := by
  dsimp only
  obtain ⟨t, ht, hh, h6, h18, h8⟩ :=
    CurrentAdditive.GaussGetterIntegratedClock.canonical_getter_cubic
      rowPre rowSuffix cellPre cellSuffix cell
  obtain ⟨u, hu, hr⟩ := lifted_run foreign _ t hh
  refine ⟨u, hu.trans ht, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]
    simpa [frame, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hh]
  · rw [hr]
    change (frame foreign _).stk (slot (6 : Fin 22)) = cell
    rw [frame_inner]
    exact h6
  · rw [hr]
    change (frame foreign _).stk (slot (18 : Fin 22)) = cell
    rw [frame_inner]
    exact h18
  · rw [hr]
    change (frame foreign _).stk (slot (8 : Fin 22)) = _
    rw [frame_inner]
    exact h8
  · intro j hj
    rw [hr]
    exact frame_foreign foreign _ j hj

theorem canonical_getter_from_ready
    (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) (S : Stack → List Bool) :
    let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
    let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
    let init := CurrentAdditive.GaussGetterIntegrated.firstFrame
      (CurrentAdditive.GaussNestedGetter.firstFrame
        (CurrentAdditive.GaussNestedGetter.inputForeign cellPre.length)
        (CurrentAdditive.CylinderContextScanStep.initial
          matrix rowPre.length))
    (∀ j : Fin 22, init.stk j = S (slot j)) →
    ∃ t ≤ 140 * (matrix.length + 1)^3,
      (run t ⟨init.l, init.var, S⟩).l = none ∧
      (run t ⟨init.l, init.var, S⟩).stk 38 = cell ∧
      (run t ⟨init.l, init.var, S⟩).stk 49 = cell ∧
      (run t ⟨init.l, init.var, S⟩).stk 8 = matrix ∧
      (∀ j : Stack, (j.val < 32 ∧ j ≠ 8) ∨ 53 ≤ j.val →
        (run t ⟨init.l, init.var, S⟩).stk j = S j) := by
  dsimp only
  intro hready
  obtain ⟨t, ht, hh, h38, h49, h8, hp⟩ :=
    canonical_getter_with_context rowPre rowSuffix cellPre
      cellSuffix cell S
  have heq := frame_eq_of_ready S
    (CurrentAdditive.GaussGetterIntegrated.firstFrame
      (CurrentAdditive.GaussNestedGetter.firstFrame
        (CurrentAdditive.GaussNestedGetter.inputForeign cellPre.length)
        (CurrentAdditive.CylinderContextScanStep.initial
          (SourceListEncoding.encode
            (rowPre ++ SourceListEncoding.encode
              (cellPre ++ cell :: cellSuffix) :: rowSuffix))
          rowPre.length))) hready
  rw [heq] at hh h38 h49 h8 hp
  exact ⟨t, ht, hh, h38, h49, h8, hp⟩

#print axioms canonical_getter_with_context
#print axioms canonical_getter_from_ready

end CurrentAdditive.GaussGetterSafe64
