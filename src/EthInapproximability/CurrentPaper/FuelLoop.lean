import EthInapproximability.CurrentPaper.BitMachineInline
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Lane owner:b-weighted-level-9, unit 2, segment 3: an explicit fixed-program iteration.

The admitted `BitMachineIteration.iteration_run` iterates a `BitMachine.Machine` (one input word
to one output word, `OutputsWithin`); the level round is a multi-stack `TM2` program on the round
bank `H4` with an EXACT named bank, so that lemma's shape does not fit without an encode/decode
wrapper around every round. This module gives instead a generic fuel loop on an arbitrary stack
type `K` (a syntactic program built with the admitted `BitMachineInline.stmt`): label `test` pops
one bit of the fuel cell `f`; on a bit it resets the body control and jumps to the body's start;
on an empty fuel cell it halts; the body's halt jumps back to `test`.

`loop_run`: if for every `j < m` the body runs from the popped bank of state `S j` to `S (j+1)`
within `T` steps (ending in its start control), `S j f` is nonempty for `j < m` and `S m f = []`,
then ONE run of the loop from `S 0` halts on `S m` within `m * (T + 1) + 1` steps. -/

namespace EthInapproximability.CurrentPaper.FuelLoop

open Turing BitMachineEncoding

variable {K LB VB : Type*} [DecidableEq K]

abbrev Label (LB : Type*) := Unit ⊕ LB
abbrev Control (VB : Type*) := Option Bool × VB

/-- The fixed loop program. -/
def program (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (b₀ : LB) (w₀ : VB) (f : K) :
    Label LB → TM2.Stmt (fun _ : K => Bool) (Label LB) (Control VB)
  | .inl _ => .pop f (fun v o => (o, v.2))
      (.branch (fun v => v.1.isSome)
        (.load (fun _ => (none, w₀)) (.goto (fun _ => .inr b₀)))
        .halt)
  | .inr l => BitMachineInline.stmt Sum.inr (fun w => (none, w)) Prod.snd (some (.inl ())) (B l)

theorem test_nonempty (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (b₀ : LB) (w₀ w : VB) (f : K)
    (S : K → List Bool) (b : Bool) (r : List Bool) (h : S f = b :: r) :
    advance (program B b₀ w₀ f)
        (⟨some (.inl ()), (none, w), S⟩ : TM2.Cfg (fun _ : K => Bool) (Label LB) (Control VB)) =
      ⟨some (.inr b₀), (none, w₀), Function.update S f r⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, h]

theorem test_empty (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (b₀ : LB) (w₀ w : VB) (f : K)
    (S : K → List Bool) (h : S f = []) :
    advance (program B b₀ w₀ f)
        (⟨some (.inl ()), (none, w), S⟩ : TM2.Cfg (fun _ : K => Bool) (Label LB) (Control VB)) =
      ⟨none, (none, w), S⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, h]

theorem loop_run (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (b₀ : LB) (w₀ : VB) (f : K)
    (T : ℕ) : ∀ (m : ℕ) (S : ℕ → K → List Bool),
    (∀ j < m, S j f ≠ []) → S m f = [] →
    (∀ j < m, ∃ t ≤ T, ((advance B)^[t])
        (⟨some b₀, w₀, Function.update (S j) f (S j f).tail⟩ : TM2.Cfg (fun _ : K => Bool) LB VB) =
        ⟨none, w₀, S (j + 1)⟩) →
    ∃ t ≤ m * (T + 1) + 1, ((advance (program B b₀ w₀ f))^[t])
        (⟨some (.inl ()), (none, w₀), S 0⟩ : TM2.Cfg (fun _ : K => Bool) (Label LB) (Control VB)) =
      ⟨none, (none, w₀), S m⟩ := by
  intro m
  induction m with
  | zero =>
    intro S _ hend _
    exact ⟨1, by omega, test_empty B b₀ w₀ w₀ f (S 0) hend⟩
  | succ m ih =>
    intro S hne hend hbody
    obtain ⟨t0, ht0, h0⟩ := hbody 0 (by omega)
    obtain ⟨u, hu, hrest⟩ := ih (fun j => S (j + 1)) (fun j hj => hne (j + 1) (by omega)) hend
      (fun j hj => hbody (j + 1) (by omega))
    -- the first test
    obtain ⟨b, r, hbr⟩ : ∃ b r, S 0 f = b :: r := by
      cases h : S 0 f with
      | nil => exact absurd h (hne 0 (by omega))
      | cons b r => exact ⟨b, r, rfl⟩
    have s1 := test_nonempty B b₀ w₀ w₀ f (S 0) b r hbr
    -- the body, inlined, returns to the test
    have hhalt : (((advance B)^[t0])
        (⟨some b₀, w₀, Function.update (S 0) f (S 0 f).tail⟩ : TM2.Cfg (fun _ : K => Bool) LB VB)).l =
        none := by rw [h0]
    obtain ⟨n, hn, hrun⟩ := BitMachineInline.outputs Sum.inr (fun w => (none, w)) Prod.snd
      (fun _ => rfl) (some (.inl ())) B (program B b₀ w₀ f) (fun _ => rfl)
      (⟨some b₀, w₀, Function.update (S 0) f (S 0 f).tail⟩ : TM2.Cfg (fun _ : K => Bool) LB VB) t0 hhalt
    rw [h0] at hrun
    simp only [BitMachineInline.cfg] at hrun
    rw [hbr, List.tail_cons] at hrun
    refine ⟨u + n + 1, ?_, ?_⟩
    · have e : (m + 1) * (T + 1) = m * (T + 1) + (T + 1) := by ring
      omega
    · rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one, s1, hrun]
      exact hrest

#print axioms loop_run

end EthInapproximability.CurrentPaper.FuelLoop
