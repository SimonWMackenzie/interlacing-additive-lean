import Paper2.MedPhases

/-!
# WP-U18a (ii), machine half, part 2: the bundled phase algebra and the clean call

Lane `owner:a-median-1` (private, 27 September 2026). Paper A, lock v12, I:117-125.

`Phase K`: a literal TM2 program on the bank `K` with a fixed start label and start control.
`Phase.Runs A S T b`: from bank `S` the program halts within `b` transitions with bank EXACTLY `T`.
`seq` is the production `BitMachineRawSequence.program` (one charged handoff), `loop` the admitted
`Paper2.CountedLoop.loop` (unary counter, charged test per round), `call M ι` the production
`BitMachineIteration.program M` embedded at stacks `ι` (production `BitMachineStackRun.run`): with
fuel `[true]` it runs `M` once from a clean bank `M.init x` to the clean bank `M.init y`
(output moved to `M.input`, every other stack of `M` cleared, all charged).
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Paper2.MedianOwner.Phases

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.BitMachineEncoding

structure Phase (K : Type) [DecidableEq K] where
  L : Type
  V : Type
  fL : Fintype L
  fV : Fintype V
  P : L → Stmt K L V
  l0 : L
  v0 : V

namespace Phase

variable {K : Type} [DecidableEq K]

/-- Exact bounded run of a phase: from bank `S`, halt within `bound` transitions with bank `T`. -/
def Runs (A : Phase K) (S T : K → List Bool) (bound : ℕ) : Prop :=
  ∃ t ≤ bound, ∃ v₁ : A.V,
    ((advance A.P)^[t]) (⟨some A.l0, A.v0, S⟩ : Cfg K A.L A.V) = ⟨none, v₁, T⟩

theorem Runs.mono {A : Phase K} {S T : K → List Bool} {b b' : ℕ} (h : A.Runs S T b)
    (hb : b ≤ b') : A.Runs S T b' := by
  obtain ⟨t, ht, v, hv⟩ := h
  exact ⟨t, ht.trans hb, v, hv⟩

theorem Runs.congr {A : Phase K} {S T T' : K → List Bool} {b : ℕ} (h : A.Runs S T b)
    (hT : T = T') : A.Runs S T' b := hT ▸ h

/-- A phase from a single literal program. -/
def ofProg {L V : Type} [Fintype L] [Fintype V] (P : L → Stmt K L V) (l0 : L) (v0 : V) :
    Phase K := ⟨L, V, inferInstance, inferInstance, P, l0, v0⟩

theorem ofProg_runs {L V : Type} [Fintype L] [Fintype V] (P : L → Stmt K L V) (l0 : L) (v0 : V)
    {S T : K → List Bool} (t : ℕ) (v₁ : V)
    (h : ((advance P)^[t]) (⟨some l0, v0, S⟩ : Cfg K L V) = ⟨none, v₁, T⟩) :
    (ofProg P l0 v0).Runs S T t := ⟨t, le_rfl, v₁, h⟩

/-- Sequential composition (production `BitMachineRawSequence.program`). -/
def seq (A B : Phase K) : Phase K where
  L := A.L ⊕ (Unit ⊕ B.L)
  V := A.V × B.V
  fL := by haveI := A.fL; haveI := B.fL; infer_instance
  fV := by haveI := A.fV; haveI := B.fV; infer_instance
  P := BitMachineRawSequence.program A.P B.P B.l0 A.v0 B.v0
  l0 := .inl A.l0
  v0 := (A.v0, B.v0)

theorem seq_runs {A B : Phase K} {S T U : K → List Bool} {ba bb : ℕ}
    (ha : A.Runs S T ba) (hb : B.Runs T U bb) : (A.seq B).Runs S U (ba + bb + 1) := by
  obtain ⟨ta, hta, v₁, hA⟩ := ha
  obtain ⟨tb, htb, w₁, hB⟩ := hb
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs A.P B.P A.l0 B.l0 A.v0 v₁ B.v0 w₁ S T U ta tb
    hA hB
  exact ⟨t, by omega, (A.v0, w₁), h⟩

/-- Counted loop (admitted `Paper2.CountedLoop.loop`, unary counter on stack `ctr`). -/
def loop (A : Phase K) (ctr : K) : Phase K where
  L := Unit ⊕ A.L
  V := Option Bool × A.V
  fL := by haveI := A.fL; infer_instance
  fV := by haveI := A.fV; infer_instance
  P := Paper2.CountedLoop.loop ctr A.P A.l0 A.v0
  l0 := .inl ()
  v0 := (none, A.v0)

theorem loop_runs (A : Phase K) (ctr : K) (j Bd : ℕ) (S : ℕ → K → List Bool)
    (hctr : ∀ i ≤ j, S i ctr = List.replicate (j - i) true)
    (hbody : ∀ i < j, A.Runs (Function.update (S i) ctr (List.replicate (j - i - 1) true))
      (S (i + 1)) Bd) :
    (A.loop ctr).Runs (S 0) (S j) (j * (Bd + 2) + 1) := by
  obtain ⟨t, ht, c', h⟩ := Paper2.CountedLoop.loop_run ctr A.P A.l0 A.v0 j Bd S hctr
    (fun i hi => by
      obtain ⟨t, ht, v, h⟩ := hbody i hi
      exact ⟨t, ht, v, h⟩) (none, A.v0)
  exact ⟨t, ht, c', h⟩

/-- The clean bank of machine `M`: `M.init x` on its own stacks, fuel `f`, empty save stack. -/
def eb (M : Machine) (x f : List Bool) : Fin M.stackCount ⊕ Fin 2 → List Bool :=
  Sum.elim (M.init x).stk (BitMachineIteration.foreign f [])

/-- One clean call of an arbitrary machine `M` at the stacks `ι` (production iteration program). -/
def call (M : Machine) (ι : (Fin M.stackCount ⊕ Fin 2) ↪ K) : Phase K where
  L := BitMachineIteration.Label M
  V := BitMachineIteration.Control M
  fL := inferInstance
  fV := inferInstance
  P := fun l => BitMachineStackEmbedding.stackStmt ι (BitMachineIteration.program M l)
  l0 := .inr .testFuel
  v0 := (M.initial, none)

/-- **Clean call.** If `M` outputs `y` on `x` within `T`, the embedded call runs from the clean
bank `M.init x` with fuel `[true]` to the clean bank `M.init y` with empty fuel, every foreign stack
unchanged, within `roundBound M L T + 1` transitions (`|x| ≤ L`). -/
theorem call_runs (M : Machine) (ι : (Fin M.stackCount ⊕ Fin 2) ↪ K) (G : K → List Bool)
    {x y : List Bool} {T L : ℕ} (hM : M.OutputsWithin x y T) (hx : x.length ≤ L) :
    (call M ι).Runs (BitMachineStackEmbedding.bank ι G (eb M x [true]))
      (BitMachineStackEmbedding.bank ι G (eb M y [])) (BitMachineIteration.roundBound M L T + 1) := by
  obtain ⟨t, ht, hr⟩ := BitMachineIteration.iteration_run M (fun j => if j = 0 then x else y)
    [true] L T (by
      intro j hj
      simp only [List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff] at hj
      subst hj
      simpa using hM) (by
      intro j hj
      simp only [List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff] at hj
      subst hj
      simpa using hx)
  simp only [List.length_cons, List.length_nil, zero_add, one_mul, ↓reduceIte,
    one_ne_zero] at ht hr
  refine ⟨t, ht, (M.initial, none), ?_⟩
  have h := BitMachineStackRun.run ι G (BitMachineIteration.program M)
    (BitMachineIteration.ready M x [true]) t
  have h2 : ((advance (BitMachineIteration.program M))^[t]) (BitMachineIteration.ready M x [true])
      = BitMachineIteration.finished M y := hr
  rw [h2] at h
  exact h

end Phase

end Paper2.MedianOwner.Phases
