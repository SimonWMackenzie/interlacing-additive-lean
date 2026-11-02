import Paper2.A3H3Dispatch
import Paper2.A3H3Size

/-!
# Unit 3 endpoint (H_A3 closure), segment 3: the LocalRun assembly and H_A3 under R12

Lane `owner:a-h-a3-assembly-3` (private, 26 September 2026). Pure composition.

The ONE fixed local program on the widened H_A3 bank `Fin (a + 3)` is the tree

  `progA3 = front ; dispatch(flag₁, probe ; dispatch(flag₂, success, none), unscheduled)`

built only from the production `BitMachineRawSequence.program` (charged handoff) and the two-way bit dispatch
of `A3H3Dispatch` (one charged transition). The five tables are NAMED PROGRAM PARAMETERS with their
specifications as NAMED HYPOTHESES (`DecideSpec`, `BranchSpec`):

* `front`  (lane a-success-table-11: count front and the `Checks` bit): from the widened H_A3 bank, halts with
  a bit `b₁` in the head of `flag₁`, `b₁ = true ↔ Checks (clog₂ n) Δ γ`, and a front exit predicate `Mid₁`;
* `probe`  (the generator-outcome decision; the admitted all-outcomes program): under `Mid₁ ∧ Checks`, halts with
  a bit `b₂` in the head of `flag₂`, `b₂ = true ↔ Good`, and an exit predicate `Mid₂`;
* `success` (the admitted success chain `ThrJoin.success_run_full`, lifted): under `Mid₂ ∧ Good`;
* `none`   (lane a-h-a3-assembly-2 `NoneOut.none_run_canonical`, lifted): under `Mid₂ ∧ ¬ Good`;
* `unsched` (lane a-h-a3-assembly-2 `Unsched.unscheduled_run`, lifted): under `Mid₁ ∧ ¬ Checks`, and only for
  `0 < Δ`, `0 < γ` (root decision R12; the admitted `failed_schedule_run` needs both).

Each branch specification states: halts within `C·(n+2)^(E(k+1))`, output cell `j` holds exactly
`EncodedSelectedOutput.outputBits … t`, and the final bank has encoded size within the same bound.
The composite clock is the sum of the component clocks plus the charged transitions (`seq_dispatch_spec`).
`H_A3_R12` then gives the production `Unit4Shell.Shells.H_A3 Δ γ` through the frozen owner-1 wrapper
`Wrap.H_A3_of_local` and the checked `Size.inputSize` (segment 1).
-/

namespace Paper2.A3Assembly.Run

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2

/-- The H_A3 hypotheses on one instance. -/
def Hyp (Δ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) : Prop :=
  1 ≤ k ∧ (∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v) ∧
    (∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ)

/-- A predicate on (instance, selected tape, bank). -/
abbrev Pred (Δ : ℕ) (γ : ℚ) (a : ℕ) : Type :=
  ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ),
    (TotalFiniteConstructorScratch.select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape →
      (Fin (a + 3) → List Bool) → Prop

/-- A condition on (instance, selected tape). -/
abbrev Cond (Δ : ℕ) (γ : ℚ) : Type :=
  ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ),
    (TotalFiniteConstructorScratch.select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape → Prop

/-- NAMED SPEC SHAPE (branch): from every bank satisfying `Pre`, the table `P` halts within
`C·(n+2)^(E(k+1))` with `outputBits` in cell `j` and final encoded bank size within the same bound. -/
def BranchSpec (Δ : ℕ) (γ : ℚ) (a : ℕ) {L V : Type}
    (P : L → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L V) (s : L) (v : V) (j : Fin (a + 3))
    (Pre : Pred Δ γ a) (C E : ℕ) : Prop :=
  ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ), Hyp Δ g hg k →
    ∀ (t : (TotalFiniteConstructorScratch.select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape)
      (S : Fin (a + 3) → List Bool), Pre g hg hn k t S →
      ∃ (T : ℕ) (u : V) (S' : Fin (a + 3) → List Bool),
        T ≤ C * (g.vertices + 2) ^ (E * (k + 1)) ∧
        ((advance P)^[T]) ⟨some s, v, S⟩ = ⟨none, u, S'⟩ ∧
        S' j = EncodedSelectedOutput.outputBits hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k t ∧
        (BitMachineBankCodec.encode S').length ≤ C * (g.vertices + 2) ^ (E * (k + 1))

/-- NAMED SPEC SHAPE (decision): from every bank satisfying `Pre`, the table `D` halts within
`C·(n+2)^(E(k+1))` with a bit `b` as the head of cell `flag`, `b = true ↔ Good`, and exit predicate `Mid`. -/
def DecideSpec (Δ : ℕ) (γ : ℚ) (a : ℕ) {L V : Type}
    (D : L → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L V) (s : L) (v : V) (flag : Fin (a + 3))
    (Pre Mid : Pred Δ γ a) (Good : Cond Δ γ) (C E : ℕ) : Prop :=
  ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ), Hyp Δ g hg k →
    ∀ (t : (TotalFiniteConstructorScratch.select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape)
      (S : Fin (a + 3) → List Bool), Pre g hg hn k t S →
      ∃ (T : ℕ) (u : V) (S' : Fin (a + 3) → List Bool) (b : Bool),
        T ≤ C * (g.vertices + 2) ^ (E * (k + 1)) ∧
        ((advance D)^[T]) ⟨some s, v, S⟩ = ⟨none, u, S'⟩ ∧
        (S' flag).head? = some b ∧ (b = true ↔ Good g hg hn k t) ∧ Mid g hg hn k t S'

/-- Pure clock arithmetic of one decision followed by a dispatch. -/
theorem clock_arith (N x y CD C₁ C₂ ED E₁ E₂ k : ℕ) (hN : 1 ≤ N)
    (hx : x ≤ CD * N ^ (ED * (k + 1))) (hy : y ≤ C₁ * N ^ (E₁ * (k + 1))) :
    x + (y + 1) + 1 ≤ (CD + C₁ + C₂ + 2) * N ^ (max ED (max E₁ E₂) * (k + 1)) := by
  have hP : 1 ≤ N ^ (max ED (max E₁ E₂) * (k + 1)) := Nat.one_le_pow _ _ hN
  have hD : N ^ (ED * (k + 1)) ≤ N ^ (max ED (max E₁ E₂) * (k + 1)) :=
    Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ (le_max_left _ _))
  have h1 : N ^ (E₁ * (k + 1)) ≤ N ^ (max ED (max E₁ E₂) * (k + 1)) :=
    Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _
      ((le_max_left E₁ E₂).trans (le_max_right _ _)))
  have a1 := Nat.mul_le_mul_left CD hD
  have a2 := Nat.mul_le_mul_left C₁ h1
  have a3 : C₂ * 1 ≤ C₂ * N ^ (max ED (max E₁ E₂) * (k + 1)) := Nat.mul_le_mul_left _ hP
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
  omega

theorem size_arith (N z C₁ C₂ CD E₁ E₂ ED k : ℕ) (hN : 1 ≤ N) (hz : z ≤ C₁ * N ^ (E₁ * (k + 1))) :
    z ≤ (CD + C₁ + C₂ + 2) * N ^ (max ED (max E₁ E₂) * (k + 1)) := by
  have h1 : N ^ (E₁ * (k + 1)) ≤ N ^ (max ED (max E₁ E₂) * (k + 1)) :=
    Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _
      ((le_max_left E₁ E₂).trans (le_max_right _ _)))
  have a2 := Nat.mul_le_mul_left C₁ h1
  have : C₁ ≤ CD + C₁ + C₂ + 2 := by omega
  exact hz.trans (a2.trans (Nat.mul_le_mul_right _ this))

theorem clock_arith' (N x y CD C₁ C₂ ED E₁ E₂ k : ℕ) (hN : 1 ≤ N)
    (hx : x ≤ CD * N ^ (ED * (k + 1))) (hy : y ≤ C₂ * N ^ (E₂ * (k + 1))) :
    x + (y + 1) + 1 ≤ (CD + C₁ + C₂ + 2) * N ^ (max ED (max E₁ E₂) * (k + 1)) := by
  have := clock_arith N x y CD C₂ C₁ ED E₂ E₁ k hN hx hy
  rw [max_comm E₂ E₁, show CD + C₂ + C₁ + 2 = CD + C₁ + C₂ + 2 by omega] at this
  exact this

theorem size_arith' (N z C₁ C₂ CD E₁ E₂ ED k : ℕ) (hN : 1 ≤ N) (hz : z ≤ C₂ * N ^ (E₂ * (k + 1))) :
    z ≤ (CD + C₁ + C₂ + 2) * N ^ (max ED (max E₁ E₂) * (k + 1)) := by
  have := size_arith N z C₂ C₁ CD E₂ E₁ ED k hN hz
  rw [max_comm E₂ E₁, show CD + C₂ + C₁ + 2 = CD + C₁ + C₂ + 2 by omega] at this
  exact this

/-- **Composition lemma.** A decision table followed by a dispatch to two branch tables satisfies the
branch specification from the decision's precondition, with the summed clock plus two charged steps. -/
theorem seq_dispatch_spec (Δ : ℕ) (γ : ℚ) (a : ℕ) {LD VD L₁ V₁ L₂ V₂ : Type}
    (D : LD → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LD VD) (sD : LD) (vD : VD) (flag : Fin (a + 3))
    (P₁ : L₁ → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L₁ V₁) (s₁ : L₁) (w₁ : V₁)
    (P₂ : L₂ → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L₂ V₂) (s₂ : L₂) (w₂ : V₂)
    (j : Fin (a + 3)) (Pre Mid : Pred Δ γ a) (Good : Cond Δ γ) (CD ED C₁ E₁ C₂ E₂ : ℕ)
    (hD : DecideSpec Δ γ a D sD vD flag Pre Mid Good CD ED)
    (h₁ : BranchSpec Δ γ a P₁ s₁ w₁ j (fun g hg hn k t S => Mid g hg hn k t S ∧ Good g hg hn k t) C₁ E₁)
    (h₂ : BranchSpec Δ γ a P₂ s₂ w₂ j (fun g hg hn k t S => Mid g hg hn k t S ∧ ¬ Good g hg hn k t)
      C₂ E₂) :
    BranchSpec Δ γ a (Dispatch.seqDispatch D vD flag P₁ s₁ P₂ s₂ w₁ w₂)
      (BitMachineRawSequence.leftLabel sD) (vD, ((none : Option Bool), (w₁, w₂))) j Pre
      (CD + C₁ + C₂ + 2) (max ED (max E₁ E₂)) := by
  intro g hg hn k hH t S hPre
  have hN : 1 ≤ g.vertices + 2 := by omega
  obtain ⟨TD, u, S₁, b, hTD, hrD, hflag, hb, hMid⟩ := hD g hg hn k hH t S hPre
  cases b with
  | true =>
    have hG : Good g hg hn k t := hb.mp rfl
    obtain ⟨T₁, u₁, S', hT₁, hr₁, hj, hsz⟩ := h₁ g hg hn k hH t S₁ ⟨hMid, hG⟩
    obtain ⟨t', ht', hr'⟩ := Dispatch.run_true flag P₁ s₁ P₂ s₂ w₁ w₂ S₁ S' u₁
      ((none : Option Bool), (w₁, w₂)) T₁ hflag hr₁
    obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs D (Dispatch.program flag P₁ s₁ P₂ s₂ w₁ w₂)
      sD (.inl ()) vD u ((none : Option Bool), (w₁, w₂)) (Dispatch.emb₁ w₂ u₁) S S₁ S' TD t' hrD hr'
    refine ⟨T, _, S', ?_, hr, hj, ?_⟩
    · have := clock_arith (g.vertices + 2) TD T₁ CD C₁ C₂ ED E₁ E₂ k hN hTD hT₁
      omega
    · exact size_arith (g.vertices + 2) _ C₁ C₂ CD E₁ E₂ ED k hN hsz
  | false =>
    have hG : ¬ Good g hg hn k t := fun h => absurd (hb.mpr h) (by decide)
    obtain ⟨T₂, u₂, S', hT₂, hr₂, hj, hsz⟩ := h₂ g hg hn k hH t S₁ ⟨hMid, hG⟩
    obtain ⟨t', ht', hr'⟩ := Dispatch.run_false flag P₁ s₁ P₂ s₂ w₁ w₂ S₁ S' u₂
      ((none : Option Bool), (w₁, w₂)) T₂ hflag hr₂
    obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs D (Dispatch.program flag P₁ s₁ P₂ s₂ w₁ w₂)
      sD (.inl ()) vD u ((none : Option Bool), (w₁, w₂)) (Dispatch.emb₂ w₁ u₂) S S₁ S' TD t' hrD hr'
    refine ⟨T, _, S', ?_, hr, hj, ?_⟩
    · have := clock_arith' (g.vertices + 2) TD T₂ CD C₁ C₂ ED E₁ E₂ k hN hTD hT₂
      omega
    · exact size_arith' (g.vertices + 2) _ C₁ C₂ CD E₁ E₂ ED k hN hsz

/-- The precondition "the bank is the widened literal H_A3 input bank". -/
def IsInput (Δ : ℕ) (γ : ℚ) (a : ℕ) : Pred Δ γ a :=
  fun g hg hn k t S => S = Wrap.widen a (Wrap.inputBank Δ γ g hg hn k t)

/-- A branch specification from the literal input bank is exactly `Wrap.LocalRun`. -/
theorem localRun_of_spec (Δ : ℕ) (γ : ℚ) (a : ℕ) {L V : Type} [Fintype L] [Fintype V]
    (P : L → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L V) (s : L) (v : V) (j : Fin (a + 3)) (C E : ℕ)
    (h : BranchSpec Δ γ a P s v j (IsInput Δ γ a) C E) :
    Wrap.LocalRun Δ γ a P s v j C E := by
  intro g hg hn k hk hsurj hdeg t
  obtain ⟨T, u, S', hT, hr, hj, hsz⟩ := h g hg hn k ⟨hk, hsurj, hdeg⟩ t _ rfl
  exact ⟨T, _, hT, hr, rfl, hj, hsz⟩

theorem localRun_mono (Δ : ℕ) (γ : ℚ) (a : ℕ) {L V : Type} [Fintype L] [Fintype V]
    (P : L → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L V) (s : L) (v : V) (j : Fin (a + 3))
    (C E C' E' : ℕ) (hC : C ≤ C') (hE : E ≤ E') (h : Wrap.LocalRun Δ γ a P s v j C E) :
    Wrap.LocalRun Δ γ a P s v j C' E' := by
  intro g hg hn k hk hsurj hdeg t
  obtain ⟨T, c, hT, hr, hl, hj, hsz⟩ := h g hg hn k hk hsurj hdeg t
  have hp : C * (g.vertices + 2) ^ (E * (k + 1)) ≤ C' * (g.vertices + 2) ^ (E' * (k + 1)) :=
    Nat.mul_le_mul hC (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ hE))
  exact ⟨T, c, hT.trans hp, hr, hl, hj, hsz.trans hp⟩

theorem inputSize_mono (Δ : ℕ) (γ : ℚ) (C E C' E' : ℕ) (hC : C ≤ C') (hE : E ≤ E')
    (h : Wrap.InputSize Δ γ C E) : Wrap.InputSize Δ γ C' E' := by
  intro g hg hn k hk hsurj hdeg t
  have hp : C * (g.vertices + 2) ^ (E * (k + 1)) ≤ C' * (g.vertices + 2) ^ (E' * (k + 1)) :=
    Nat.mul_le_mul hC (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ hE))
  exact (h g hg hn k hk hsurj hdeg t).trans hp

/-- The `Checks` condition of `select`, as a condition on instances. -/
def ChecksCond (Δ : ℕ) (γ : ℚ) : Cond Δ γ :=
  fun g _ _ _ _ => CompletePublicScheduleScratch.Checks
    (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) Δ γ

/-- The fixed program tree. -/
def progA3 {a : ℕ} {LF VF LP VP LS VS LN VN LU VU : Type}
    (front : LF → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LF VF) (vF : VF) (flag₁ : Fin (a + 3))
    (probe : LP → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LP VP) (sP : LP) (vP : VP) (flag₂ : Fin (a + 3))
    (succ : LS → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LS VS) (sS : LS) (vS : VS)
    (none_ : LN → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LN VN) (sN : LN) (vN : VN)
    (unsched : LU → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LU VU) (sU : LU) (vU : VU) :=
  Dispatch.seqDispatch front vF flag₁
    (Dispatch.seqDispatch probe vP flag₂ succ sS none_ sN vS vN)
    (BitMachineRawSequence.leftLabel sP) unsched sU
    (vP, ((none : Option Bool), (vS, vN))) vU

/-- **Segment 3.** `LocalRun` for the fixed tree from the five named specifications (R12 for the
unscheduled branch). -/
theorem localRun_progA3 (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) (a : ℕ)
    {LF VF LP VP LS VS LN VN LU VU : Type}
    [Fintype LF] [Fintype VF] [Fintype LP] [Fintype VP] [Fintype LS] [Fintype VS]
    [Fintype LN] [Fintype VN] [Fintype LU] [Fintype VU]
    (front : LF → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LF VF) (sF : LF) (vF : VF) (flag₁ : Fin (a + 3))
    (probe : LP → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LP VP) (sP : LP) (vP : VP) (flag₂ : Fin (a + 3))
    (succ : LS → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LS VS) (sS : LS) (vS : VS)
    (none_ : LN → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LN VN) (sN : LN) (vN : VN)
    (unsched : LU → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LU VU) (sU : LU) (vU : VU)
    (j : Fin (a + 3)) (Mid₁ Mid₂ : Pred Δ γ a) (Good : Cond Δ γ)
    (CF EF CP EP CS ES CN EN CU EU : ℕ)
    (hFront : DecideSpec Δ γ a front sF vF flag₁ (IsInput Δ γ a) Mid₁ (ChecksCond Δ γ) CF EF)
    (hProbe : DecideSpec Δ γ a probe sP vP flag₂
      (fun g hg hn k t S => Mid₁ g hg hn k t S ∧ ChecksCond Δ γ g hg hn k t) Mid₂ Good CP EP)
    (hSucc : BranchSpec Δ γ a succ sS vS j
      (fun g hg hn k t S => Mid₂ g hg hn k t S ∧ Good g hg hn k t) CS ES)
    (hNone : BranchSpec Δ γ a none_ sN vN j
      (fun g hg hn k t S => Mid₂ g hg hn k t S ∧ ¬ Good g hg hn k t) CN EN)
    (hUnsched : 0 < Δ → 0 < γ → BranchSpec Δ γ a unsched sU vU j
      (fun g hg hn k t S => Mid₁ g hg hn k t S ∧ ¬ ChecksCond Δ γ g hg hn k t) CU EU) :
    Wrap.LocalRun Δ γ a
      (progA3 front vF flag₁ probe sP vP flag₂ succ sS vS none_ sN vN unsched sU vU)
      (BitMachineRawSequence.leftLabel sF)
      (vF, ((none : Option Bool), ((vP, ((none : Option Bool), (vS, vN))), vU))) j
      (CF + (CP + CS + CN + 2) + CU + 2) (max EF (max (max EP (max ES EN)) EU)) := by
  have hS := seq_dispatch_spec Δ γ a probe sP vP flag₂ succ sS vS none_ sN vN j
    (fun g hg hn k t S => Mid₁ g hg hn k t S ∧ ChecksCond Δ γ g hg hn k t) Mid₂ Good
    CP EP CS ES CN EN hProbe hSucc hNone
  have hAll := seq_dispatch_spec Δ γ a front sF vF flag₁
    (Dispatch.seqDispatch probe vP flag₂ succ sS none_ sN vS vN)
    (BitMachineRawSequence.leftLabel sP) (vP, ((none : Option Bool), (vS, vN)))
    unsched sU vU j (IsInput Δ γ a) Mid₁ (ChecksCond Δ γ)
    CF EF (CP + CS + CN + 2) (max EP (max ES EN)) CU EU hFront hS (hUnsched hΔ hγ)
  exact localRun_of_spec Δ γ a _ _ _ j _ _ hAll

/-- **H_A3 under R12** from the five named specifications: the production `Unit4Shell.Shells.H_A3 Δ γ`,
via the frozen owner-1 wrapper `Wrap.H_A3_of_local` and the checked input-size bound `Size.inputSize`. -/
theorem H_A3_R12 (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) (a : ℕ)
    {LF VF LP VP LS VS LN VN LU VU : Type}
    [Fintype LF] [Fintype VF] [Fintype LP] [Fintype VP] [Fintype LS] [Fintype VS]
    [Fintype LN] [Fintype VN] [Fintype LU] [Fintype VU]
    (front : LF → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LF VF) (sF : LF) (vF : VF) (flag₁ : Fin (a + 3))
    (probe : LP → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LP VP) (sP : LP) (vP : VP) (flag₂ : Fin (a + 3))
    (succ : LS → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LS VS) (sS : LS) (vS : VS)
    (none_ : LN → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LN VN) (sN : LN) (vN : VN)
    (unsched : LU → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LU VU) (sU : LU) (vU : VU)
    (j : Fin (a + 3)) (Mid₁ Mid₂ : Pred Δ γ a) (Good : Cond Δ γ)
    (CF EF CP EP CS ES CN EN CU EU : ℕ)
    (hFront : DecideSpec Δ γ a front sF vF flag₁ (IsInput Δ γ a) Mid₁ (ChecksCond Δ γ) CF EF)
    (hProbe : DecideSpec Δ γ a probe sP vP flag₂
      (fun g hg hn k t S => Mid₁ g hg hn k t S ∧ ChecksCond Δ γ g hg hn k t) Mid₂ Good CP EP)
    (hSucc : BranchSpec Δ γ a succ sS vS j
      (fun g hg hn k t S => Mid₂ g hg hn k t S ∧ Good g hg hn k t) CS ES)
    (hNone : BranchSpec Δ γ a none_ sN vN j
      (fun g hg hn k t S => Mid₂ g hg hn k t S ∧ ¬ Good g hg hn k t) CN EN)
    (hUnsched : 0 < Δ → 0 < γ → BranchSpec Δ γ a unsched sU vU j
      (fun g hg hn k t S => Mid₁ g hg hn k t S ∧ ¬ ChecksCond Δ γ g hg hn k t) CU EU) :
    Unit4Shell.Shells.H_A3 Δ γ := by
  have hrun := localRun_progA3 Δ γ hΔ hγ a front sF vF flag₁ probe sP vP flag₂ succ sS vS
    none_ sN vN unsched sU vU j Mid₁ Mid₂ Good CF EF CP EP CS ES CN EN CU EU
    hFront hProbe hSucc hNone hUnsched
  have hrun' := localRun_mono Δ γ a _ _ _ j _ _
    (CF + (CP + CS + CN + 2) + CU + 2 + (4 * Δ + 9))
    (max (max EF (max (max EP (max ES EN)) EU)) 160) (by omega) (le_max_left _ _) hrun
  have hin := inputSize_mono Δ γ (4 * Δ + 9) 160
    (CF + (CP + CS + CN + 2) + CU + 2 + (4 * Δ + 9))
    (max (max EF (max (max EP (max ES EN)) EU)) 160) (by omega) (le_max_right _ _)
    (Size.inputSize Δ γ)
  exact Wrap.H_A3_of_local Δ γ a _ _ _ j _ _ hrun' hin

end Paper2.A3Assembly.Run

#print axioms Paper2.A3Assembly.Run.seq_dispatch_spec
#print axioms Paper2.A3Assembly.Run.localRun_of_spec
#print axioms Paper2.A3Assembly.Run.localRun_mono
#print axioms Paper2.A3Assembly.Run.inputSize_mono
#print axioms Paper2.A3Assembly.Run.localRun_progA3
#print axioms Paper2.A3Assembly.Run.H_A3_R12
