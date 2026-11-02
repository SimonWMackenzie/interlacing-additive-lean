import CurrentAdditive.QuarticProbeOutcome
import CurrentAdditive.QuarticInputSize
import Paper2.A3H3Run

/-! Generic, fixed-program dispatch interfaces retargeted to the literal v27 selected tape and encoded output. These do not assert the existence of branch specifications. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticDispatchSpec

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2 Paper2.A3Assembly

/-- The H_A3 hypotheses on one instance. -/
def Hyp (Δ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) : Prop :=
  1 ≤ k ∧ (∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v) ∧
    (∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ)

/-- A predicate on (instance, selected tape, bank). -/
abbrev Pred (Δ : ℕ) (γ : ℚ) (a : ℕ) : Type :=
  ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ),
    (QuarticConstructor.select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape →
      (Fin (a + 3) → List Bool) → Prop

/-- A condition on (instance, selected tape). -/
abbrev Cond (Δ : ℕ) (γ : ℚ) : Type :=
  ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ),
    (QuarticConstructor.select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape → Prop

/-- NAMED SPEC SHAPE (branch): from every bank satisfying `Pre`, the table `P` halts within
`C·(n+2)^(E(k+1))` with `outputBits` in cell `j` and final encoded bank size within the same bound. -/
def BranchSpec (Δ : ℕ) (γ : ℚ) (a : ℕ) {L V : Type}
    (P : L → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L V) (s : L) (v : V) (j : Fin (a + 3))
    (Pre : Pred Δ γ a) (C E : ℕ) : Prop :=
  ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ), Hyp Δ g hg k →
    ∀ (t : (QuarticConstructor.select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape)
      (S : Fin (a + 3) → List Bool), Pre g hg hn k t S →
      ∃ (T : ℕ) (u : V) (S' : Fin (a + 3) → List Bool),
        T ≤ C * (g.vertices + 2) ^ (E * (k + 1)) ∧
        ((advance P)^[T]) ⟨some s, v, S⟩ = ⟨none, u, S'⟩ ∧
        S' j = QuarticConstructor.outputBits27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k t ∧
        (BitMachineBankCodec.encode S').length ≤ C * (g.vertices + 2) ^ (E * (k + 1))

/-- NAMED SPEC SHAPE (decision): from every bank satisfying `Pre`, the table `D` halts within
`C·(n+2)^(E(k+1))` with a bit `b` as the head of cell `flag`, `b = true ↔ Good`, and exit predicate `Mid`. -/
def DecideSpec (Δ : ℕ) (γ : ℚ) (a : ℕ) {L V : Type}
    (D : L → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L V) (s : L) (v : V) (flag : Fin (a + 3))
    (Pre Mid : Pred Δ γ a) (Good : Cond Δ γ) (C E : ℕ) : Prop :=
  ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ), Hyp Δ g hg k →
    ∀ (t : (QuarticConstructor.select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape)
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


/-- The exact v27 three-cell input packet. -/
def inputBank27 (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0 < g.vertices) (k : ℕ)
    (t : (QuarticConstructor.select27 hn
      (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) : Fin 3 → List Bool :=
  ![EncodedGraph.encode g, List.replicate k true,
    (QuarticConstructor.select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t]

/-- The initial bank for the v27 selected output. -/
def IsInput27 (Δ : ℕ) (γ : ℚ) (a : ℕ) : Pred Δ γ a :=
  fun g hg hn k t S => S = Wrap.widen a (inputBank27 Δ γ g hg hn k t)

/-- The desired fixed-machine endpoint for the v27 selected constructor. -/
def LocalRun27 (Δ : ℕ) (γ : ℚ) (a : ℕ)
    {L V : Type} (P : L → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L V)
    (start : L) (initial : V) (j : Fin (a + 3)) (C E : ℕ) : Prop :=
  ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ),
    Hyp Δ g hg k →
    ∀ t : (QuarticConstructor.select27 hn
      (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape,
      ∃ (T : ℕ) (c : TM2.Cfg (fun _ : Fin (a + 3) => Bool) L V),
        T ≤ C * (g.vertices + 2) ^ (E * (k + 1)) ∧
        ((advance P)^[T])
          ⟨some start, initial, Wrap.widen a (inputBank27 Δ γ g hg hn k t)⟩ = c ∧
        c.l = none ∧
        c.stk j = QuarticConstructor.outputBits27 hn
          (CanonicalEdgeTape.graphEdge g hg) Δ γ k t ∧
        (BitMachineBankCodec.encode c.stk).length ≤
          C * (g.vertices + 2) ^ (E * (k + 1))

theorem localRun27_of_spec (Δ : ℕ) (γ : ℚ) (a : ℕ)
    {L V : Type} (P : L → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L V)
    (s : L) (v : V) (j : Fin (a + 3)) (C E : ℕ)
    (h : BranchSpec Δ γ a P s v j (IsInput27 Δ γ a) C E) :
    LocalRun27 Δ γ a P s v j C E := by
  intro g hg hn k hH t
  obtain ⟨T, u, S', hT, hr, hj, hsz⟩ :=
    h g hg hn k hH t _ rfl
  exact ⟨T, _, hT, hr, rfl, hj, hsz⟩

/-- Polynomial input packet length required by `LocalRun27`. -/
def InputSize27 (Δ : ℕ) (γ : ℚ) (C E : ℕ) : Prop :=
  ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ),
    Hyp Δ g hg k →
    ∀ t : (QuarticConstructor.select27 hn
      (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape,
      (BitMachineBankCodec.encode (inputBank27 Δ γ g hg hn k t)).length ≤
        C * (g.vertices + 2) ^ (E * (k + 1))

/-- The literal source checks, before using the eventual source threshold. -/
def ChecksCond27 (Δ : ℕ) (γ : ℚ) : Cond Δ γ :=
  fun g _ _ _ _ => CurrentAdditive.QuarticSchedule.Checks27
    (V := Fin g.vertices) (Edges := Fin g.edges.length)
    (Nat.clog 2 g.vertices) Δ γ

#print axioms seq_dispatch_spec
#print axioms localRun27_of_spec

end Paper2.CurrentAdditive.QuarticDispatchSpec
