import Paper2.SSSched

/-! Lane owner:a-sched-space-1, WP-SCHED segment (2): the k-free polynomial clock of `SSSched.sched`, and the
standalone WP-SCHED statement (T44 clause 4 / U10 clause 3, lock v12 P:64-65, "The schedule and its checks have
polynomial bit complexity in the source encoding"): ONE fixed machine `SSSched.sched Δ γ` per `(Δ, γ)`, clock
`2^E·(|encode g|+1)^E` with `E = 45·cF Δ γ` (independent of `k`; there is no `k`). Pure arithmetic on top of the
admitted `FrontClock13.gBd_le`. -/

namespace SSSchedClock

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2
open Paper2.A3Assembly
open Paper2.FrontClock13
open Paper2.CountFront (J2 LK QK jc lc qc gB gfront gStart gfrontCtl G0 LFacts QFacts g_run)
open SSSched

/-- **The k-free clock.** -/
theorem sched_clock (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) :
    FullFront.gBd γ.num.toNat γ.den Δ g + (g.vertices + g.edges.length + 2) + 1 ≤
      ((EncodedGraph.encode g).length + 2) ^ (cF Δ γ * 45) := by
  have hlow := EncodedGraph.encode_length_lower g
  have hcge : 200 + γ.num.toNat + γ.den + Δ + UnaryBinaryEncoding.coefficient ≤ cF Δ γ := le_rfl
  generalize cF Δ γ = c at *
  generalize γ.num.toNat = a at *
  generalize γ.den = b at *
  obtain ⟨N, hNdef⟩ : ∃ N, N = (EncodedGraph.encode g).length + 2 := ⟨_, rfl⟩
  rw [← hNdef]
  have hN2 : 2 ≤ N := by omega
  obtain ⟨V0, hV0def⟩ : ∃ V0, V0 = N ^ c := ⟨_, rfl⟩
  have hV01 : 1 ≤ V0 := by rw [hV0def]; exact Nat.one_le_pow _ _ (by omega)
  have hNc : ∀ j, j ≤ c → N ^ j ≤ V0 := fun j hj => by rw [hV0def]; exact Nat.pow_le_pow_right (by omega) hj
  have hNV : N ≤ V0 := by have := hNc 1 (by omega); simpa using this
  have hN2V : N ^ 2 ≤ V0 := hNc 2 (by omega)
  have k32 : 2 ^ 32 ≤ V0 := by
    rw [hV0def]; exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_le_pow_left hN2 c)
  have kc : UnaryBinaryEncoding.coefficient + 6 ≤ V0 := by rw [hV0def]; exact const_le hN2 (by omega)
  have ka : a ≤ V0 := by rw [hV0def]; exact const_le hN2 (by omega)
  have kbΔ : 2 * b * Δ ≤ V0 := by
    have h1 : b < 2 ^ b := Nat.lt_two_pow_self
    have h2 : Δ < 2 ^ Δ := Nat.lt_two_pow_self
    have h3 : 2 * b * Δ ≤ 2 * 2 ^ b * 2 ^ Δ := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1.le) h2.le
    have h4 : 2 * 2 ^ b * 2 ^ Δ = 2 ^ (1 + b + Δ) := by rw [pow_add, pow_add]; ring
    have h5 : 2 ^ (1 + b + Δ) ≤ N ^ c :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_le_pow_left hN2 c)
    rw [hV0def]; omega
  have kb : 6144 * b ≤ V0 := by
    have h1 : b < 2 ^ b := Nat.lt_two_pow_self
    have h3 : 6144 * b ≤ 2 ^ 13 * 2 ^ b := Nat.mul_le_mul (by norm_num) h1.le
    have h4 : 2 ^ 13 * 2 ^ b = 2 ^ (13 + b) := by rw [pow_add]
    have h5 : 2 ^ (13 + b) ≤ N ^ c :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_le_pow_left hN2 c)
    rw [hV0def]; omega
  have kn : g.vertices + 3 ≤ V0 := by omega
  have km : g.edges.length ≤ V0 := by omega
  have kenc : (EncodedGraph.encode g).length + 1 ≤ V0 := by omega
  have k2L : 2 ^ Nat.clog 2 g.vertices ≤ V0 := by
    have h := Clock.two_pow_clog_le g.vertices
    have h1 : (g.vertices + 2) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have k2e : 2 ^ Nat.clog 2 (Nat.clog 2 g.vertices + 1) ≤ V0 := by
    have h := Clock.two_pow_clog_le (Nat.clog 2 g.vertices + 1)
    have hl := clog_le' g.vertices
    have h1 : (Nat.clog 2 g.vertices + 1 + 2) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have kee : 2 ^ (Nat.clog 2 (Nat.clog 2 g.vertices + 1) * Nat.clog 2 (Nat.clog 2 g.vertices + 1)) ≤ V0 ^ 2 := by
    have h := clog_sq_le (Nat.clog 2 g.vertices)
    have h1 : 2 ^ (Nat.clog 2 (Nat.clog 2 g.vertices + 1) * Nat.clog 2 (Nat.clog 2 g.vertices + 1)) ≤
        2 ^ (Nat.clog 2 g.vertices + 9) := Nat.pow_le_pow_right (by norm_num) h
    have h2 : 2 ^ (Nat.clog 2 g.vertices + 9) = 2 ^ Nat.clog 2 g.vertices * 2 ^ 9 := pow_add _ _ _
    have hL2 : 2 ^ Nat.clog 2 g.vertices ≤ N ^ 2 := by
      have h := Clock.two_pow_clog_le g.vertices
      have h1 : (g.vertices + 2) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have h3 : 2 ^ 9 ≤ N ^ 9 := Nat.pow_le_pow_left hN2 9
    have h4 : N ^ 2 * N ^ 9 = N ^ 11 := by rw [← pow_add]
    have h5 := Nat.mul_le_mul hL2 h3
    have h6 := hNc 11 (by omega)
    have h7 : V0 ≤ V0 ^ 2 := by
      have := Nat.pow_le_pow_right hV01 (show 1 ≤ 2 by omega); simpa using this
    omega
  have hgb := gBd_le a b Δ g V0 k32 kc ka kbΔ kb kn km k2L k2e kee kenc
  have e45 : V0 ^ 45 = N ^ (c * 45) := by rw [hV0def, ← pow_mul]
  have h45 : V0 ^ 44 + V0 ≤ V0 ^ 45 := by
    have h1 : V0 ≤ V0 ^ 44 := by
      have := Nat.pow_le_pow_right hV01 (show 1 ≤ 44 by omega); simpa using this
    have h2 : V0 ^ 45 = V0 ^ 44 * V0 := pow_succ V0 44
    have h3 : V0 ^ 44 * 2 ≤ V0 ^ 44 * V0 := Nat.mul_le_mul_left _ (by omega)
    omega
  rw [← e45]
  omega

theorem pow_two_mul (x E : ℕ) : (x + 2) ^ E ≤ 2 ^ E * (x + 1) ^ E := by
  rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) E

/-- **WP-SCHED standalone statement.** ONE fixed machine `SSSched.sched Δ γ` per `(Δ, γ)`: from the literal graph
bytes alone it halts within `2^E·(|encode g|+1)^E` steps, `E = 45·cF Δ γ` independent of any repetition count, in
exactly the stated bank holding the encoded schedule values and the Checks bit. -/
theorem schedule_machine (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ) :
    ∃ T ≤ 2 ^ (FrontClock13.cF Δ γ * 45) * ((EncodedGraph.encode g).length + 1) ^ (FrontClock13.cF Δ γ * 45),
      ∃ u, ∃ bit : Bool, ∃ FL : LK → List Bool, ∃ FQ : QK → List Bool,
        ((advance (sched Δ γ))^[T])
            (⟨some (schedStart Δ γ), schedCtl Δ γ, Sum.elim (G0 g) (fun _ => [])⟩ :
              TM2.Cfg (fun _ : KS => Bool) _ _) =
          ⟨none, u, Function.update (Function.update
            (Sum.elim (gExit g hg FL FQ) (fun _ => [bit])) sA []) sB []⟩ ∧
        LFacts g.vertices FL ∧
        QFacts γ.num.toNat γ.den Δ g.vertices g.edges.length (Nat.clog 2 g.vertices)
          (2 ^ (16 + (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1))))
          (2 ^ ((Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)) * (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)))) FQ ∧
        FL LProducer.pC = LProducer.u (LookupSeed.width (Nat.clog 2 g.vertices)) ∧
        FL LProducer.sC = LProducer.u (SourceProfileParameters.width (Nat.clog 2 g.vertices)) ∧
        FL LProducer.q1C = LProducer.u (SourceProfileParameters.width (Nat.clog 2 g.vertices) - 2) ∧
        FL LProducer.q2C = LProducer.u (SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices)) ∧
        FL LProducer.wC = LProducer.u (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices)) ∧
        FQ (.inl 2) = QProducer.u (Nat.clog 2 g.vertices) ∧
        FQ (.inl 24) = QProducer.u
          (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) ∧
        (bit = true ↔ CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) Δ γ) := by
  obtain ⟨T, hT, rest⟩ := sched_run Δ γ hγ hΔ g hg hn hinc hdeg
  refine ⟨T, ?_, rest⟩
  exact hT.trans ((sched_clock Δ γ g).trans (pow_two_mul _ _))

end

end SSSchedClock

#print axioms SSSchedClock.sched_clock
#print axioms SSSchedClock.schedule_machine
