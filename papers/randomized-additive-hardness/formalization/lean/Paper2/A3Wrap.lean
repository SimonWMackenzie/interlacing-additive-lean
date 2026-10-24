import Paper2.A4Shells
import EthInapproximability.CurrentPaper.U4PostFrame
import EthInapproximability.CurrentPaper.BitMachineBankWrapper
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# Unit 3 endpoint assembly, segment 4 (generic part): the BitMachine wrapper on the H_A3 bank

Lane `owner:a-h-a3-assembly-1` (private, 26 September 2026). Production imports only.

One fixed machine
`MA = composition (Unit4Post.Pre.machine a) (composition (BitMachineBankWrapper.machine P start initial)
  (BankFieldProjection.machine j))`
(all three admitted Paper B machines; the width-changing `Pre` is the admitted `U4PostFrame` one):
`Pre a` prepends `a` empty fields to the three-field H_A3 packet, the admitted bank wrapper parses the
`(a+3)`-field packet, runs the fixed local program `P` on the widened bank and serializes the final bank,
and the admitted field projection prints the raw word of cell `j`. Every charge is the admitted one.

The ONLY premises are the local run of `P` on the widened H_A3 bank (`LocalRun`: it halts within
`C·(n+2)^(E(k+1))` with `outputBits` in cell `j` and final bank of encoded size within the same bound)
and the H_A3 input-size bound (`InputSize`). Everything else is admitted.
-/

namespace Paper2.A3Assembly.Wrap

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

/-- The H_A3 three-field bank preceded by `a` blank cells. -/
def widen (a : ℕ) (X : Fin 3 → List Bool) : Fin (a + 3) → List Bool :=
  fun i => if h : a ≤ i.val then X ⟨i.val - a, by omega⟩ else []

theorem encode_widen (a : ℕ) (X : Fin 3 → List Bool) :
    BitMachineBankCodec.encode (widen a X) =
      List.replicate a false ++ BitMachineBankCodec.encode X := by
  rw [Unit4Post.encode_split a 3 (widen a X)]
  have h1 : (fun i : Fin a => widen a X (i.castLE (Nat.le_add_right a 3))) =
      fun _ => ([] : List Bool) := by
    funext i
    have hi : ¬ a ≤ (i.castLE (Nat.le_add_right a 3)).val := by
      simp only [Fin.val_castLE]; omega
    simp only [widen, hi, dite_false]
  have h2 : (fun j : Fin 3 => widen a X (j.natAdd a)) = X := by
    funext j
    have hj : a ≤ (j.natAdd a).val := by simp only [Fin.val_natAdd]; omega
    simp only [widen, hj, dite_true]
    congr 1
    ext
    simp only [Fin.val_natAdd]
    omega
  rw [h1, h2, Unit4Post.encode_nil]

/-- The literal H_A3 input bank. -/
def inputBank (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (k : ℕ) (t : (TotalFiniteConstructorScratch.select hn
      (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) : Fin 3 → List Bool :=
  ![EncodedGraph.encode g, List.replicate k true,
    (TotalFiniteConstructorScratch.select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t]

variable {L V : Type} [Fintype L] [Fintype V]

/-- NAMED PREMISE (local run): the fixed local program `P` on `a + 3` cells, started on the widened
H_A3 bank, halts within `C·(n+2)^(E(k+1))` steps with the consumer word in cell `j`, and the final bank
has encoded size within the same bound. Binders exactly those of `Shells.H_A3`. -/
def LocalRun (Δ : ℕ) (γ : ℚ) (a : ℕ) (P : L → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L V)
    (start : L) (initial : V) (j : Fin (a + 3)) (C E : ℕ) : Prop :=
  ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ), 1 ≤ k →
    (∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v) →
    (∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ) →
    ∀ t : (TotalFiniteConstructorScratch.select hn
        (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape,
      ∃ (T : ℕ) (c : TM2.Cfg (fun _ : Fin (a + 3) => Bool) L V),
        T ≤ C * (g.vertices + 2) ^ (E * (k + 1)) ∧
        ((advance P)^[T]) ⟨some start, initial, widen a (inputBank Δ γ g hg hn k t)⟩ = c ∧
        c.l = none ∧
        c.stk j = EncodedSelectedOutput.outputBits hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k t ∧
        (BitMachineBankCodec.encode c.stk).length ≤ C * (g.vertices + 2) ^ (E * (k + 1))

/-- NAMED PREMISE (input size): the literal H_A3 packet has length within `C·(n+2)^(E(k+1))`. -/
def InputSize (Δ : ℕ) (γ : ℚ) (C E : ℕ) : Prop :=
  ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ), 1 ≤ k →
    (∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v) →
    (∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ) →
    ∀ t : (TotalFiniteConstructorScratch.select hn
        (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape,
      (BitMachineBankCodec.encode (inputBank Δ γ g hg hn k t)).length ≤
        C * (g.vertices + 2) ^ (E * (k + 1))

theorem halted_fixed {K : Type} [DecidableEq K] {Λ σ : Type}
    (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (v : σ) (S : K → List Bool) (u : ℕ) :
    ((advance P)^[u]) (⟨none, v, S⟩ : TM2.Cfg (fun _ : K => Bool) Λ σ) = ⟨none, v, S⟩ := by
  induction u with
  | zero => rfl
  | succ u ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem cfg_eta_none {K : Type} {Λ σ : Type}
    (d : TM2.Cfg (fun _ : K => Bool) Λ σ) (h : d.l = none) : d = ⟨none, d.var, d.stk⟩ := by
  rcases d with ⟨l, v, s⟩
  change l = none at h
  subst h
  rfl

open Classical in
/-- The (noncomputable, specification-only) final bank of the local run; the machine is fixed. -/
noncomputable def finalBank {a : ℕ} (P : L → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L V)
    (start : L) (initial : V) (S : Fin (a + 3) → List Bool) : Fin (a + 3) → List Bool :=
  if h : ∃ T, (((advance P)^[T]) ⟨some start, initial, S⟩).l = none then
    (((advance P)^[Nat.find h]) ⟨some start, initial, S⟩).stk
  else S

omit [Fintype L] [Fintype V] in
theorem finalBank_spec {a : ℕ} (P : L → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L V)
    (start : L) (initial : V) (S : Fin (a + 3) → List Bool) (T : ℕ)
    (c : TM2.Cfg (fun _ : Fin (a + 3) => Bool) L V)
    (hr : ((advance P)^[T]) ⟨some start, initial, S⟩ = c) (hl : c.l = none) :
    ∃ T' ≤ T, (((advance P)^[T']) ⟨some start, initial, S⟩).l = none ∧
      (((advance P)^[T']) ⟨some start, initial, S⟩).stk = finalBank P start initial S ∧
      finalBank P start initial S = c.stk := by
  classical
  have h : ∃ T, (((advance P)^[T]) ⟨some start, initial, S⟩).l = none := ⟨T, by rw [hr]; exact hl⟩
  have hle : Nat.find h ≤ T := Nat.find_min' h (by rw [hr]; exact hl)
  have hspec := Nat.find_spec h
  have hfb : finalBank P start initial S =
      (((advance P)^[Nat.find h]) ⟨some start, initial, S⟩).stk := by
    unfold finalBank; rw [dif_pos h]
  refine ⟨Nat.find h, hle, hspec, hfb.symm, ?_⟩
  rw [hfb]
  set d := ((advance P)^[Nat.find h]) ⟨some start, initial, S⟩ with hd
  have hdc : d = ⟨none, d.var, d.stk⟩ := cfg_eta_none d hspec
  have hT : T = (T - Nat.find h) + Nat.find h := by omega
  have hc : c = ((advance P)^[T - Nat.find h]) d := by
    rw [← hr, hT, Function.iterate_add_apply, ← hd]
    simp only [Nat.add_sub_cancel]
  rw [hc, hdc, halted_fixed]

private theorem clock_arith (K a C N x w : ℕ) (hN : 1 ≤ N) (hx : x ≤ C * N) (hw : w ≤ C * N) :
    a + 1 + 2 * (a + x) + 2 +
        ((2 * K + 1) * (a + x + 1) + C * N + 2 * (C * N) + 4 + 2 * w + 2 +
          (2 * K + 4) * (w + 1)) ≤
      (3 * a + 9 + 2 * C + (2 * K + 1) * (a + 1 + C) + 5 * C + (2 * K + 4) * (C + 1)) * N := by
  have h1 : (2 * K + 1) * (a + x + 1) ≤ (2 * K + 1) * ((a + 1) * N + C * N) := by
    apply Nat.mul_le_mul_left
    have : a + 1 ≤ (a + 1) * N := Nat.le_mul_of_pos_right _ hN
    omega
  have h2 : (2 * K + 4) * (w + 1) ≤ (2 * K + 4) * (C * N + N) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : 3 * a + 9 ≤ (3 * a + 9) * N := Nat.le_mul_of_pos_right _ hN
  have hexp : (3 * a + 9 + 2 * C + (2 * K + 1) * (a + 1 + C) + 5 * C + (2 * K + 4) * (C + 1)) * N =
      (3 * a + 9) * N + 2 * (C * N) + (2 * K + 1) * ((a + 1) * N + C * N) + 5 * (C * N) +
        (2 * K + 4) * (C * N + N) := by ring
  rw [hexp]
  omega

set_option maxHeartbeats 1000000 in
/-- **Segment 4 (generic): H_A3 from the named local-run and input-size premises.** -/
theorem H_A3_of_local (Δ : ℕ) (γ : ℚ) (a : ℕ)
    (P : L → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L V) (start : L) (initial : V)
    (j : Fin (a + 3)) (C E : ℕ)
    (hrun : LocalRun Δ γ a P start initial j C E) (hin : InputSize Δ γ C E) :
    Unit4Shell.Shells.H_A3 Δ γ := by
  refine ⟨BitMachineComposition.composition (Unit4Post.Pre.machine a)
      (BitMachineComposition.composition (BitMachineBankWrapper.machine P start initial)
        (BankFieldProjection.machine j)),
    3 * a + 9 + 2 * C + (2 * (a + 3) + 1) * (a + 1 + C) + 5 * C + (2 * (a + 3) + 4) * (C + 1),
    E, ?_⟩
  intro g hg hn k hk hsurj hdeg t
  change BitMachine.Machine.OutputsWithin _
    (BitMachineBankCodec.encode (inputBank Δ γ g hg hn k t)) _ _
  obtain ⟨X, hX⟩ : ∃ X, X = inputBank Δ γ g hg hn k t := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N, N = (g.vertices + 2) ^ (E * (k + 1)) := ⟨_, rfl⟩
  rw [← hX, ← hNdef]
  have hN : 1 ≤ N := by rw [hNdef]; exact Nat.one_le_pow _ _ (by omega)
  obtain ⟨T, c, hT, hr, hl, hj, hsz⟩ := hrun g hg hn k hk hsurj hdeg t
  have hx := hin g hg hn k hk hsurj hdeg t
  rw [← hX, ← hNdef] at hx
  rw [← hX] at hr
  rw [← hNdef] at hT hsz
  obtain ⟨T', hT', _, _, hF⟩ := finalBank_spec P start initial (widen a X) T c hr hl
  -- stage 1: Pre
  have hpre := Unit4Post.Pre.outputs a (BitMachineBankCodec.encode X)
  rw [← encode_widen] at hpre
  -- stage 2: the admitted bank wrapper
  have hwrap := BitMachineBankWrapper.outputs P start initial (finalBank P start initial)
    (BitMachineBankCodec.encode (widen a X)) (C * N) (C * N)
    (by
      intro S hd
      rw [BitMachineBankCodec.decode_encode] at hd
      cases Option.some.inj hd
      obtain ⟨T'', hT'', hl'', hs'', _⟩ := finalBank_spec P start initial (widen a X) T c hr hl
      exact ⟨T'', _, hT''.trans hT, rfl, hl'', hs''⟩)
    (by
      intro S hd
      rw [BitMachineBankCodec.decode_encode] at hd
      cases Option.some.inj hd
      rw [hF]; exact hsz)
  have hres : BitMachineBankWrapper.result (finalBank P start initial)
      (BitMachineBankCodec.encode (widen a X)) =
      BitMachineBankCodec.encode (finalBank P start initial (widen a X)) := by
    simp only [BitMachineBankWrapper.result, BitMachineBankCodec.decode_encode]
  rw [hres, hF] at hwrap
  -- stage 3: the admitted field projection
  have hproj := BankFieldProjection.outputs j (BitMachineBankCodec.encode c.stk)
  rw [BankFieldProjection.result_encode, hj] at hproj
  have h23 := BitMachineComposition.composition_outputsWithin _ _ hwrap hproj
  have h123 := BitMachineComposition.composition_outputsWithin _ _ hpre h23
  apply BitMachine.outputsWithin_mono _ h123
  have hlen1 : (BitMachineBankCodec.encode (widen a X)).length =
      a + (BitMachineBankCodec.encode X).length := by
    rw [encode_widen, List.length_append, List.length_replicate]
  rw [hlen1]
  have := clock_arith (a + 3) a C N (BitMachineBankCodec.encode X).length
    (BitMachineBankCodec.encode c.stk).length hN hx hsz
  exact this

end Paper2.A3Assembly.Wrap

#print axioms Paper2.A3Assembly.Wrap.encode_widen
#print axioms Paper2.A3Assembly.Wrap.finalBank_spec
#print axioms Paper2.A3Assembly.Wrap.H_A3_of_local
