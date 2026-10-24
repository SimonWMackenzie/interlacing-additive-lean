import Paper2.A3LLayout
import Paper2.FullSched

/-! Unit 3 (lock v12 App. D; T44/U10), lane a-success-table-13, segment (1): the `Checks` decision bit.

ONE fixed two-label controller on any bank with three distinct cells `A`, `B`, `O` (machine constants: the caps
`NA NB` and a finite table `f`): it pops `A` to the end, counting in its finite control with saturation at `NA`,
then pops `B` to the end, counting with saturation at `NB`, then pushes the table bit `f (min |A| NA) (min |B| NB)`
on `O` and halts. Exit: `A`, `B` blank, `O` extended by exactly that bit, every other cell unchanged; clock
exactly `|A| + |B| + 2`.

At the machine constants `NA = sizeThreshold Δ γ = 2 ^ cutoff Δ γ`, `NB = Δ · NA` and the table
`tab Δ γ ca cb = (NA ≤ ca) || decide (Checks (Fin ca) (Fin cb) (clog₂ ca) Δ γ)`, the bit is `decide (ChecksCond …)`
for every H_A3 instance (`tab_correct`): above the cutoff by the admitted `all_large_checks_at_graph`, below it
because `m ≤ Δ n < NB` (admitted double counting `twice_edges_le_degree_vertices`), so the table entry is read at
the exact `(n, m)`. -/

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Paper2.CheckBit

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive DL where
  | rdA | rdB
  deriving DecidableEq, Fintype

/-- Saturating increment. -/
def sat {N : ℕ} (c : Fin (N + 1)) : Fin (N + 1) := ⟨min (c.val + 1) N, by omega⟩

/-- Saturating addition of `a`. -/
def satN {N : ℕ} (a : ℕ) (c : Fin (N + 1)) : Fin (N + 1) := ⟨min (c.val + a) N, by omega⟩

abbrev DV (NA NB : ℕ) := Bool × (Fin (NA + 1) × Fin (NB + 1))

variable {K : Type*} [DecidableEq K]

def program (A B O : K) (NA NB : ℕ) (f : ℕ → ℕ → Bool) :
    DL → TM2.Stmt (fun _ : K => Bool) DL (DV NA NB)
  | .rdA => .pop A (fun v x => (x.isSome, (if x.isSome then sat v.2.1 else v.2.1), v.2.2))
      (.branch (fun v => v.1) (.goto fun _ => .rdA) (.goto fun _ => .rdB))
  | .rdB => .pop B (fun v y => (y.isSome, v.2.1, (if y.isSome then sat v.2.2 else v.2.2)))
      (.branch (fun v => v.1) (.goto fun _ => .rdB)
        (.push O (fun v => f v.2.1.val v.2.2.val) .halt))

/-- The initial control. -/
def ctl0 (NA NB : ℕ) : DV NA NB := (false, 0, 0)

theorem sat_satN {N : ℕ} (a : ℕ) (c : Fin (N + 1)) : satN a (sat c) = satN (a + 1) c := by
  ext; simp only [satN, sat]; omega

theorem satN_zero {N : ℕ} (c : Fin (N + 1)) : satN 0 c = c := by
  ext; simp only [satN]; omega

theorem rdA_run (A B O : K) (NA NB : ℕ) (f : ℕ → ℕ → Bool) (S : K → List Bool) (v : DV NA NB) (a : ℕ)
    (hA : S A = List.replicate a true) :
    ((advance (program A B O NA NB f))^[a + 1])
      (⟨some .rdA, v, S⟩ : TM2.Cfg (fun _ : K => Bool) DL (DV NA NB)) =
      ⟨some .rdB, (false, satN a v.2.1, v.2.2), Function.update S A []⟩ := by
  induction a generalizing S v with
  | zero =>
      have hA0 : S A = [] := by simpa using hA
      have hu : Function.update S A [] = S := Function.update_eq_self_iff.mpr hA0.symm
      simp [advance, TM2.step, TM2.stepAux, program, hA0, hu, satN_zero]
  | succ a ih =>
      have h1 : advance (program A B O NA NB f)
          (⟨some .rdA, v, S⟩ : TM2.Cfg (fun _ : K => Bool) DL (DV NA NB)) =
          ⟨some .rdA, (true, sat v.2.1, v.2.2), Function.update S A (List.replicate a true)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, hA, List.replicate_succ]
      rw [Function.iterate_succ_apply, h1,
        ih (Function.update S A (List.replicate a true)) (true, sat v.2.1, v.2.2) (by simp),
        Function.update_idem, sat_satN]

theorem rdB_run (A B O : K) (hBO : B ≠ O) (NA NB : ℕ) (f : ℕ → ℕ → Bool) (S : K → List Bool)
    (v : DV NA NB) (b : ℕ) (hB : S B = List.replicate b true) :
    ((advance (program A B O NA NB f))^[b + 1])
      (⟨some .rdB, v, S⟩ : TM2.Cfg (fun _ : K => Bool) DL (DV NA NB)) =
      ⟨none, (false, v.2.1, satN b v.2.2),
        Function.update (Function.update S B []) O (f v.2.1.val (satN b v.2.2).val :: S O)⟩ := by
  have hOB : O ≠ B := Ne.symm hBO
  induction b generalizing S v with
  | zero =>
      have hB0 : S B = [] := by simpa using hB
      have hu : Function.update S B [] = S := Function.update_eq_self_iff.mpr hB0.symm
      simp [advance, TM2.step, TM2.stepAux, program, hB0, hu, satN_zero]
  | succ b ih =>
      have h1 : advance (program A B O NA NB f)
          (⟨some .rdB, v, S⟩ : TM2.Cfg (fun _ : K => Bool) DL (DV NA NB)) =
          ⟨some .rdB, (true, v.2.1, sat v.2.2), Function.update S B (List.replicate b true)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, hB, List.replicate_succ]
      rw [Function.iterate_succ_apply, h1,
        ih (Function.update S B (List.replicate b true)) (true, v.2.1, sat v.2.2) (by simp),
        Function.update_idem, sat_satN, Function.update_of_ne hOB]

/-- **The decision run** (generic bank): exit bank exact, clock exactly `a + b + 2`. -/
theorem decide_run (A B O : K) (hAB : A ≠ B) (hAO : A ≠ O) (hBO : B ≠ O) (NA NB : ℕ)
    (f : ℕ → ℕ → Bool) (S : K → List Bool) (a b : ℕ)
    (hA : S A = List.replicate a true) (hB : S B = List.replicate b true) :
    ∃ w, ((advance (program A B O NA NB f))^[a + b + 2])
      (⟨some .rdA, ctl0 NA NB, S⟩ : TM2.Cfg (fun _ : K => Bool) DL (DV NA NB)) =
      ⟨none, w, Function.update (Function.update (Function.update S A []) B []) O
        (f (min a NA) (min b NB) :: S O)⟩ := by
  have hBA : B ≠ A := Ne.symm hAB
  have hOA : O ≠ A := Ne.symm hAO
  refine ⟨(false, satN a (0 : Fin (NA + 1)), satN b (0 : Fin (NB + 1))), ?_⟩
  have e : a + b + 2 = (b + 1) + (a + 1) := by omega
  rw [e, Function.iterate_add_apply, rdA_run A B O NA NB f S (ctl0 NA NB) a hA,
    rdB_run A B O hBO NA NB f (Function.update S A []) _ b (by rw [Function.update_of_ne hBA]; exact hB)]
  have h1 : (satN a (ctl0 NA NB).2.1).val = min a NA := by simp [satN, ctl0]
  have h2 : (satN b (ctl0 NA NB).2.2).val = min b NB := by simp [satN, ctl0]
  rw [h1, h2, Function.update_of_ne hOA]
  rfl

/-! ### The table at the machine constants `(Δ, γ)` -/

/-- Cap on `n`: the admitted size threshold `2 ^ cutoff Δ γ`. -/
def NA (Δ : ℕ) (γ : ℚ) : ℕ := CompletePublicScheduleScratch.sizeThreshold Δ γ
/-- Cap on `m`. -/
def NB (Δ : ℕ) (γ : ℚ) : ℕ := Δ * NA Δ γ

/-- The finite decision table (machine constant). -/
def tab (Δ : ℕ) (γ : ℚ) (ca cb : ℕ) : Bool :=
  decide (NA Δ γ ≤ ca) ||
    decide (CompletePublicScheduleScratch.Checks (V := Fin ca) (E := Fin cb) (Nat.clog 2 ca) Δ γ)

/-- The decision controller at the machine constants. -/
def checkProg (A B O : K) (Δ : ℕ) (γ : ℚ) := program A B O (NA Δ γ) (NB Δ γ) (tab Δ γ)

/-- **Correctness of the table** on every H_A3 instance. -/
theorem tab_correct (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ) :
    (tab Δ γ (min g.vertices (NA Δ γ)) (min g.edges.length (NB Δ γ)) = true ↔
      CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) Δ γ) := by
  haveI : Nonempty (Fin g.vertices) := ⟨⟨0, hn⟩⟩
  by_cases hbig : NA Δ γ ≤ g.vertices
  · have hmin : min g.vertices (NA Δ γ) = NA Δ γ := min_eq_right hbig
    have hC := CompletePublicScheduleScratch.all_large_checks_at_graph
      (V := Fin g.vertices) (E := Fin g.edges.length) (CanonicalEdgeTape.graphEdge g hg) Δ γ hγ hΔ hinc hdeg
      (by simpa only [Fintype.card_fin] using hbig)
    simp only [Fintype.card_fin] at hC
    simp only [tab, hmin, le_refl, decide_true, Bool.true_or, true_iff]
    exact hC
  · have hsmall : g.vertices < NA Δ γ := Nat.lt_of_not_le hbig
    have hmin : min g.vertices (NA Δ γ) = g.vertices := min_eq_left (le_of_lt hsmall)
    have h2 := SourceDensityScheduleScratch.twice_edges_le_degree_vertices
      (V := Fin g.vertices) (E := Fin g.edges.length) (CanonicalEdgeTape.graphEdge g hg) Δ hdeg
    simp only [Fintype.card_fin] at h2
    have hm : g.edges.length ≤ NB Δ γ := by
      have : Δ * g.vertices ≤ Δ * NA Δ γ := Nat.mul_le_mul_left _ (le_of_lt hsmall)
      simp only [NB]; omega
    have hminm : min g.edges.length (NB Δ γ) = g.edges.length := min_eq_left hm
    rw [hmin, hminm]
    simp only [tab, Bool.or_eq_true, decide_eq_true_iff]
    exact ⟨fun h => h.resolve_left hbig, fun h => Or.inr h⟩

/-- `0 < |E(g)|` and `0 < Δ` from the H_A3 hypotheses (admitted `vertices_le_twice_edges` and double counting). -/
theorem pos_of_hyp (Δ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ) :
    0 < g.edges.length ∧ 0 < Δ := by
  haveI : Nonempty (Fin g.vertices) := ⟨⟨0, hn⟩⟩
  have h1 := SourceConstruction.vertices_le_twice_edges
    (V := Fin g.vertices) (E := Fin g.edges.length) (CanonicalEdgeTape.graphEdge g hg) hinc
  have h2 := SourceDensityScheduleScratch.twice_edges_le_degree_vertices
    (V := Fin g.vertices) (E := Fin g.edges.length) (CanonicalEdgeTape.graphEdge g hg) Δ hdeg
  simp only [Fintype.card_fin] at h1 h2
  refine ⟨Nat.pos_of_ne_zero (fun h0 => by rw [h0] at h1; omega), ?_⟩
  rcases Nat.eq_zero_or_pos Δ with h | h
  · subst h; omega
  · exact h

/-- **Segment (1)**: the decision bit on a generic bank holding unary `n` in `A` and unary `m` in `B`. -/
theorem check_run (A B O : K) (hAB : A ≠ B) (hAO : A ≠ O) (hBO : B ≠ O) (Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ)
    (S : K → List Bool) (hA : S A = List.replicate g.vertices true)
    (hB : S B = List.replicate g.edges.length true) :
    ∃ w, ∃ bit : Bool, ((advance (checkProg A B O Δ γ))^[g.vertices + g.edges.length + 2])
      (⟨some .rdA, ctl0 (NA Δ γ) (NB Δ γ), S⟩ : TM2.Cfg (fun _ : K => Bool) DL (DV (NA Δ γ) (NB Δ γ))) =
      ⟨none, w, Function.update (Function.update (Function.update S A []) B []) O (bit :: S O)⟩ ∧
      (bit = true ↔ CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) Δ γ) := by
  obtain ⟨w, hw⟩ := decide_run A B O hAB hAO hBO (NA Δ γ) (NB Δ γ) (tab Δ γ) S _ _ hA hB
  exact ⟨w, _, hw, tab_correct Δ γ hγ hΔ g hg hn hinc hdeg⟩

end Paper2.CheckBit

#print axioms Paper2.CheckBit.decide_run
#print axioms Paper2.CheckBit.tab_correct
#print axioms Paper2.CheckBit.pos_of_hyp
#print axioms Paper2.CheckBit.check_run
