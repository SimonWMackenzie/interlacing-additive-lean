import CurrentAdditive.V39RLoopCurrent

/-! Unit 3, segment (2): the k-fold recursion of `RecursiveEntries.request` as ONE
loop. The ONE fixed program `rloop = CountedLoop.loop ctr body bodyStart bodyCtl`
(production `CountedLoop`), run from the level-`K` loop bank of a level-`K` pair
`(x, y)` (the counter holds `K` marks), halts in EXACTLY the level-`0` loop bank
of `V39RecursiveTable.seedRequest activity K x y` (its row and column encodings in
`r1 Xc`, `r1 Yc`, the level-`0` codes in `nC 0`, `nC 1`, `E` blank, the master region
unchanged, the counter empty), within `K * (Bd + 2) + 1` steps, where `Bd` is the
`Finset.sup` over the `K` levels of the checked body clock. Level marks are produced
from the loop counter; every level's requests are the typed chain `lstep`. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39RLoop

noncomputable section

open Paper2
open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- A level together with a pair of that level. -/
abbrev Lvl (n p s q₁ q₂ w Q : ℕ) :=
  Σ k : ℕ, V39RecursiveGenerator.Row n p q₁ q₂ s w Q k ×
    V39RecursiveGenerator.Column n p q₁ q₂ s w Q k

/-- The typed request chain: one level down by `RecursiveEntries.request`. -/
def lstep {n : ℕ} (activity : SourceConstruction.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q) :
    Lvl n p s q₁ q₂ w Q → Lvl n p s q₁ q₂ w Q
  | ⟨0, xy⟩ => ⟨0, xy⟩
  | ⟨k + 1, xy⟩ => ⟨k, V39RecursiveTable.request activity k xy.1 xy.2⟩

theorem lstep_level {n : ℕ} (activity : SourceConstruction.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (lv : Lvl n p s q₁ q₂ w Q) : (lstep activity ξ lv).1 = lv.1 - 1 := by
  rcases lv with ⟨_ | k, xy⟩ <;> rfl

theorem iter_level {n : ℕ} (activity : SourceConstruction.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (lv : Lvl n p s q₁ q₂ w Q) (i : ℕ) : ((lstep activity ξ)^[i] lv).1 = lv.1 - i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', lstep_level, ih]; omega

theorem iter_seed {n : ℕ} (activity : SourceConstruction.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q) (k : ℕ)
    (x : V39RecursiveGenerator.Row n p q₁ q₂ s w Q k)
    (y : V39RecursiveGenerator.Column n p q₁ q₂ s w Q k) :
    (lstep activity ξ)^[k] ⟨k, (x, y)⟩ = ⟨0, V39RecursiveTable.seedRequest activity k x y⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ _

/-- The body clock of one level (zero at level `0`, never used there). -/
def clockLv (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q) :
    Lvl g.vertices p s q₁ q₂ w Q → ℕ
  | ⟨0, _⟩ => 0
  | ⟨k + 1, xy⟩ => bodyClock g hg hs r hq ξ k xy.1 xy.2

/-- The uniform per-level bound: the maximum over the `K` levels actually visited. -/
def loopBd (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K : ℕ)
    (x : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (y : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) : ℕ :=
  (Finset.range K).sup (fun i => clockLv g hg hs r hq ξ
    ((lstep (V39EdgeSourceFront.edgeActivity g hg (by omega) r hq)
      ξ)^[i] ⟨K, (x, y)⟩))

/-- Segment (2): the k-fold request recursion as ONE loop, exact entry and exit banks. -/
theorem request_loop (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K : ℕ)
    (x : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (y : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K)
    (c : Option Bool × type_of% bodyCtl) :
    let activity := V39EdgeSourceFront.edgeActivity g hg (by omega) r hq
    let sd := V39RecursiveTable.seedRequest activity K x y
    ∃ t ≤ K * (loopBd g hg hs r hq ξ K x y + 2) + 1, ∃ c',
      ((advance rloop)^[t])
        (⟨some (.inl ()), c, bankCurrent g r K x y⟩ : TM2.Cfg (fun _ : JL => Bool) _ _) =
        ⟨none, c', bankCurrent (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r 0 sd.1 sd.2⟩ := by
  intro activity sd
  let S : ℕ → JL → List Bool := fun i =>
    bankCurrent g r ((lstep activity ξ)^[i] ⟨K, (x, y)⟩).1 ((lstep activity ξ)^[i] ⟨K, (x, y)⟩).2.1
      ((lstep activity ξ)^[i] ⟨K, (x, y)⟩).2.2
  have hS0 : S 0 = bankCurrent g r K x y := rfl
  have hSK : S K = bankCurrent (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r 0 sd.1 sd.2 := by
    show bankCurrent g r ((lstep activity ξ)^[K] ⟨K, (x, y)⟩).1 _ _ = _
    rw [iter_seed activity ξ K x y]
  have hctr : ∀ i ≤ K, S i ctr = List.replicate (K - i) true := by
    intro i _
    show List.replicate ((lstep activity ξ)^[i] ⟨K, (x, y)⟩).1 true = _
    rw [iter_level]
  have hbody : ∀ i < K, ∃ t ≤ loopBd g hg hs r hq ξ K x y, ∃ v₁,
      ((advance body)^[t]) (⟨some bodyStart, bodyCtl, Function.update (S i) ctr
        (List.replicate (K - i - 1) true)⟩ : TM2.Cfg (fun _ : JL => Bool) _ _) =
        ⟨none, v₁, S (i + 1)⟩ := by
    intro i hi
    have hlev := iter_level activity ξ ⟨K, (x, y)⟩ i
    have hle : clockLv g hg hs r hq ξ ((lstep activity ξ)^[i] ⟨K, (x, y)⟩) ≤
        loopBd g hg hs r hq ξ K x y :=
      Finset.le_sup (f := fun i => clockLv g hg hs r hq ξ ((lstep activity ξ)^[i] ⟨K, (x, y)⟩))
        (Finset.mem_range.mpr hi)
    have hS1 : S (i + 1) = bankCurrent g r (lstep activity ξ ((lstep activity ξ)^[i] ⟨K, (x, y)⟩)).1
        (lstep activity ξ ((lstep activity ξ)^[i] ⟨K, (x, y)⟩)).2.1
        (lstep activity ξ ((lstep activity ξ)^[i] ⟨K, (x, y)⟩)).2.2 := by
      show bankCurrent g r ((lstep activity ξ)^[i + 1] ⟨K, (x, y)⟩).1 _ _ = _
      rw [Function.iterate_succ_apply']
    rw [hS1]
    show ∃ t ≤ _, ∃ v₁, ((advance body)^[t]) ⟨some bodyStart, bodyCtl, Function.update
      (bankCurrent g r ((lstep activity ξ)^[i] ⟨K, (x, y)⟩).1 ((lstep activity ξ)^[i] ⟨K, (x, y)⟩).2.1
        ((lstep activity ξ)^[i] ⟨K, (x, y)⟩).2.2) ctr (List.replicate (K - i - 1) true)⟩ = _
    revert hle hlev
    generalize (lstep activity ξ)^[i] ⟨K, (x, y)⟩ = lv
    rcases lv with ⟨_ | k, xx, yy⟩
    · intro hlev; simp at hlev; omega
    · intro hlev hle
      simp only at hlev
      have hk : K - i - 1 = k := by omega
      rw [hk]
      obtain ⟨t, ht, v, hrun⟩ := body_run_current g hg hp hs r hq ξ k xx yy
      exact ⟨t, le_trans ht hle, v, hrun⟩
  obtain ⟨t, ht, c', hrun⟩ := CountedLoop.loop_run ctr body bodyStart bodyCtl K
    (loopBd g hg hs r hq ξ K x y) S hctr hbody c
  refine ⟨t, ht, c', ?_⟩
  rw [← hSK]
  exact hrun

end

#print axioms lstep_level
#print axioms iter_level
#print axioms iter_seed
#print axioms request_loop

end CurrentAdditive.V39RLoop
