import Paper2.WEntry
import Paper2.CodedEntryEvaluator
import EthInapproximability.CurrentPaper.MatrixTableWriter

/-! Unit 3, segment (4), second part: the `Fin K` instance of the admitted
`MatrixTableWriter.EntryRuns` contract for the per-entry program `WEntry.wprog`, and
the admitted `MatrixTableWriter.write_rowMajor` run of the successful table.
The writer's bank is `CellStack Kw = Fin Kw ⊕ Fin 3` with `Kw = card Aux`; the
auxiliary cells are placed by the fixed enumeration `Fintype.equivFin Aux`
(a fixed finite choice; one fixed program). The per-entry clock is the explicit
maximum `Tent` of `WEntry.entryBd` over the `mX * mY` entries. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.WEntry

noncomputable section

attribute [local irreducible] entryBd coreBd

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries

@[irreducible] def Kw : ℕ := Fintype.card Aux

def eqv : Aux ≃ Fin Kw := by unfold Kw; exact Fintype.equivFin Aux

def ιWf : A → MatrixTableWriter.CellStack Kw := Sum.map eqv id

theorem ιWf_injective : Function.Injective ιWf :=
  Sum.map_injective.mpr ⟨eqv.injective, fun _ _ h => h⟩

def ιW : A ↪ MatrixTableWriter.CellStack Kw := ⟨ιWf, ιWf_injective⟩

/-- The per-entry program on the writer's cell bank: ONE fixed program. -/
def P := fun l => stackStmt ιW (wprog l)

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The writer's fixed bank (`Fin Kw` cells). -/
def bankW (g : EncodedGraph.Graph) (r K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) : Fin Kw → List Bool :=
  fun i => auxBank g r K mX mY xs ys (eqv.symm i)

/-- The table entry read by the writer (`false` outside the dimensions, never read). -/
def entryF (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) : ℕ → ℕ → Bool :=
  fun x y => if h : x < mX ∧ y < mY then
    RecursiveEntries.matrix (LookupSeed.matrix p)
      (SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) ξ K
      (xs ⟨x, h.1⟩) (ys ⟨y, h.2⟩)
  else false

/-- The uniform per-entry clock: the maximum of the explicit per-entry clocks. -/
def Tent (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) : ℕ :=
  (Finset.univ : Finset (Fin mX × Fin mY)).sup
    (fun ij => entryBd g hg hs r hq ξ K mX mY xs ys ij.1 ij.2)

theorem entryBd_le_Tent (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s)
    (r : ℕ) (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) (i : Fin mX) (j : Fin mY) :
    entryBd g hg hs r hq ξ K mX mY xs ys i j ≤ Tent g hg hs r hq ξ K mX mY xs ys := by
  unfold Tent
  exact Finset.le_sup (f := fun ij : Fin mX × Fin mY =>
    entryBd g hg hs r hq ξ K mX mY xs ys ij.1 ij.2) (Finset.mem_univ (i, j))

theorem ιW_inl (k : Fin Kw) : (Sum.inl k : MatrixTableWriter.CellStack Kw) = ιW (.inl (eqv.symm k)) := by
  show Sum.inl k = Sum.map eqv id (Sum.inl (eqv.symm k))
  simp

theorem ιW_inr (i : Fin 3) : (Sum.inr i : MatrixTableWriter.CellStack Kw) = ιW (.inr i) := rfl

/-- Transport of one entry run from the bank `A` to the writer's cell bank. -/
theorem transport (g : EncodedGraph.Graph) (r K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) (x y : ℕ) (b : Bool) (t : ℕ) (v : _)
    (hrun : ((advance wprog)^[t])
        (⟨some wStart, wCtl, bankA g r K mX mY xs ys x y []⟩ :
          TM2.Cfg (fun _ : A => Bool) _ _) =
        ⟨none, v, bankA g r K mX mY xs ys x y [b]⟩) :
    ((advance P)^[t]) (MatrixTableWriter.cellCfg (some wStart) wCtl
        (bankW g r K mX mY xs ys) x y []) =
      MatrixTableWriter.cellCfg none v (bankW g r K mX mY xs ys) x y [b] := by
  set F0 : MatrixTableWriter.CellStack Kw → List Bool :=
    Sum.elim (bankW g r K mX mY xs ys)
      (![List.replicate x true, List.replicate y true, []] : Fin 3 → List Bool) with hF0
  have hS : ∀ a, bankA g r K mX mY xs ys x y [] a = F0 (ιW a) := by
    intro a
    rcases a with z | i
    · show auxBank g r K mX mY xs ys z = auxBank g r K mX mY xs ys (eqv.symm (eqv z))
      rw [Equiv.symm_apply_apply]
    · rfl
  have h := BitMachineStackRun.run ιW F0 wprog
    (⟨some wStart, wCtl, bankA g r K mX mY xs ys x y []⟩ : TM2.Cfg (fun _ : A => Bool) _ _) t
  rw [hrun] at h
  simp only [stackCfg] at h
  rw [bank_eq_self ιW F0 _ hS] at h
  have hend : bank ιW F0 (bankA g r K mX mY xs ys x y [b]) =
      Sum.elim (bankW g r K mX mY xs ys)
        (![List.replicate x true, List.replicate y true, [b]] : Fin 3 → List Bool) := by
    funext c
    rcases c with k | i
    · conv_lhs => rw [ιW_inl k]
      rw [bank_at]; rfl
    · conv_lhs => rw [ιW_inr i]
      rw [bank_at]; rfl
  rw [hend] at h
  exact h

/-- The `EntryRuns` instance: for every `x < mX`, `y < mY`, the ONE program `P` halts
within `Tent` on the writer's fixed bank with `[entryF x y]` in the answer cell and
the bank and both coordinates restored exactly. -/
theorem entry_runs (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (hfix : ∀ (k : ℕ) (i : SourceConstruction.Items s (Fin g.vertices))
      (js : Fin s → SourceMatrix.OuterColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k)),
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.encode
        (SourceMatrix.sourceColumn (SourceActiveRank.scanAtCanonical
          (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) i
          (SourceMatrix.forgetTag (ξ k) (.fixedTail js))) =
        (CanonicalDefaultWordScratch.words p s q₁ q₂ w Q k).2)
    (K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) :
    MatrixTableWriter.EntryRuns P wStart wCtl (bankW g r K mX mY xs ys) mX mY
      (Tent g hg hs r hq ξ K mX mY xs ys) (entryF g hg hs r hq ξ K mX mY xs ys) := by
  intro x hx y hy
  obtain ⟨t, ht, v, hrun⟩ := entry_run g hg hp hs r hq ξ hfix K mX mY xs ys ⟨x, hx⟩ ⟨y, hy⟩
  have hT := entryBd_le_Tent g hg hs r hq ξ K mX mY xs ys ⟨x, hx⟩ ⟨y, hy⟩
  have he : entryF g hg hs r hq ξ K mX mY xs ys x y =
      RecursiveEntries.matrix (LookupSeed.matrix p)
        (SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) ξ K
        (xs ⟨x, hx⟩) (ys ⟨y, hy⟩) := by
    simp only [entryF, dif_pos (And.intro hx hy)]
  refine ⟨t, ht.trans hT, v, ?_⟩
  rw [he]
  exact transport g r K mX mY xs ys x y _ t v hrun

/-- The successful table writer: the admitted row-major writer, driven by the ONE
entry program `P`, prints `rowMajor f ++ output` with
`f i j = RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ K (xs i) (ys j)`
within `writerBound mX mY Tent`, restoring its bank. -/
theorem table_run (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (hfix : ∀ (k : ℕ) (i : SourceConstruction.Items s (Fin g.vertices))
      (js : Fin s → SourceMatrix.OuterColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k)),
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.encode
        (SourceMatrix.sourceColumn (SourceActiveRank.scanAtCanonical
          (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) i
          (SourceMatrix.forgetTag (ξ k) (.fixedTail js))) =
        (CanonicalDefaultWordScratch.words p s q₁ q₂ w Q k).2)
    (K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) (output : List Bool) :
    let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
      (by omega) hq
    let f : Fin mX → Fin mY → Bool := fun i j =>
      RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ K (xs i) (ys j)
    ∃ t ≤ MatrixTableWriter.writerBound mX mY (Tent g hg hs r hq ξ K mX mY xs ys), ∃ v,
      MatrixTableWriter.run P wStart wCtl t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows))) (wCtl, none)
          (MatrixTableWriter.ready (bankW g r K mX mY xs ys) mX mY 0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready (bankW g r K mX mY xs ys) mX mY 0 0 0 0 []
          (MatrixMaterialization.rowMajor f ++ output)) := by
  intro activity f
  exact MatrixTableWriter.write_rowMajor P wStart wCtl (bankW g r K mX mY xs ys) mX mY
    (Tent g hg hs r hq ξ K mX mY xs ys) (entryF g hg hs r hq ξ K mX mY xs ys) f
    (fun x y => by simp only [entryF, dif_pos (And.intro x.isLt y.isLt)]; rfl)
    (entry_runs g hg hp hs r hq ξ hfix K mX mY xs ys) output

end

#print axioms ιWf_injective
#print axioms transport
#print axioms entry_runs
#print axioms table_run

end Paper2.WEntry
