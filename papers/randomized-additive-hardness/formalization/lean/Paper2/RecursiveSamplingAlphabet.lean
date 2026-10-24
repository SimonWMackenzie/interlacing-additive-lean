import Paper2.RecursiveSamplingGraph

/-!
# Elementary alphabet bounds for the actual source generators

Frozen v12 Appendix D, `app:implementation`, the public elementary-draw
bound used for capped rejection sampling.  The cap below bounds individual
requests in the program tree, not the cardinality of the output carrier.
In particular, taking a long independent tuple does not enlarge a single
elementary alphabet.  The constants 256 and 512 are the actual protected
mixture ticket denominators.

This supplies alphabet bounds for the already-defined generators.  It does
not itself prove recursive machine-time bounds or the final capped-law
comparison.
-/

namespace Paper2.RecursiveSampling

open SourceMatrix RecursiveSamplingProgram RecursiveSamplingLaws

variable {X Y V A : Type*} {q₁ q₂ s : ℕ}

theorem maxAlphabet_outer_le [NeZero q₂] (p : Program Y) (M : ℕ)
    (hq : q₂ ≤ M) (hp : Program.maxAlphabet p ≤ M) :
    Program.maxAlphabet (outer (q₁ := q₁) (q₂ := q₂) (s := s) p) ≤ M := by
  apply (maxAlphabet_prod_le _ _).trans
  apply max_le
  · simpa only [uniform, Program.maxAlphabet_uniform] using hq
  · exact (maxAlphabet_iid_le p (q₁ + s + 1)).trans hp

theorem maxAlphabet_raw_le [NeZero q₂] (p : Program Y) (M : ℕ)
    (hq : q₂ ≤ M) (hp : Program.maxAlphabet p ≤ M) :
    Program.maxAlphabet (raw (q₁ := q₁) (q₂ := q₂) (s := s) p) ≤ M := by
  apply (maxAlphabet_prod_le _ _).trans
  apply max_le
  · exact (maxAlphabet_iid_le p (s + 1)).trans hp
  · exact (maxAlphabet_iid_le _ s).trans (maxAlphabet_outer_le p M hq hp)

theorem maxAlphabet_fixedTail_le [NeZero q₂] (p : Program Y) (M : ℕ)
    (hq : q₂ ≤ M) (hp : Program.maxAlphabet p ≤ M) :
    Program.maxAlphabet (fixedTail (q₁ := q₁) (q₂ := q₂) (s := s) p) ≤ M :=
  (maxAlphabet_iid_le _ s).trans (maxAlphabet_outer_le p M hq hp)

theorem maxAlphabet_tagged_le [NeZero q₂] (p : Program Y) (M : ℕ)
    (ht : 256 ≤ M) (hq : q₂ ≤ M) (hp : Program.maxAlphabet p ≤ M) :
    Program.maxAlphabet (tagged (q₁ := q₁) (q₂ := q₂) (s := s) p) ≤ M := by
  rw [tagged, Program.maxAlphabet_draw]
  apply max_le ht
  apply Finset.sup_le
  intro t _
  split_ifs <;> rw [Program.maxAlphabet_map]
  · exact maxAlphabet_raw_le p M hq hp
  · exact maxAlphabet_fixedTail_le p M hq hp
  · exact maxAlphabet_outer_le p M hq hp

theorem maxAlphabet_template_le [NeZero q₁] (p : Program X) (M : ℕ)
    (hq : q₁ ≤ M) (hp : Program.maxAlphabet p ≤ M) :
    Program.maxAlphabet (template (q₁ := q₁) (q₂ := q₂) p) ≤ M := by
  apply (maxAlphabet_iid_le _ q₂).trans
  apply (maxAlphabet_prod_le _ _).trans
  apply max_le
  · simpa only [uniform, Program.maxAlphabet_uniform] using hq
  · exact hp

theorem maxAlphabet_templateRow_le [NeZero q₁] [NeZero s]
    (p : Program X) (M : ℕ) (hq : q₁ ≤ M) (hs : s ≤ M)
    (hp : Program.maxAlphabet p ≤ M) :
    Program.maxAlphabet (templateRow (q₁ := q₁) (q₂ := q₂) (s := s) p) ≤ M := by
  apply (maxAlphabet_prod_le _ _).trans
  apply max_le
  · simpa only [uniform, Program.maxAlphabet_uniform] using hs
  · exact maxAlphabet_template_le p M hq hp

theorem maxAlphabet_itemRow_le (labels : Program V) (p : Program X) (M : ℕ)
    (hl : Program.maxAlphabet labels ≤ M) (hp : Program.maxAlphabet p ≤ M) :
    Program.maxAlphabet (itemRow labels p) ≤ M :=
  (maxAlphabet_prod_le _ _).trans (max_le hl hp)

theorem maxAlphabet_rows_le [NeZero q₁] [NeZero s]
    (vertices : Program V) (auxiliaries : Program A) (p : Program X) (M : ℕ)
    (ht : 512 ≤ M) (hq : q₁ ≤ M) (hs : s ≤ M)
    (hv : Program.maxAlphabet vertices ≤ M)
    (ha : Program.maxAlphabet auxiliaries ≤ M) (hp : Program.maxAlphabet p ≤ M) :
    Program.maxAlphabet
      (rows (q₁ := q₁) (q₂ := q₂) (s := s) vertices auxiliaries p) ≤ M := by
  rw [rows, Program.maxAlphabet_draw]
  apply max_le ht
  apply Finset.sup_le
  intro t _
  split_ifs <;> rw [Program.maxAlphabet_map]
  · exact maxAlphabet_templateRow_le p M hq hs hp
  · exact maxAlphabet_itemRow_le vertices p M hv hp
  · exact maxAlphabet_itemRow_le auxiliaries p M ha hp

section Graph

variable [Fintype V] [Nonempty V]

theorem maxAlphabet_vertex (order : Fin (Fintype.card V) ≃ V) :
    Program.maxAlphabet (vertex order) = Fintype.card V := by
  simp only [vertex, Program.maxAlphabet_map, Program.maxAlphabet_uniform]

theorem maxAlphabet_vertexLabels_le (order : Fin (Fintype.card V) ≃ V)
    (hs : 4 ≤ s) (M : ℕ) (hg : 4 * s ≤ M) (hv : Fintype.card V ≤ M) :
    Program.maxAlphabet (vertexLabels order hs) ≤ M := by
  apply (maxAlphabet_prod_le _ _).trans
  apply max_le
  · simpa only [Program.maxAlphabet_uniform] using hg
  · simpa only [maxAlphabet_vertex] using hv

end Graph

theorem maxAlphabet_auxiliaryLabels_le (s : ℕ) (hs : 4 ≤ s) (M : ℕ)
    (hg : 4 * s ≤ M) : Program.maxAlphabet (auxiliaryLabels s hs) ≤ M := by
  apply (maxAlphabet_prod_le _ _).trans
  apply max_le
  · simpa only [Program.maxAlphabet_uniform] using hg
  · simp only [Program.maxAlphabet_uniform]
    omega

/-- One common public cap suffices for all requests in an actual graph-source
row. Neither `q₂` nor any tuple-carrier cardinality appears in this cap. -/
theorem maxAlphabet_graphRows_le [Fintype V] [Nonempty V] [NeZero q₁]
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s) (p : Program X) (M : ℕ)
    (ht : 512 ≤ M) (hq : q₁ ≤ M) (hg : 4 * s ≤ M)
    (hv : Fintype.card V ≤ M) (hp : Program.maxAlphabet p ≤ M) :
    Program.maxAlphabet (graphRows (q₁ := q₁) (q₂ := q₂) order hs p) ≤ M := by
  letI : NeZero s := ⟨by omega⟩
  simp only [graphRows, Program.maxAlphabet_map]
  exact maxAlphabet_rows_le _ _ p M ht hq (by omega)
    (maxAlphabet_vertexLabels_le order hs M hg hv)
    (maxAlphabet_auxiliaryLabels_le s hs M hg) hp

#print axioms maxAlphabet_tagged_le
#print axioms maxAlphabet_graphRows_le

end Paper2.RecursiveSampling
