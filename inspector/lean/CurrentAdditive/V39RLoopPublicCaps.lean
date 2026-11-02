import CurrentAdditive.V39EntryCurrent
import Paper2.SC2Master
import Paper2.SC2Nav
import Paper2.GeneratorSize

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39RLoop
noncomputable section
open Paper2
open EthInapproximability.CurrentPaper
open GeneratorCode GeneratorSerialization GeneratorSource RecursiveLabelCodecScratch RecursiveEntries

def syntaxCap (n p s q₁ q₂ w Q K : ℕ) : ℕ :=
  (GeneratorSize.scale n p s q₁ q₂ w Q)^(9*(K+2))

def labelBase (n p s : ℕ) : ℕ :=
  max 1 (max (piCodec boolCodec p).maxLen
    (max (finCodec p).maxLen (defaultItemCodec n s).maxLen))

def labelCap (n p s q₁ q₂ w Q K : ℕ) : ℕ :=
  labelBase n p s * (labelStepCap s q₁ q₂ w Q)^(K+1)

def scalarSum (g : EncodedGraph.Graph) (p s q₁ q₂ w Q r K : ℕ) : ℕ :=
  g.vertices+p+4*s+q₁+q₂+w+Q+g.edges.length+r+K+16

/-- A formula in public counts and encoded graph length. It neither enumerates
the input pairs nor takes a maximum over their execution times. -/
def publicScale (g : EncodedGraph.Graph) (p s q₁ q₂ w Q r K : ℕ) : ℕ :=
  1048576 + 3*scalarSum g p s q₁ q₂ w Q r K + 3*((EncodedGraph.encode g).length+1) +
    2*g.edges.length*g.vertices + 6*syntaxCap g.vertices p s q₁ q₂ w Q K +
    6*labelCap g.vertices p s q₁ q₂ w Q K

theorem syntaxCap_le (n p s q₁ q₂ w Q K i : ℕ) (hi : i ≤ K+1) :
    codeSize (seedRecursiveCodes n p s q₁ q₂ w Q i).1 +
      codeSize (seedRecursiveCodes n p s q₁ q₂ w Q i).2 + 1 ≤
        syntaxCap n p s q₁ q₂ w Q K := by
  have h := GeneratorSize.seed_total_le_scale n p s q₁ q₂ w Q i
  have hb := GeneratorSize.scale_ge n p s q₁ q₂ w Q
  exact h.trans (Nat.pow_le_pow_right (by omega) (by omega))

theorem labelCap_le (n p s q₁ q₂ w Q K i : ℕ) (hi : i ≤ K+1) :
    (defaultCarrierCodecs n p s q₁ q₂ w Q i).1.maxLen ≤ labelCap n p s q₁ q₂ w Q K ∧
    (defaultCarrierCodecs n p s q₁ q₂ w Q i).2.maxLen ≤ labelCap n p s q₁ q₂ w Q K := by
  have h := carrierCodecs_maxLen_le s q₁ q₂ w Q (piCodec boolCodec p) (finCodec p)
    (defaultItemCodec n s) i
  have ht : 1 ≤ labelStepCap s q₁ q₂ w Q := by unfold labelStepCap; omega
  have hp := Nat.mul_le_mul_left (labelBase n p s)
    (Nat.pow_le_pow_right (by omega) hi :
      (labelStepCap s q₁ q₂ w Q)^i ≤ (labelStepCap s q₁ q₂ w Q)^(K+1))
  exact ⟨h.1.trans hp,h.2.trans hp⟩

theorem publicScale_caps (g : EncodedGraph.Graph) (p s q₁ q₂ w Q r K k : ℕ)
    (hk : k ≤ K) :
    let X := publicScale g p s q₁ q₂ w Q r K
    1048576 ≤ X ∧
    g.vertices+p+4*s+q₁+q₂+w+Q+g.edges.length+r+k+16 ≤ X ∧
    codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k+1)).1 +
      codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k+1)).2+q₁+8 ≤ X ∧
    (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k+1)).1.maxLen+
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k+1)).2.maxLen ≤ X ∧
    (EncodedGraph.encode g).length+1 ≤ X ∧ 2*g.edges.length*g.vertices ≤ X := by
  intro X
  have hc := syntaxCap_le g.vertices p s q₁ q₂ w Q K (k+1) (by omega)
  obtain ⟨hr,hl⟩ := labelCap_le g.vertices p s q₁ q₂ w Q K (k+1) (by omega)
  dsimp [X,publicScale,scalarSum]
  omega

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

theorem master_public_bound (g : EncodedGraph.Graph) (r K : ℕ) :
    (∑ z : SrcX.JX, (master (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r z).length) ≤
      2*syntaxCap g.vertices p s q₁ q₂ w Q K + (EncodedGraph.encode g).length +
        scalarSum g p s q₁ q₂ w Q r K := by
  have hm := SuccessClock2.master_sum_le (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r
  have hb := SuccessClock2.WXb_sum_le (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r
  have h0 := syntaxCap_le g.vertices p s q₁ q₂ w Q K 0 (by omega)
  have h1 := syntaxCap_le g.vertices p s q₁ q₂ w Q K 1 (by omega)
  obtain ⟨_,_,ho,_,_,_,_⟩ := SuccessClock.derived_le (n:=g.vertices) (s:=s) (q₁:=q₁)
    (q₂:=q₂) (NeZero.one_le : 1≤w) (NeZero.one_le : 1≤Q) (copies p .bit) (.ticket p) 0
  change codeSize (outerCode q₁ q₂ s (seedRecursiveCodes g.vertices p s q₁ q₂ w Q 0).2) ≤
    codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q 1).1 at ho
  change (∑ z : SrcX.JX, (master (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r z).length) ≤ _ at hm
  dsimp only [scalarSum]
  omega

theorem entryBank_public_bound (g : EncodedGraph.Graph) [NeZero g.vertices] (r K k : ℕ)
    (hk : k ≤ K)
    (x : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q (k+1))
    (y : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q (k+1)) :
    let xx := (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q (k+1)).1 x
    let yy := (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q (k+1)).2 y
    (∑ z : TemplateStepX.JT, ((Sum.elim (TemplateStepX.W0f k xx yy)
      (E0k (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r k)) z).length) ≤
        publicScale g p s q₁ q₂ w Q r K := by
  intro xx yy
  have he := SuccessClock2.E0k_sum_le (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r k
  have hj := SuccessClock2.W0f_sum_le k xx yy
  have hm := master_public_bound (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r K
  have hc := syntaxCap_le g.vertices p s q₁ q₂ w Q K (k+1) (by omega)
  obtain ⟨hr,hl⟩ := labelCap_le g.vertices p s q₁ q₂ w Q K (k+1) (by omega)
  rw [Fintype.sum_sum_type]
  change (∑ z : TemplateStep.J, (TemplateStepX.W0f k xx yy z).length) +
    (∑ z : SrcX.JX, (E0k (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r k z).length) ≤ _
  change (∑ z : SrcX.JX, (E0k (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r k z).length) ≤
    (∑ z : SrcX.JX, (master (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r z).length)+k at he
  dsimp [publicScale,scalarSum] at hm ⊢
  omega

end
#print axioms publicScale_caps
#print axioms master_public_bound
#print axioms entryBank_public_bound
end CurrentAdditive.V39RLoop
