import CurrentAdditive.V39RLoopPublicClock

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39RLoop
noncomputable section
open Paper2 Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper
open GeneratorCode GeneratorSerialization GeneratorSource RecursiveLabelCodecScratch RecursiveEntries

attribute [local irreducible] bodyCoefficient V39RLoopGrowth.pushBound

/-- A public scalar clock, uniform over every complete current label pair. -/
def publicCoreClock (g : EncodedGraph.Graph) (p s q₁ q₂ w Q r K : ℕ) : ℕ :=
  (bodyCoefficient+10000)*(publicScale g p s q₁ q₂ w Q r K)^11

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

theorem coreClock_public (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hs : 4 ≤ s) (r : ℕ) (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K : ℕ) (x0 : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (y0 : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    coreClock g hg hs r hq ξ K x0 y0 ≤ publicCoreClock g p s q₁ q₂ w Q r K := by
  let X := publicScale g p s q₁ q₂ w Q r K
  have hX := (publicScale_caps g p s q₁ q₂ w Q r K K (le_refl K)).1
  have hX1 : 1 ≤ X := by omega
  have hXp : X ≤ X^11 := by simpa using (Nat.pow_le_pow_right hX1 (show 1 ≤ 11 by omega))
  have hK : K ≤ X := by dsimp [X,publicScale,scalarSum]; omega
  have hp : p ≤ X := by dsimp [X,publicScale,scalarSum]; omega
  have hcK := syntaxCap_le g.vertices p s q₁ q₂ w Q K K (by omega)
  have hc0 := syntaxCap_le g.vertices p s q₁ q₂ w Q K 0 (by omega)
  obtain ⟨hrK,hlK⟩ := labelCap_le g.vertices p s q₁ q₂ w Q K K (by omega)
  obtain ⟨hr0,hl0⟩ := labelCap_le g.vertices p s q₁ q₂ w Q K 0 (by omega)
  have hcKX : codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q K).1+
      codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q K).2 ≤ X := by
    dsimp [X,publicScale]; omega
  have hc0X : codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q 0).1+
      codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q 0).2 ≤ X := by
    dsimp [X,publicScale]; omega
  have hrKX : (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q K).1.maxLen ≤ X := by
    dsimp [X,publicScale]; omega
  have hlKX : (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q K).2.maxLen ≤ X := by
    dsimp [X,publicScale]; omega
  have hr0X : (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q 0).1.maxLen ≤ X := by
    dsimp [X,publicScale]; omega
  have hl0X : (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q 0).2.maxLen ≤ X := by
    dsimp [X,publicScale]; omega
  have hloop := loopBd_public g hg hs r hq ξ K x0 y0
  have hprod := Nat.mul_le_mul hK hloop
  have hnorm : X*(bodyCoefficient*X^10) = bodyCoefficient*X^11 := by ring
  rw [hnorm] at hprod
  have hloopFull : K*(loopBd g hg hs r hq ξ K x0 y0+2) ≤ bodyCoefficient*X^11+2*X := by
    rw [Nat.mul_add]; omega
  unfold coreClock
  extract_lets x y activity C c sd C0 c0 Lin Lout
  have hxr := C.1.length_le x
  have hyr := C.2.length_le y
  have hsxr := C0.1.length_le sd.1
  have hsyr := C0.2.length_le sd.2
  have hcrK : C.1.maxLen ≤ X := hrKX
  have hccK : C.2.maxLen ≤ X := hlKX
  have hcr0 : C0.1.maxLen ≤ X := hr0X
  have hcc0 : C0.2.maxLen ≤ X := hl0X
  have hck : codeSize c.1+codeSize c.2 ≤ X := hcKX
  have hc0' : codeSize c0.1+codeSize c0.2 ≤ X := hc0X
  have hLin : Lin ≤ 4*X := by
    dsimp only [Lin]
    simp only [encodeCode_length]
    omega
  have hLout : Lout ≤ 4*X := by
    dsimp only [Lout]
    simp only [encodeCode_length]
    omega
  change _ ≤ (bodyCoefficient+10000)*X^11
  rw [Nat.add_mul]
  omega

/-- Fixed current evaluator, literal current input words, actual current
matrix bit, and exact restoration of every other prepared bank. -/
theorem core_run_public (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K : ℕ)
    (x : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (y : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    let c := seedRecursiveCodes g.vertices p s q₁ q₂ w Q K
    let activity := V39EdgeSourceFront.edgeActivity g hg (by omega) r hq
    ∃ t ≤ publicCoreClock g p s q₁ q₂ w Q r K, ∃ v,
      ((advance coreProg)^[t])
        (⟨some coreStart,coreCtl,
          readyE (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r
            (V39PhysicalSelect.rowWord K x) (V39PhysicalSelect.columnWord K y)
            (encodeCode c.1) (encodeCode c.2) K []⟩ :
          TM2.Cfg (fun _ : JE => Bool) _ _) =
        ⟨none,v,readyE (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r
            (V39PhysicalSelect.rowWord K x) (V39PhysicalSelect.columnWord K y)
            (encodeCode c.1) (encodeCode c.2) K
            [V39RecursiveTable.matrix activity K x y]⟩ := by
  obtain ⟨t,ht,v,hrun⟩ := core_run_current g hg hp hs r hq ξ K x y
  exact ⟨t,ht.trans (coreClock_public g hg hs r hq ξ K x y),v,hrun⟩

end
#print axioms core_run_public
#print axioms coreClock_public
end CurrentAdditive.V39RLoop
