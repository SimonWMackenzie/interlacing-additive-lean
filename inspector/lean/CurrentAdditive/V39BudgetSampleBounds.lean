import CurrentAdditive.V39BudgetPrintedLaw
import Paper2.EncodedSelectedOutput

set_option autoImplicit false

/-! Rank compression and its single rounding loss for the same complete
current sample. The final source consumer supplies the proved profile/rank
for the actual matrix; these scalar/profile-premise lemmas are reusable joins. -/

namespace CurrentAdditive.V39BudgetSampleBounds
noncomputable section
open Paper2 Workspace.Types.CommComplexity
open EthInapproximability.CurrentPaper
open EncodedCommunication
open V39RecursiveGenerator V39RecursiveTable V38OneStep V39BudgetPrintedLaw

set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

variable (n p q₁ q₂ s w Q : ℕ)
variable [NeZero n] [NeZero p] [NeZero q₁] [NeZero q₂]
  [NeZero s] [NeZero (4*s)] [NeZero (s-3)] [NeZero w] [NeZero Q]

def sampledMatrix (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (hs : 4 ≤ s) (hq₁ : q₁=s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.blockLength n p q₂ s w Q N) N) :
    Fin m → Fin m → Bool :=
  let z:=V39PhysicalSample.sampleAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits
  sampleMatrix (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k) z.1 z.2

theorem every_tape_upper
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (hs : 4 ≤ s) (hq₁ : q₁=s-2) (k m N B : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (hupper : D (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k) ≤ B)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.blockLength n p q₂ s w Q N) N) :
    D (sampledMatrix n p q₁ q₂ s w Q activity hs hq₁ k m N hN bits)≤B := by
  exact sample_D_le_of_le (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k)
    (V39PhysicalSample.sampleAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits).1
    (V39PhysicalSample.sampleAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits).2 hupper

theorem tableInstance_matrix
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s)) (k m B : ℕ)
    (z : (Fin m → Row n p q₁ q₂ s w Q k) × (Fin m → Column n p q₁ q₂ s w Q k)) :
    ProtocolVerifier.tableGame (tableInstance activity k m B z).rows
      (tableInstance activity k m B z).cols (tableInstance activity k m B z).table =
      sampleMatrix (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k) z.1 z.2 := by
  change ProtocolVerifier.tableGame m m (sampledTable activity k m z).bits=_
  rw [EncodedSelectedOutput.tableGame_eq_matrix]
  funext i j
  exact sampledTable_entry activity k m z i j

theorem outputWord_rowMajor
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s)) (k m B : ℕ)
    (z : (Fin m → Row n p q₁ q₂ s w Q k) × (Fin m → Column n p q₁ q₂ s w Q k)) :
    outputWord activity k m B z = encodeInstance
      ⟨m,m,B,MatrixMaterialization.rowMajor (sampleMatrix (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k) z.1 z.2)⟩ := by
  unfold outputWord tableInstance
  congr 2
  change List.ofFn (YaoMaterialization.linearEntries _) = List.ofFn _
  congr 1
  funext i
  exact evaluate_eq_matrix activity k _ _

theorem ideal_failure
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (k r H : ℕ) (hH : 1 ≤ H)
    (hrank : (RankLeaves.realMatrix (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k)).rank≤r)
    (hrobust : ∀ U V, (3/5:ℝ)≤(laws n p q₁ q₂ s w Q k).1.toFiniteLaw.prob (·∈U) →
      (3/5:ℝ)≤(laws n p q₁ q₂ s w Q k).2.toFiniteLaw.prob (·∈V) →
      H≤Compression.restrictionD (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k) U V) :
    let m:=V38RankCount.squareDrawsV38 r H
    (sampleLaw n p q₁ q₂ s w Q k m).toFiniteLaw.prob
      (fun z => D (sampleMatrix (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k) z.1 z.2)<H)<(1:ℝ)/100 :=
  row_first_compression _ _ _ r H hH hrank hrobust

theorem rounded_failure
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (hs : 4 ≤ s) (hq₁ : q₁=s-2) (k r H N : ℕ) (hH : 1 ≤ H)
    (hrank : (RankLeaves.realMatrix (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k)).rank≤r)
    (hrobust : ∀ U V, (3/5:ℝ)≤(laws n p q₁ q₂ s w Q k).1.toFiniteLaw.prob (·∈U) →
      (3/5:ℝ)≤(laws n p q₁ q₂ s w Q k).2.toFiniteLaw.prob (·∈V) →
      H≤Compression.restrictionD (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k) U V)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k (V38RankCount.squareDrawsV38 r H)≤N) :
    (RoundedDraw.bitBlocksLaw (V39PhysicalSample.blockLength n p q₂ s w Q N) N).prob
      (fun bits => D (sampledMatrix n p q₁ q₂ s w Q activity hs hq₁ k
        (V38RankCount.squareDrawsV38 r H) N hN bits)<H)<(3:ℝ)/200 := by
  have hid:=ideal_failure n p q₁ q₂ s w Q activity k r H hH hrank hrobust
  have ht:=V39PhysicalSample.budget_labels_event_error_200 n p q₁ q₂ s w Q hs hq₁
    k (V38RankCount.squareDrawsV38 r H) N hN
    (fun z => D (sampleMatrix (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k) z.1 z.2)<H)
  have hb:=(abs_le.mp ht).2
  change _ < _
  change _ < _ at hid
  change _ ≤ _ at hb
  dsimp only [sampledMatrix]
  linarith

theorem rounded_exact_probability
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (hs : 4 ≤ s) (hq₁ : q₁=s-2) (k r H N : ℕ) (hH : 1 ≤ H)
    (hrank : (RankLeaves.realMatrix (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k)).rank≤r)
    (hrobust : ∀ U V, (3/5:ℝ)≤(laws n p q₁ q₂ s w Q k).1.toFiniteLaw.prob (·∈U) →
      (3/5:ℝ)≤(laws n p q₁ q₂ s w Q k).2.toFiniteLaw.prob (·∈V) →
      H≤Compression.restrictionD (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k) U V)
    (hupper : D (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k)≤H)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k (V38RankCount.squareDrawsV38 r H)≤N) :
    (49:ℝ)/50 ≤
      (RoundedDraw.bitBlocksLaw (V39PhysicalSample.blockLength n p q₂ s w Q N) N).prob
        (fun bits => D (sampledMatrix n p q₁ q₂ s w Q activity hs hq₁ k
          (V38RankCount.squareDrawsV38 r H) N hN bits)=H) := by
  let μ:=RoundedDraw.bitBlocksLaw (V39PhysicalSample.blockLength n p q₂ s w Q N) N
  let bad:=fun bits => D (sampledMatrix n p q₁ q₂ s w Q activity hs hq₁ k
    (V38RankCount.squareDrawsV38 r H) N hN bits)<H
  have hf:=rounded_failure n p q₁ q₂ s w Q activity hs hq₁ k r H N hH hrank hrobust hN
  have hc:=prob_not μ bad
  have he:(fun bits => ¬bad bits)=(fun bits => D (sampledMatrix n p q₁ q₂ s w Q
      activity hs hq₁ k (V38RankCount.squareDrawsV38 r H) N hN bits)=H) := by
    funext bits
    apply propext
    have hu:=every_tape_upper n p q₁ q₂ s w Q activity hs hq₁ k
      (V38RankCount.squareDrawsV38 r H) N H hN hupper bits
    dsimp only [bad]
    omega
  rw [he] at hc
  change μ.prob bad < _ at hf
  change _ ≤ μ.prob _
  linarith

/-- An event of the literal encoded word, evaluated by its actual decoder. -/
def ExactWordCost (H : ℕ) (word : List Bool) : Prop :=
  ∃ out, decodeInstance word=some out ∧
    D (ProtocolVerifier.tableGame out.rows out.cols out.table)=H

theorem exactWordCost_outputWord
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s)) (k m B H : ℕ)
    (hm : 0 < m)
    (z : (Fin m → Row n p q₁ q₂ s w Q k) × (Fin m → Column n p q₁ q₂ s w Q k)) :
    ExactWordCost H (outputWord activity k m B z) ↔
      D (sampleMatrix (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k) z.1 z.2)=H := by
  constructor
  · rintro ⟨out,hd,hcost⟩
    rw [decode_outputWord activity k m B hm z] at hd
    cases Option.some.inj hd
    simpa only [tableInstance_matrix] using hcost
  · intro hcost
    exact ⟨tableInstance activity k m B z,decode_outputWord activity k m B hm z,
      by simpa only [tableInstance_matrix] using hcost⟩

theorem printed_yes_membership
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (hs : 4 ≤ s) (hq₁ : q₁=s-2) (k m N B : ℕ) (hm : 0 < m)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (hupper : D (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k)≤B)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.blockLength n p q₂ s w Q N) N) :
    printedWord n p q₁ q₂ s w Q activity hs hq₁ k m B N hN bits ∈ EncodedCommunication.Language := by
  let z:=V39PhysicalSample.sampleAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits
  refine ⟨tableInstance activity k m B z,decode_outputWord activity k m B hm z,?_⟩
  change D (ProtocolVerifier.tableGame (tableInstance activity k m B z).rows
    (tableInstance activity k m B z).cols (tableInstance activity k m B z).table)≤B
  rw [tableInstance_matrix]
  exact sample_D_le_of_le _ _ _ hupper

theorem printed_exact_probability
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (hs : 4 ≤ s) (hq₁ : q₁=s-2) (k r B H N : ℕ) (hH : 1 ≤ H)
    (hrank : (RankLeaves.realMatrix (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k)).rank≤r)
    (hrobust : ∀ U V, (3/5:ℝ)≤(laws n p q₁ q₂ s w Q k).1.toFiniteLaw.prob (·∈U) →
      (3/5:ℝ)≤(laws n p q₁ q₂ s w Q k).2.toFiniteLaw.prob (·∈V) →
      H≤Compression.restrictionD (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k) U V)
    (hupper : D (V39RecursiveTable.matrix (p₀ := p) (q₁ := q₁) (w := w) (Q := Q) activity k)≤H)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k (V38RankCount.squareDrawsV38 r H)≤N) :
    (49:ℝ)/50 ≤
      (RoundedDraw.bitBlocksLaw (V39PhysicalSample.blockLength n p q₂ s w Q N) N).prob
        (fun bits => ExactWordCost H
          (printedWord n p q₁ q₂ s w Q activity hs hq₁ k
            (V38RankCount.squareDrawsV38 r H) B N hN bits)) := by
  have hm:0<V38RankCount.squareDrawsV38 r H := by
    unfold V38RankCount.squareDrawsV38
    positivity
  simp_rw [printedWord,exactWordCost_outputWord n p q₁ q₂ s w Q activity k _ B H hm]
  exact rounded_exact_probability n p q₁ q₂ s w Q activity hs hq₁ k r H N
    hH hrank hrobust hupper hN

#print axioms outputWord_rowMajor
#print axioms ideal_failure
#print axioms rounded_failure
#print axioms rounded_exact_probability
#print axioms printed_yes_membership
#print axioms printed_exact_probability
end
end CurrentAdditive.V39BudgetSampleBounds
