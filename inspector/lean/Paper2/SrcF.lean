import Paper2.ItemOperands
import Paper2.DefaultWordSeed
import Paper2.CanonicalDefaultWord
import Paper2.CanonicalDefaultSource

/-! Unit 3, segment (1): the source arm for the FIXED-TAIL tag at the
canonical widths (`p = LookupSeed.width L`, `s = width L`,
`q₁ = width L - 2`, `q₂ = outerWidth L`) with the canonical default tails
`CanonicalDefaultSource.canonicalDefaultTails` (the tail family of
`codedCanonicalEntry`).

Value (`fixed_source_value`): for EVERY activity map, item and fixed-tail
tuple, the encoded source column of the fixed-tail column is the default
column word `(words p s q₁ q₂ w Q k).2` (every canonical default tail entry
has the same encoding, the admitted `canonical_tail_encoded`); so the source
position is not needed on this arm.

Machine (`srcF_run`): ONE program on `JF = DefaultWordLoop.LB ⊕ Fin 4`:
`ItemOperands.program` strips the item from the raw source-row word (the row
cell keeps `C.1.encode u`), then the admitted `DefaultWordLoop.wordsProgram`
(lifted by `Sum.inl`) produces `words … k` from unary `p, q₁, s, Q, w` and
`k` counter marks. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.SrcF

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries SourceMatrix
open BitMachineRawSequence (leftLabel)
open Paper2.CanonicalDefaultWordScratch (words)

theorem fixed_source_value (L n w Q : ℕ) (hn : 0 < n) (hw : 0 < w) (hQ : 0 < Q) (k : ℕ)
    [NeZero (SourceProfileParameters.width L)]
    (activity : SourceConstruction.Items (SourceProfileParameters.width L) (Fin n) →
      Fin (SourceProfileParameters.outerWidth L) → Option (Fin (SourceProfileParameters.width L)))
    (i : SourceConstruction.Items (SourceProfileParameters.width L) (Fin n))
    (js : Fin (SourceProfileParameters.width L) →
      OuterColumn (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L)
        (SourceProfileParameters.width L)
        (Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
          (SourceConstruction.Items (SourceProfileParameters.width L) (Fin n))
          (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
          (SourceProfileParameters.outerWidth L) w Q k)) :
    (defaultCarrierCodecs n (LookupSeed.width L) (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L) w Q k).2.encode
      (sourceColumn activity i
        (forgetTag (CanonicalDefaultSource.canonicalDefaultTails L n w Q hn hw hQ k)
          (.fixedTail js))) =
    (words (LookupSeed.width L) (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L) w Q k).2 :=
  CanonicalDefaultWordScratch.canonical_tail_encoded L n w Q hn hw hQ k
    (sourcePosition activity i
      (forgetTag (CanonicalDefaultSource.canonicalDefaultTails L n w Q hn hw hQ k)
        (.fixedTail js)))

abbrev JF := DefaultWordLoop.LB ⊕ Fin 4

def ιL : DefaultWordLoop.LB ↪ JF := ⟨Sum.inl, Sum.inl_injective⟩

def srcF : JF := .inr 0
def aF : JF := .inr 1
def kF : JF := .inr 2
def xF : JF := .inr 3

def F1 := ItemOperands.program srcF aF kF xF
def F2 := fun l => stackStmt ιL (DefaultWordLoop.wordsProgram l)

abbrev d1 := ((none : Option Bool), (((none : Option Bool), (none : Option Bool)),
  (none : Option Bool)))
abbrev d2 := (DefaultWordLoop.seedCtl, ((none : Option Bool), DefaultWordLoop.bodyCtl))

/-- The fixed-tail source arm: one program. -/
def armF := BitMachineRawSequence.program F1 F2
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel ())))))) d1 d2

theorem liftF {Kk L V : Type*} [DecidableEq Kk] (ι : Kk ↪ JF)
    (P : L → TM2.Stmt (fun _ : Kk => Bool) L V)
    (W : JF → List Bool) (S T : Kk → List Bool) (hS : ∀ k, S k = W (ι k)) (l : L) (v v' : V)
    (t : ℕ)
    (hrun : ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) =
      ⟨none, v', T⟩) :
    ((advance (fun l => stackStmt ι (P l)))^[t])
        (⟨some l, v, W⟩ : TM2.Cfg (fun _ : JF => Bool) L V) =
      ⟨none, v', bank ι W T⟩ := by
  have hs := BitMachineStackRun.run ι W P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) t
  rw [hrun] at hs
  simp only [stackCfg] at hs
  rwa [bank_eq_self ι W S hS] at hs

theorem bank_ιL (X : DefaultWordLoop.LB → List Bool) (Y : Fin 4 → List Bool)
    (T : DefaultWordLoop.LB → List Bool) :
    bank ιL (Sum.elim X Y) T = Sum.elim T Y := by
  funext j
  cases j with
  | inl j => exact bank_at ιL _ T j
  | inr j => exact bank_outside ιL _ T (.inr j) (by rintro ⟨k, hk⟩; cases hk)

theorem srcF_run {n p s q₁ q₂ w Q : ℕ} (k : ℕ)
    (i : SourceConstruction.Items s (Fin n))
    (uu : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k) :
    let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
    ∃ t ≤ (1 + ((i.1.val + 1) + 1 + (CanonicalEndpointRankBridge.itemValue i.2 + 1) + 2) + 1) +
        ((1 + (p * 5 + 1) + (2 * p + 2) + (p + 1) + 2 + 1 + 5) +
          (k * (DefaultWordLoop.levelBound p s q₁ q₂ w Q k + 2) + 1) + 1) + 1, ∃ v,
      ((advance armF)^[t])
        (⟨some (leftLabel (leftLabel ())), (d1, d2),
          (Sum.elim (DefaultWordLoop.entry p q₁ s Q w k)
            ![(prodCodec (defaultItemCodec n s) C.1).encode (i, uu), [], [], []] :
            JF → List Bool)⟩ : TM2.Cfg (fun _ : JF => Bool) _ _) =
        ⟨none, v, Sum.elim (DefaultWordLoop.S q₁ s Q w (words p s q₁ q₂ w Q k).1
            (words p s q₁ q₂ w Q k).2 [])
          ![C.1.encode uu, List.replicate i.1.val true, [i.2.isRight],
            CanonicalEndpointRankMachine.unaryWord (CanonicalEndpointRankBridge.itemValue i.2)]⟩ := by
  intro C
  obtain ⟨t1, ht1, v1, l1⟩ := ItemOperands.item_operands (n := n) (p := p) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) k i uu srcF aF kF xF
    (by simp [srcF, aF]) (by simp [srcF, kF]) (by simp [srcF, xF]) (by simp [aF, kF])
    (by simp [aF, xF]) (by simp [kF, xF])
    (Sum.elim (DefaultWordLoop.entry p q₁ s Q w k)
      ![(prodCodec (defaultItemCodec n s) C.1).encode (i, uu), [], [], []]) rfl rfl rfl rfl
  have hY : ∀ (y0 y1 y2 y3 : List Bool),
      Function.update (Function.update (Function.update (Function.update
        (![(prodCodec (defaultItemCodec n s) C.1).encode (i, uu), [], [], []] : Fin 4 → List Bool)
          0 y0) 1 y1) 2 y2) 3 y3 = ![y0, y1, y2, y3] := by
    intro y0 y1 y2 y3
    funext j; fin_cases j <;> rfl
  simp only [srcF, aF, kF, xF, Sum.update_elim_inr, hY] at l1
  obtain ⟨t2, ht2, v2, l2⟩ := DefaultWordLoop.default_words_run p s q₁ q₂ w Q k
  have l2' := liftF ιL DefaultWordLoop.wordsProgram
    (Sum.elim (DefaultWordLoop.entry p q₁ s Q w k)
      ![C.1.encode uu, List.replicate i.1.val true, [i.2.isRight],
        CanonicalEndpointRankMachine.unaryWord (CanonicalEndpointRankBridge.itemValue i.2)])
    _ _ (fun _ => rfl) _ _ _ _ l2
  rw [bank_ιL] at l2'
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs F1 F2 (leftLabel ())
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel ())))))) d1 v1 d2 v2
    _ _ _ _ _ l1 l2'
  exact ⟨u1, by omega, _, q1⟩

#print axioms fixed_source_value
#print axioms bank_ιL
#print axioms srcF_run

end

end Paper2.SrcF
