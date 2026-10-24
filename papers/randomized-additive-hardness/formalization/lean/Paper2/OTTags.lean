import Paper2.OTGen

/-! Unit 3, segment (1), outer-token equality for the remaining tags.

* Unrestricted tag: `OTGen.fullG` with the production
  `FetchIndexed.rowProgram` (skip the `s+1` tail words of the raw column
  word with the column code `col_k`, then `i` outer words with the outer code,
  capture outer word `i`; `row_fetch`), on the raw column word after the tag
  bit: `unrestricted_eq_run`.
* Diagonal tag: ONE program `diagProg` = production `RawRowSplit.readU` of the
  single outer word's token (the tag bits already popped), then one pushed
  `true` on the equality cell (`diag_run`); for a diagonal column every outer
  coordinate is the same word, so the source equality holds by definition
  (`diag_eq`), and the residual word is exactly the diagonal tail tuple word
  consumed by the Codex-checked `SourceTailFetch.diagonal_source_tail_fetch`.
* The link to `SourceMatrix.sourcePosition`: the produced bit is the `heq`
  premise of the checked `SourcePos.sourcePosition_eq` for
  `Z = forgetTag ξ₀ zt` in each tag (`fixed_heq`, `unrestricted_heq`,
  `diag_eq`). -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.OTTags

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource RecursiveRequestCodeShape
open RecursiveLabelCodecScratch RecursiveEntries SourceMatrix
open OutputSkipper
open BitMachineRawSequence (leftLabel)
open Paper2.OTOps (u)
open Paper2.OTBody
open Paper2.OTLoop (accL tokF eq_iff)

variable {n p s q₁ q₂ w Q : ℕ}
  [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The body of outer word `i` after its token (`[]` off range). -/
def restF (k : ℕ)
    (js : Fin s → OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (i : ℕ) : List Bool :=
  if h : i < s then
    (piCodec (defaultCarrierCodecs n p s q₁ q₂ w Q k).2 (q₁ + s + 1)).encode (js ⟨i, h⟩).2
  else []

/-- The exact `row_fetch` clock of outer word `i`. -/
def TfU (k : ℕ)
    (Z : RawColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (O : List Bool) (i : ℕ) : ℕ :=
  let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
  let col := (seedRecursiveCodes n p s q₁ q₂ w Q k).2
  let oc := outerColumnCodec q₁ q₂ s C.2
  FetchIndexed.rowBound col (outerCode q₁ q₂ s col)
    (List.ofFn (fun a : Fin (s + 1) => C.2.encode (Z.1 a)))
    (List.ofFn (fun a : Fin s => oc.encode (Z.2 a))) i O

theorem tokF_zero (k : ℕ)
    (js : Fin s → OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)) :
    tokF k js 0 = (js 0).1.val := by
  have hs0 : 0 < s := NeZero.pos s
  have h0 : (⟨0, hs0⟩ : Fin s) = 0 := Fin.ext (by simp)
  simp only [tokF, dif_pos hs0, h0]

/-- Unrestricted tag: the outer-token equality bit and unary `(Z.2 0).1` by
ONE fixed program (`OTGen.fullG` over the production `rowProgram`) on the raw
column word. -/
theorem unrestricted_eq_run (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ)
    (Z : RawColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (O : List Bool) :
    let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
    let col := (seedRecursiveCodes n p s q₁ q₂ w Q k).2
    let fw := (rawColumnCodec q₁ q₂ s C.2).encode Z ++ O
    ∃ t ≤ OTGen.fullGBound s (TfU k Z O) (tokF k Z.2) (restF k Z.2), ∃ v,
      ((advance (OTGen.fullG FetchIndexed.rowProgram FetchIndexed.rowStart
          FetchIndexed.rowControl))^[t])
        (⟨some (OTGen.fullGStart FetchIndexed.rowProgram FetchIndexed.rowStart
            FetchIndexed.rowControl), OTGen.fullGCtl FetchIndexed.rowControl,
          BB [] fw (encodeCode col) (encodeCode (outerCode q₁ q₂ s col)) (u (s + 1))
            [] [] [] [] [] [] [] (u s)⟩ :
          TM2.Cfg (fun _ : B => Bool) _ _) =
        ⟨none, v, BB [] fw (encodeCode col) (encodeCode (outerCode q₁ q₂ s col)) (u (s + 1))
          (u s) (u (Z.2 0).1.val) [] [] [] [] [decide (∀ pp, (Z.2 pp).1 = (Z.2 0).1)] (u s)⟩ := by
  intro C col fw
  let oc := outerColumnCodec q₁ q₂ s C.2
  let cs := List.ofFn (fun a : Fin (s + 1) => C.2.encode (Z.1 a))
  let rs := List.ofFn (fun a : Fin s => oc.encode (Z.2 a))
  have hcol : Shape col :=
    (OutputSkipper.shape_seedRecursiveCodes n p s q₁ q₂ w Q k (by omega)).2
  have hrow : Shape (outerCode q₁ q₂ s col) := OutputSkipper.shape_outer q₁ q₂ s _ hcol
  have hcs : ∀ c ∈ cs, Produces (meaning col) c := by
    intro c hc
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hc
    exact (FullSupport.codes_full (n := n) (p := p) (s := s)
      (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k).2 (Z.1 a)
  have hout := (FullSupport.subcodes_full (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hp hs k).2.2.2.1
  have hrs : ∀ r ∈ rs, Produces (meaning (outerCode q₁ q₂ s col)) r := by
    intro r hr
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hr
    exact hout (Z.2 a)
  have hfw : cs.flatten ++ rs.flatten ++ O = fw := by
    have e1 : (piCodec C.2 (s + 1)).encode Z.1 = cs.flatten := by
      rw [CodeSampleOutputDecoder.piCodec_encode_tupleWord, SuccessCodec.tupleWord_eq_flatten]
    have e2 : (piCodec oc s).encode Z.2 = rs.flatten := by
      rw [CodeSampleOutputDecoder.piCodec_encode_tupleWord, SuccessCodec.tupleWord_eq_flatten]
    have e3 : (rawColumnCodec q₁ q₂ s C.2).encode Z =
        (piCodec C.2 (s + 1)).encode Z.1 ++ (piCodec oc s).encode Z.2 := rfl
    simp only [fw, e3, e1, e2, List.append_assoc]
  have hlen : List.replicate cs.length true = u (s + 1) := by simp [cs, u]
  have hF : ∀ i < s, OTGen.FetchRun FetchIndexed.rowProgram FetchIndexed.rowStart
      FetchIndexed.rowControl fw (encodeCode col) (encodeCode (outerCode q₁ q₂ s col))
      (u (s + 1)) i (tokF k Z.2 i) (restF k Z.2 i) (TfU k Z O i) := by
    intro i hi
    have hi' : i < rs.length := by simpa [rs] using hi
    obtain ⟨t, ht, v, hr⟩ := FetchIndexed.row_fetch col (outerCode q₁ q₂ s col) hcol hrow cs rs
      hcs hrs O i hi' _ _ rfl rfl
    refine ⟨t, ht, v, ?_⟩
    have hw : rs.getD i [] = List.replicate (tokF k Z.2 i) true ++ false :: restF k Z.2 i := by
      rw [List.getD_eq_getElem _ _ hi']
      simp only [rs, List.getElem_ofFn, tokF, restF, dif_pos hi]
      exact OuterTokenFetch.outer_word_token k (Z.2 ⟨i, hi⟩)
    rw [hw, hfw, hlen] at hr
    exact hr
  obtain ⟨t, ht, v, hr⟩ := OTGen.fullG_run FetchIndexed.rowProgram FetchIndexed.rowStart
    FetchIndexed.rowControl s fw (encodeCode col) (encodeCode (outerCode q₁ q₂ s col))
    (u (s + 1)) (TfU k Z O) (tokF k Z.2) (restF k Z.2) hF (NeZero.pos s)
  refine ⟨t, ht, v, ?_⟩
  rw [hr, tokF_zero, eq_iff]

/-- Fixed-tail tag: the checked `OTLoop.fixed_eq_run` bit is the source
equality of `forgetTag ξ₀ (.fixedTail js)`. -/
theorem fixed_heq (ξ₀ : Tail s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (js : Fin s → OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)) :
    (decide (∀ pp, (js pp).1 = (js 0).1) = true ↔
      ∀ pp, ((forgetTag ξ₀ (.fixedTail js)).2 pp).1 = ((forgetTag ξ₀ (.fixedTail js)).2 0).1) ∧
    ((forgetTag ξ₀ (.fixedTail js)).2 0).1.val = (js 0).1.val := by
  exact ⟨decide_eq_true_iff, rfl⟩

theorem unrestricted_heq (ξ₀ : Tail s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (Z : RawColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)) :
    (decide (∀ pp, (Z.2 pp).1 = (Z.2 0).1) = true ↔
      ∀ pp, ((forgetTag ξ₀ (.unrestricted Z)).2 pp).1 =
        ((forgetTag ξ₀ (.unrestricted Z)).2 0).1) ∧
    ((forgetTag ξ₀ (.unrestricted Z)).2 0).1.val = (Z.2 0).1.val := by
  exact ⟨decide_eq_true_iff, rfl⟩

omit [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] in
theorem diag_eq (ξ₀ : Tail s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (j : OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)) :
    (true = true ↔
      ∀ pp, ((forgetTag ξ₀ (.diagonal j)).2 pp).1 = ((forgetTag ξ₀ (.diagonal j)).2 0).1) ∧
    ((forgetTag ξ₀ (.diagonal j)).2 0).1.val = j.1.val :=
  ⟨⟨fun _ _ => rfl, fun _ => rfl⟩, rfl⟩

/-! ### Diagonal program (generic cells) -/

section Diag

variable {J : Type*} [DecidableEq J]

def diagProg (src a e : J) :=
  BitMachineRawSequence.program (RawRowSplit.readU src a) (OTOps.inc e) () ob ob

theorem diag_run (src a e : J) (h1 : src ≠ a) (h2 : src ≠ e) (h3 : a ≠ e)
    (j : ℕ) (rest : List Bool) (S : J → List Bool)
    (hS : S src = List.replicate j true ++ false :: rest) (ha : S a = []) (he : S e = []) :
    ∃ t ≤ (j + 1) + 1 + 1,
      ((advance (diagProg src a e))^[t])
        (⟨some (leftLabel ()), (ob, ob), S⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, (ob, ob), Function.update (Function.update (Function.update S src rest) a
          (List.replicate j true)) e [true]⟩ := by
  have r1 := RawRowSplit.readU_run src a h1 j rest [] S ob hS ha
  rw [List.append_nil] at r1
  have r2 := OTOps.inc_run e (Function.update (Function.update S src rest) a
    (List.replicate j true)) ob
  have hE : Function.update (Function.update S src rest) a (List.replicate j true) e = [] := by
    rw [Function.update_of_ne (Ne.symm h3), Function.update_of_ne (Ne.symm h2), he]
  rw [hE] at r2
  obtain ⟨t, ht, q⟩ := BitMachineRawSequence.runs (RawRowSplit.readU src a) (OTOps.inc e)
    () () ob (some false) ob ob _ _ _ _ _ r1 r2
  exact ⟨t, ht, q⟩

/-- The diagonal tagged word after the two tag bits: token, then the tail
tuple word (the input form of `SourceTailFetch.diagonal_source_tail_fetch`). -/
theorem diag_word (k : ℕ)
    (j : OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)) :
    (taggedColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2).encode
        (.diagonal j) =
      true :: true :: (List.replicate j.1.val true ++ false ::
        (List.ofFn (fun a : Fin (q₁ + s + 1) =>
          (defaultCarrierCodecs n p s q₁ q₂ w Q k).2.encode (j.2 a))).flatten) := by
  have e1 := OuterTokenFetch.outer_word_token (n := n) (p := p) (s := s) (q₁ := q₁)
    (q₂ := q₂) (w := w) (Q := Q) k j
  have e2 : (piCodec (defaultCarrierCodecs n p s q₁ q₂ w Q k).2 (q₁ + s + 1)).encode j.2 =
      (List.ofFn (fun a : Fin (q₁ + s + 1) =>
          (defaultCarrierCodecs n p s q₁ q₂ w Q k).2.encode (j.2 a))).flatten := by
    rw [CodeSampleOutputDecoder.piCodec_encode_tupleWord, SuccessCodec.tupleWord_eq_flatten]
  rw [← e2, ← e1]
  rfl

/-- The fixed-tail tagged word after the two tag bits is the fixed-tail tuple
word consumed by `OTLoop.fixed_eq_run`; the unrestricted word after its tag bit
is the raw column word consumed by `unrestricted_eq_run`. -/
theorem fixed_word (k : ℕ)
    (js : Fin s → OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)) :
    (taggedColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2).encode
        (.fixedTail js) =
      true :: false :: (piCodec (outerColumnCodec q₁ q₂ s
        (defaultCarrierCodecs n p s q₁ q₂ w Q k).2) s).encode js := rfl

theorem unrestricted_word (k : ℕ)
    (Z : RawColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)) :
    (taggedColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2).encode
        (.unrestricted Z) =
      false :: (rawColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2).encode Z :=
  rfl

end Diag

#print axioms tokF_zero
#print axioms unrestricted_eq_run
#print axioms fixed_heq
#print axioms unrestricted_heq
#print axioms diag_eq
#print axioms diag_run
#print axioms diag_word
#print axioms fixed_word
#print axioms unrestricted_word

end

end Paper2.OTTags
