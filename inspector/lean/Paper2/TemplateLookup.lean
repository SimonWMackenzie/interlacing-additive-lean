import Paper2.RequestSelect

/-! Segment 2, item (2): the template case of `SourceMatrix.baseRequest`,
given the encoded outer column `o = Z.2 p` and the encoded template `z`:

`baseRequest activity (.inl (p, z)) Z = ((z (Z.2 p).1).2, head (Z.2 p).2 (z (Z.2 p).1).1)`.

It is the same fixed program `RequestSelect.program` (copy, read unary, fetch,
read unary, fetch), now with the template entry code `append (ticket q₁) row_k`
over the template word and the level-`k` column code `col_k` over the outer
column's `Y`-tuple. No default tail and no activity value is used in this
case (the tail enters only `Z.1`, which the template case never reads). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.TemplateLookup

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveRequestCodeShape
open RecursiveLabelCodecScratch RecursiveEntries
open OutputSkipper (Shape)

theorem template_run {n p s q₁ q₂ w Q : ℕ} [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w]
    [NeZero Q] (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ)
    (o : SourceMatrix.OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (z : SourceMatrix.Template q₁ q₂
      (Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)) :
    let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
    let c := seedRecursiveCodes n p s q₁ q₂ w Q k
    let E : Code := .append (.ticket q₁) c.1
    let ent := prodCodec (finCodec q₁) C.1
    let cs := List.ofFn (fun a => ent.encode (z a))
    let rs := List.ofFn (fun b => C.2.encode (o.2 b))
    ∃ t ≤ RequestSelect.clock ((outerColumnCodec q₁ q₂ s C.2).encode o) o.1.val (z o.1).1.val
        E c.2 cs rs, ∃ v,
      ((advance RequestSelect.program)^[t])
        (⟨some RequestSelect.startLabel, RequestSelect.startControl,
          RequestSelect.mk [] [] (RequestSelect.vec ((piCodec ent q₂).encode z)
            ((outerColumnCodec q₁ q₂ s C.2).encode o) (encodeCode E) (encodeCode c.2)
            [] [] [])⟩ :
          TM2.Cfg (fun _ : RequestSelect.Stack => Bool) _ _) =
        ⟨none, v, RequestSelect.mk (C.1.encode (z o.1).2)
          (C.2.encode (SourceMatrix.head o.2 (z o.1).1))
          (RequestSelect.vec ((piCodec ent q₂).encode z)
            ((outerColumnCodec q₁ q₂ s C.2).encode o) (encodeCode E) (encodeCode c.2)
            (List.replicate o.1.val true) ((piCodec C.2 (q₁ + s + 1)).encode o.2)
            (List.replicate (z o.1).1.val true))⟩ := by
  intro C c E ent cs rs
  have hr := FullSupport.row_exact (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hp hs k
  obtain ⟨fr, -⟩ := FullSupport.seed_programs_full (n := n) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hp hs k
  have hE_full := FullSupport.code_full (ticketProd_exact q₁ _ _ _ hr)
    (FullSupport.full_prod (FullSupport.full_uniform' q₁) fr)
  obtain ⟨-, hG_full⟩ := FullSupport.codes_full (n := n) (p := p) (s := s) (q₁ := q₁)
    (q₂ := q₂) (w := w) (Q := Q) hp hs k
  have hshape := OutputSkipper.shape_seedRecursiveCodes n p s q₁ q₂ w Q k (by omega)
  have hE : Shape E := ⟨trivial, hshape.1⟩
  have hcs : ∀ u ∈ cs, Produces (meaning E) u := by
    intro u hu
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hu
    exact hE_full _
  have hrs : ∀ u ∈ rs, Produces (meaning c.2) u := by
    intro u hu
    obtain ⟨b, rfl⟩ := List.mem_ofFn.mp hu
    exact hG_full _
  have hX : (piCodec ent q₂).encode z = cs.flatten := by
    rw [CodeSampleOutputDecoder.piCodec_encode_tupleWord, SuccessCodec.tupleWord_eq_flatten]
  have hR : (piCodec C.2 (q₁ + s + 1)).encode o.2 = rs.flatten := by
    rw [CodeSampleOutputDecoder.piCodec_encode_tupleWord, SuccessCodec.tupleWord_eq_flatten]
  have hY : (outerColumnCodec q₁ q₂ s C.2).encode o =
      List.replicate o.1.val true ++ false :: rs.flatten := by
    change (finCodec q₂).encode o.1 ++ (piCodec C.2 (q₁ + s + 1)).encode o.2 = _
    rw [hR]
    simp [finCodec]
  have hj : o.1.val < cs.length := by simp [cs]
  have hb : (z o.1).1.val < q₁ + s + 1 := by have := (z o.1).1.isLt; omega
  have hi : (z o.1).1.val < rs.length := by simp [rs]; omega
  have hget : cs.getD o.1.val [] = ent.encode (z o.1) := by
    simp [cs, List.getD_eq_getElem?_getD]
  have hentry : cs.getD o.1.val [] = List.replicate (z o.1).1.val true ++
      false :: C.1.encode (z o.1).2 := by
    rw [hget]
    change (finCodec q₁).encode (z o.1).1 ++ C.1.encode (z o.1).2 = _
    simp [finCodec]
  have hcol : rs.getD (z o.1).1.val [] = C.2.encode (SourceMatrix.head o.2 (z o.1).1) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hb]
    rfl
  obtain ⟨t, ht, v, h⟩ := RequestSelect.select_generic E c.2 hE hshape.2 cs rs hcs hrs
    o.1.val (z o.1).1.val hj hi _ hentry
  rw [hcol] at h
  rw [hX, hY, hR]
  exact ⟨t, ht, v, h⟩

/-- The outputs are literally the encoded template-case `baseRequest` pair,
for any raw column `Z` whose `p`-th outer column is `o`. -/
theorem template_is_baseRequest {X Y I : Type*} {q₁ q₂ s : ℕ} [NeZero s]
    (activity : I → Fin q₂ → Option (Fin s)) (pp : Fin s)
    (z : SourceMatrix.Template q₁ q₂ X) (Z : SourceMatrix.RawColumn q₁ q₂ s Y) :
    SourceMatrix.baseRequest activity (.inl (pp, z)) Z =
      ((z (Z.2 pp).1).2, SourceMatrix.head (Z.2 pp).2 (z (Z.2 pp).1).1) := rfl

end

#print axioms template_run
#print axioms template_is_baseRequest

end Paper2.TemplateLookup
