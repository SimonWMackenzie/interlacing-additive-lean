import CurrentAdditive.GenericSupportRequestSelect

/-! The template branch uses the same fixed selector with support syntax for
arbitrary compact indexed bases. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.GenericSupportTemplateLookup

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource Paper2.RecursiveRequestCodeShape
open Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries
open Paper2.GenericSupportCarrier Paper2.CompactSupportShape
open Paper2.GenericSupportPropagation
open Paper2.OutputSkipper (Shape)

theorem template_run {nr nc n s q₁ q₂ w Q L : ℕ}
    (hr : nr ≤ 2 ^ L) (hc : nc ≤ 2 ^ L) (hs : 0 < s) (k : ℕ)
    (o : Paper2.SourceMatrix.OuterColumn q₁ q₂ s
      (Column (Fin nr) (Fin nc) (Paper2.SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k))
    (z : Paper2.SourceMatrix.Template q₁ q₂
      (Row (Fin nr) (Fin nc) (Paper2.SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k)) :
    let C := codecs nr nc n s q₁ q₂ w Q k
    let c := supportCodes nr nc n s q₁ q₂ w Q L k
    let E : Code := .append (.ticket q₁) c.1
    let ent := prodCodec (finCodec q₁) C.1
    let cs := List.ofFn (fun a => ent.encode (z a))
    let rs := List.ofFn (fun b => C.2.encode (o.2 b))
    ∃ t ≤ Paper2.RequestSelect.clock
        ((outerColumnCodec q₁ q₂ s C.2).encode o)
        o.1.val (z o.1).1.val E c.2 cs rs, ∃ v,
      ((advance Paper2.RequestSelect.program)^[t])
        (⟨some Paper2.RequestSelect.startLabel,
          Paper2.RequestSelect.startControl,
          Paper2.RequestSelect.mk [] []
            (Paper2.RequestSelect.vec ((piCodec ent q₂).encode z)
              ((outerColumnCodec q₁ q₂ s C.2).encode o)
              (encodeCode E) (encodeCode c.2) [] [] [])⟩ :
          TM2.Cfg (fun _ : Paper2.RequestSelect.Stack => Bool) _ _) =
        ⟨none, v, Paper2.RequestSelect.mk
          (C.1.encode (z o.1).2)
          (C.2.encode (Paper2.SourceMatrix.head o.2 (z o.1).1))
          (Paper2.RequestSelect.vec ((piCodec ent q₂).encode z)
            ((outerColumnCodec q₁ q₂ s C.2).encode o)
            (encodeCode E) (encodeCode c.2)
            (List.replicate o.1.val true)
            ((piCodec C.2 (q₁ + s + 1)).encode o.2)
            (List.replicate (z o.1).1.val true))⟩ := by
  intro C c E ent cs rs
  have h := carrier_support (n := n) (s := s) (q₁ := q₁)
    (q₂ := q₂) (w := w) (Q := Q) hr hc k
  have hE_full := ticket_pair q₁ c.1 C.1 h.1
  have hG_full := h.2
  have hshape := support_recursive_shape n s q₁ q₂ w Q L k hs
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
    rw [Paper2.CodeSampleOutputDecoder.piCodec_encode_tupleWord,
      Paper2.SuccessCodec.tupleWord_eq_flatten]
  have hR : (piCodec C.2 (q₁ + s + 1)).encode o.2 = rs.flatten := by
    rw [Paper2.CodeSampleOutputDecoder.piCodec_encode_tupleWord,
      Paper2.SuccessCodec.tupleWord_eq_flatten]
  have hY : (outerColumnCodec q₁ q₂ s C.2).encode o =
      List.replicate o.1.val true ++ false :: rs.flatten := by
    change (finCodec q₂).encode o.1 ++
      (piCodec C.2 (q₁ + s + 1)).encode o.2 = _
    rw [hR]
    simp [finCodec]
  have hj : o.1.val < cs.length := by simp [cs]
  have hb : (z o.1).1.val < q₁ + s + 1 := by
    have := (z o.1).1.isLt
    omega
  have hi : (z o.1).1.val < rs.length := by simp [rs]; omega
  have hget : cs.getD o.1.val [] = ent.encode (z o.1) := by
    simp [cs, List.getD_eq_getElem?_getD]
  have hentry : cs.getD o.1.val [] = List.replicate (z o.1).1.val true ++
      false :: C.1.encode (z o.1).2 := by
    rw [hget]
    change (finCodec q₁).encode (z o.1).1 ++ C.1.encode (z o.1).2 = _
    simp [finCodec]
  have hcol : rs.getD (z o.1).1.val [] =
      C.2.encode (Paper2.SourceMatrix.head o.2 (z o.1).1) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hb]
    rfl
  obtain ⟨t, ht, v, hrun⟩ := Paper2.RequestSelect.select_generic
    E c.2 hE hshape.2 cs rs hcs hrs o.1.val
    (z o.1).1.val hj hi _ hentry
  rw [hcol] at hrun
  rw [hX, hY, hR]
  exact ⟨t, ht, v, hrun⟩

#print axioms template_run

end Paper2.GenericSupportTemplateLookup
