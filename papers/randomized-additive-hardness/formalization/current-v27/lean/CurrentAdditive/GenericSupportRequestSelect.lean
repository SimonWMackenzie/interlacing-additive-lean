import CurrentAdditive.GenericSupportCarrier
import Paper2.RequestSelect

/-! A literal request-selection run for arbitrary indexed rational bases.
The machine reads a shape-safe support code, while sampling may use the
separate, exactly weighted rational code. Every requested indexed label has
the same compact encoding in both roles. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.GenericSupportRequestSelect

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource Paper2.RecursiveRequestCodeShape
open Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries
open Paper2.GenericSupportCarrier Paper2.CompactSupportShape
open Paper2.OutputSkipper (Shape)

theorem select_run {nr nc n s q₁ q₂ w Q L : ℕ}
    (hr : nr ≤ 2 ^ L) (hc : nc ≤ 2 ^ L) (hs : 0 < s) (k : ℕ)
    (x : Row (Fin nr) (Fin nc) (Paper2.SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q (k + 1))
    (y : Column (Fin nr) (Fin nc) (Paper2.SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q (k + 1)) :
    let C := codecs nr nc n s q₁ q₂ w Q k
    let D := codecs nr nc n s q₁ q₂ w Q (k + 1)
    let c := supportCodes nr nc n s q₁ q₂ w Q L k
    let E : Code := .append (.ticket w) (taggedCode q₁ q₂ s c.2)
    let G : Code := graphRowsCode (V := Fin n) q₁ q₂ s c.1
    let entry := prodCodec (finCodec w) (taggedColumnCodec q₁ q₂ s C.2)
    let rrow := rawRowCodec q₁ q₂ s C.1 (defaultItemCodec n s)
    let cs := List.ofFn (fun j => entry.encode (x j))
    let rs := List.ofFn (fun i => rrow.encode (y.2 i))
    ∃ t ≤ Paper2.RequestSelect.clock (D.2.encode y) y.1.val
        (x y.1).1.val E G cs rs, ∃ v,
      ((advance Paper2.RequestSelect.program)^[t])
        (⟨some Paper2.RequestSelect.startLabel,
          Paper2.RequestSelect.startControl,
          Paper2.RequestSelect.mk [] []
            (Paper2.RequestSelect.vec (D.1.encode x) (D.2.encode y)
              (encodeCode E) (encodeCode G) [] [] [])⟩ :
          TM2.Cfg (fun _ : Paper2.RequestSelect.Stack => Bool) _ _) =
        ⟨none, v, Paper2.RequestSelect.mk
          ((taggedColumnCodec q₁ q₂ s C.2).encode (x y.1).2)
          (rrow.encode (y.2 (x y.1).1))
          (Paper2.RequestSelect.vec (D.1.encode x) (D.2.encode y)
            (encodeCode E) (encodeCode G) (List.replicate y.1.val true)
            ((piCodec rrow w).encode y.2)
            (List.replicate (x y.1).1.val true))⟩ := by
  intro C D c E G entry rrow cs rs
  obtain ⟨hE_full, hG_full⟩ := request_subcodes_support
    (n := n) (s := s) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hr hc k
  have hshape := support_recursive_shape n s q₁ q₂ w Q L k hs
  have hE : Shape E := ⟨trivial, Paper2.OutputSkipper.shape_tagged q₁ q₂ s _ hshape.2⟩
  have hG : Shape G := Paper2.OutputSkipper.shape_graphRows n q₁ q₂ s hs _ hshape.1
  have hcs : ∀ u ∈ cs, Produces (meaning E) u := by
    intro u hu
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
    exact hE_full _
  have hrs : ∀ u ∈ rs, Produces (meaning G) u := by
    intro u hu
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact hG_full _
  have hX : D.1.encode x = cs.flatten := by
    change (piCodec entry Q).encode x = _
    rw [Paper2.CodeSampleOutputDecoder.piCodec_encode_tupleWord,
      Paper2.SuccessCodec.tupleWord_eq_flatten]
  have hR : (piCodec rrow w).encode y.2 = rs.flatten := by
    rw [Paper2.CodeSampleOutputDecoder.piCodec_encode_tupleWord,
      Paper2.SuccessCodec.tupleWord_eq_flatten]
  have hY : D.2.encode y = List.replicate y.1.val true ++ false :: rs.flatten := by
    change (finCodec Q).encode y.1 ++ (piCodec rrow w).encode y.2 = _
    rw [hR]
    simp [finCodec]
  have hj : y.1.val < cs.length := by simp [cs]
  have hi : (x y.1).1.val < rs.length := by simp [rs]
  have hget : cs.getD y.1.val [] = entry.encode (x y.1) := by
    simp [cs, List.getD_eq_getElem?_getD]
  have hentry : cs.getD y.1.val [] = List.replicate (x y.1).1.val true ++
      false :: (taggedColumnCodec q₁ q₂ s C.2).encode (x y.1).2 := by
    rw [hget]
    change (finCodec w).encode (x y.1).1 ++
      (taggedColumnCodec q₁ q₂ s C.2).encode (x y.1).2 = _
    simp [finCodec]
  have hrow : rs.getD (x y.1).1.val [] = rrow.encode (y.2 (x y.1).1) := by
    simp [rs, List.getD_eq_getElem?_getD]
  obtain ⟨t, ht, v, h⟩ := Paper2.RequestSelect.select_generic
    E G hE hG cs rs hcs hrs y.1.val (x y.1).1.val hj hi _ hentry
  rw [hrow] at h
  rw [hX, hY, hR]
  exact ⟨t, ht, v, h⟩

#print axioms select_run

end Paper2.GenericSupportRequestSelect
