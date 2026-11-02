import Paper2.RequestSelect

/-! The selection half of one physical `RecursiveEntries.request` step on the
actual encoded level-`k+1` labels (`defaultCarrierCodecs … (k+1)`), for every
row `x` and column `y` of that level (not only sampled ones: the code-driven
skipping premise comes from `FullSupport.subcodes_full`). The machine halts
with the literal level-`k` words
`taggedColumnCodec.encode (x y.1).2` and `rawRowCodec.encode (y.2 (x y.1).1)`:
exactly the two arguments of `baseRequest activity (y.2 (x y.1).1)
(forgetTag (ξ k) (x y.1).2)` in `RecursiveEntries.request`, in encoded form. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.RequestSelectActual

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveRequestCodeShape
open RecursiveLabelCodecScratch RecursiveEntries
open OutputSkipper (Shape)

theorem select_run {n p s q₁ q₂ w Q : ℕ} [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w]
    [NeZero Q] (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q (k + 1)) :
    let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
    let D := defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)
    let c := seedRecursiveCodes n p s q₁ q₂ w Q k
    let E : Code := .append (.ticket w) (taggedCode q₁ q₂ s c.2)
    let G : Code := graphRowsCode (V := Fin n) q₁ q₂ s c.1
    let entry := prodCodec (finCodec w) (taggedColumnCodec q₁ q₂ s C.2)
    let rrow := rawRowCodec q₁ q₂ s C.1 (defaultItemCodec n s)
    let cs := List.ofFn (fun j => entry.encode (x j))
    let rs := List.ofFn (fun i => rrow.encode (y.2 i))
    ∃ t ≤ RequestSelect.clock (D.2.encode y) y.1.val (x y.1).1.val E G cs rs, ∃ v,
      ((advance RequestSelect.program)^[t])
        (⟨some RequestSelect.startLabel, RequestSelect.startControl,
          RequestSelect.mk [] [] (RequestSelect.vec (D.1.encode x) (D.2.encode y)
            (encodeCode E) (encodeCode G) [] [] [])⟩ :
          TM2.Cfg (fun _ : RequestSelect.Stack => Bool) _ _) =
        ⟨none, v, RequestSelect.mk ((taggedColumnCodec q₁ q₂ s C.2).encode (x y.1).2)
          (rrow.encode (y.2 (x y.1).1))
          (RequestSelect.vec (D.1.encode x) (D.2.encode y) (encodeCode E) (encodeCode G)
            (List.replicate y.1.val true) ((piCodec rrow w).encode y.2)
            (List.replicate (x y.1).1.val true))⟩ := by
  intro C D c E G entry rrow cs rs
  obtain ⟨hE_full, -, -, -, -, hG_full⟩ := FullSupport.subcodes_full (n := n) (p := p)
    (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k
  have hshape := OutputSkipper.shape_seedRecursiveCodes n p s q₁ q₂ w Q k (by omega)
  have hE : Shape E := ⟨trivial, OutputSkipper.shape_tagged q₁ q₂ s _ hshape.2⟩
  have hG : Shape G := OutputSkipper.shape_graphRows n q₁ q₂ s (by omega) _ hshape.1
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
    rw [CodeSampleOutputDecoder.piCodec_encode_tupleWord, SuccessCodec.tupleWord_eq_flatten]
  have hR : (piCodec rrow w).encode y.2 = rs.flatten := by
    rw [CodeSampleOutputDecoder.piCodec_encode_tupleWord, SuccessCodec.tupleWord_eq_flatten]
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
    change (finCodec w).encode (x y.1).1 ++ (taggedColumnCodec q₁ q₂ s C.2).encode (x y.1).2 = _
    simp [finCodec]
  have hrow : rs.getD (x y.1).1.val [] = rrow.encode (y.2 (x y.1).1) := by
    simp [rs, List.getD_eq_getElem?_getD]
  obtain ⟨t, ht, v, h⟩ := RequestSelect.select_generic E G hE hG cs rs hcs hrs y.1.val
    (x y.1).1.val hj hi _ hentry
  rw [hrow] at h
  rw [hX, hY, hR]
  exact ⟨t, ht, v, h⟩

end

#print axioms select_run

end Paper2.RequestSelectActual
