import CurrentAdditive.GenericSupportTemplateLookup
import Paper2.SourceTailFetch

/-! Physical tail fetch for the source-row branch of a recursive request,
using shape-safe support syntax with arbitrary compact indexed base labels. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Paper2.GenericSupportTailFetch

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource Paper2.RecursiveRequestCodeShape
open Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries
open Paper2.SourceMatrix Paper2.OutputSkipper
open Paper2.GenericSupportCarrier Paper2.CompactSupportShape

variable {nr nc n s q₁ q₂ w Q L : ℕ} [NeZero s]

theorem unrestricted_source_tail_fetch
    (hr : nr ≤ 2 ^ L) (hc : nc ≤ 2 ^ L) (hs : 0 < s) (k : ℕ)
    (i : Paper2.SourceConstruction.Items s (Fin n))
    (activity : Paper2.SourceConstruction.Items s (Fin n) →
      Fin q₂ → Option (Fin s))
    (Z : RawColumn q₁ q₂ s
      (Column (Fin nr) (Fin nc) (Paper2.SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k))
    (O rc my : List Bool) :
    let C := codecs nr nc n s q₁ q₂ w Q k
    let col := (supportCodes nr nc n s q₁ q₂ w Q L k).2
    let cs := List.ofFn (fun a : Fin (s + 1) => C.2.encode (Z.1 a))
    let pos := (sourcePosition activity i Z).val
    ∃ t ≤ Paper2.FetchIndexed.colBound col cs pos O, ∃ v,
      ((advance Paper2.FetchIndexed.colProgram)^[t])
        (⟨some Paper2.FetchIndexed.colStart,
          Paper2.FetchIndexed.colControl,
          Paper2.FetchIndexed.FB [] [] [] []
            (cs.flatten ++ O) (encodeCode col) rc my
            (List.replicate pos true)⟩ :
          TM2.Cfg (fun _ : Paper2.FetchIndexed.Stack => Bool) _ _) =
        ⟨none, v, Paper2.FetchIndexed.FB [] [] []
          (C.2.encode (sourceColumn activity i Z))
          (cs.flatten ++ O) (encodeCode col) rc my
          (List.replicate pos true)⟩ := by
  dsimp only
  let C := codecs nr nc n s q₁ q₂ w Q k
  let col := (supportCodes nr nc n s q₁ q₂ w Q L k).2
  let cs := List.ofFn (fun a : Fin (s + 1) => C.2.encode (Z.1 a))
  let pos := (sourcePosition activity i Z).val
  have hshape : Shape col :=
    (support_recursive_shape n s q₁ q₂ w Q L k hs).2
  have hprod : ∀ c ∈ cs, Produces (meaning col) c := by
    intro c hc'
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hc'
    exact (carrier_support (n := n) (s := s) (q₁ := q₁)
      (q₂ := q₂) (w := w) (Q := Q) hr hc k).2 (Z.1 a)
  have hpos : pos < cs.length := by
    simpa [pos, cs] using (sourcePosition activity i Z).isLt
  obtain ⟨t, ht, v, hrun⟩ := Paper2.FetchIndexed.col_fetch
    col hshape cs hprod O pos hpos (encodeCode col) rc my rfl
  refine ⟨t, ht, v, ?_⟩
  have hword : cs.getD pos [] = C.2.encode (sourceColumn activity i Z) := by
    rw [List.getD_eq_getElem _ _ hpos]
    change (List.ofFn (fun a : Fin (s + 1) => C.2.encode (Z.1 a)))[pos] =
      C.2.encode (Z.1 (sourcePosition activity i Z))
    rw [List.getElem_ofFn]
  simpa only [hword] using hrun

theorem diagonal_source_tail_fetch
    (hr : nr ≤ 2 ^ L) (hc : nc ≤ 2 ^ L) (hs : 0 < s) (k : ℕ)
    (i : Paper2.SourceConstruction.Items s (Fin n))
    (activity : Paper2.SourceConstruction.Items s (Fin n) →
      Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s (Column (Fin nr) (Fin nc)
      (Paper2.SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (j : OuterColumn q₁ q₂ s (Column (Fin nr) (Fin nc)
      (Paper2.SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (O rc my : List Bool) :
    let C := codecs nr nc n s q₁ q₂ w Q k
    let col := (supportCodes nr nc n s q₁ q₂ w Q L k).2
    let cs := List.ofFn (fun a : Fin (q₁ + s + 1) => C.2.encode (j.2 a))
    let pos := q₁ +
      (sourcePosition activity i (forgetTag ξ₀ (.diagonal j))).val
    ∃ t ≤ Paper2.FetchIndexed.colBound col cs pos O, ∃ v,
      ((advance Paper2.FetchIndexed.colProgram)^[t])
        (⟨some Paper2.FetchIndexed.colStart,
          Paper2.FetchIndexed.colControl,
          Paper2.FetchIndexed.FB [] [] [] []
            (cs.flatten ++ O) (encodeCode col) rc my
            (List.replicate pos true)⟩ :
          TM2.Cfg (fun _ : Paper2.FetchIndexed.Stack => Bool) _ _) =
        ⟨none, v, Paper2.FetchIndexed.FB [] [] []
          (C.2.encode (sourceColumn activity i
            (forgetTag ξ₀ (.diagonal j))))
          (cs.flatten ++ O) (encodeCode col) rc my
          (List.replicate pos true)⟩ := by
  dsimp only
  let C := codecs nr nc n s q₁ q₂ w Q k
  let col := (supportCodes nr nc n s q₁ q₂ w Q L k).2
  let cs := List.ofFn (fun a : Fin (q₁ + s + 1) => C.2.encode (j.2 a))
  let pos := q₁ +
    (sourcePosition activity i (forgetTag ξ₀ (.diagonal j))).val
  have hshape : Shape col :=
    (support_recursive_shape n s q₁ q₂ w Q L k hs).2
  have hprod : ∀ c ∈ cs, Produces (meaning col) c := by
    intro c hc'
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hc'
    exact (carrier_support (n := n) (s := s) (q₁ := q₁)
      (q₂ := q₂) (w := w) (Q := Q) hr hc k).2 (j.2 a)
  have hpos : pos < cs.length := by
    simp only [pos, cs, List.length_ofFn]
    have h := (sourcePosition activity i
      (forgetTag ξ₀ (.diagonal j))).isLt
    omega
  obtain ⟨t, ht, v, hrun⟩ := Paper2.FetchIndexed.col_fetch
    col hshape cs hprod O pos hpos (encodeCode col) rc my rfl
  refine ⟨t, ht, v, ?_⟩
  have hword : cs.getD pos [] =
      C.2.encode (sourceColumn activity i
        (forgetTag ξ₀ (.diagonal j))) := by
    rw [List.getD_eq_getElem _ _ hpos]
    change (List.ofFn (fun a : Fin (q₁ + s + 1) =>
      C.2.encode (j.2 a)))[pos] =
      C.2.encode (j.2 ⟨pos, by simpa [cs] using hpos⟩)
    rw [List.getElem_ofFn]
  simpa only [hword] using hrun

#print axioms unrestricted_source_tail_fetch
#print axioms diagonal_source_tail_fetch

end Paper2.GenericSupportTailFetch
