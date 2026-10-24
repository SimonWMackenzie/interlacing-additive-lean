import CurrentAdditive.GenericCodeNavigation
import CurrentAdditive.CompactFinCodec
import Paper2.OutputSkipperLabel
import Paper2.RecursiveRequestCodeShape

/-! A separate navigation code with the same compact index words as the
rational sampler. Its tagged ternary grammar is exactly the grammar accepted
by the inherited physical output skipper. Sampling still uses the rational
code; this code is only a support witness for parsing a sampled word. -/

namespace Paper2.CompactSupportShape

open Paper2.GeneratorCode
open Paper2.RecursiveRequestCodeShape
open Paper2.CompactFinCodec

def support : ℕ → Code
  | 0 => .emit [false]
  | L + 1 =>
      .branch3 256 254 255
        (.append (.emit [false]) (.emit []))
        (.append (.emit [true, false]) (support L))
        (.append (.emit [true, true]) (support L))

theorem support_shape (L : ℕ) : Paper2.OutputSkipper.Shape (support L) := by
  induction L with
  | zero => trivial
  | succ L ih =>
      simp only [support, Paper2.OutputSkipper.Shape]
      refine ⟨Or.inr (Or.inl ?_), ?_, ?_, ?_⟩
      · exact ⟨trivial, trivial, trivial,
          ⟨.emit [], support L, support L, rfl, rfl, rfl⟩⟩
      · exact ⟨trivial, trivial⟩
      · exact ⟨trivial, ih⟩
      · exact ⟨trivial, ih⟩

private theorem emit_produces (bs : List Bool) :
    Produces (meaning (.emit bs)) bs :=
  (produces_emit bs bs).mpr rfl

private theorem append_produces (a b : Code) (x y : List Bool)
    (hx : Produces (meaning a) x) (hy : Produces (meaning b) y) :
    Produces (meaning (.append a b)) (x ++ y) :=
  (produces_concat _ _).mpr ⟨x, y, hx, hy, rfl⟩

theorem support_produces (L : ℕ) (bs : List Bool)
    (h : bs.length ≤ L) :
    Produces (meaning (support L)) (frame bs) := by
  induction L generalizing bs with
  | zero =>
      cases bs with
      | nil => exact emit_produces [false]
      | cons b rest => simp at h
  | succ L ih =>
      cases bs with
      | nil =>
          change Produces
            (RecursiveSamplingProgram.Program.draw 256 (by omega)
              (fun i => if i.val < 254 then
                meaning (.append (.emit [false]) (.emit []))
              else if i.val < 255 then
                meaning (.append (.emit [true, false]) (support L))
              else meaning (.append (.emit [true, true]) (support L)))) [false]
          refine .draw (i := (⟨0, by omega⟩ : Fin 256)) ?_
          simpa using append_produces (.emit [false]) (.emit [])
            [false] [] (emit_produces _) (emit_produces _)
      | cons b rest =>
          have hr : rest.length ≤ L := by simp at h; omega
          cases b with
          | false =>
              change Produces
                (RecursiveSamplingProgram.Program.draw 256 (by omega)
                  (fun i => if i.val < 254 then
                    meaning (.append (.emit [false]) (.emit []))
                  else if i.val < 255 then
                    meaning (.append (.emit [true, false]) (support L))
                  else meaning (.append (.emit [true, true]) (support L))))
                (true :: false :: frame rest)
              refine .draw (i := (⟨254, by omega⟩ : Fin 256)) ?_
              simpa using append_produces (.emit [true, false]) (support L)
                [true, false] (frame rest) (emit_produces _) (ih rest hr)
          | true =>
              change Produces
                (RecursiveSamplingProgram.Program.draw 256 (by omega)
                  (fun i => if i.val < 254 then
                    meaning (.append (.emit [false]) (.emit []))
                  else if i.val < 255 then
                    meaning (.append (.emit [true, false]) (support L))
                  else meaning (.append (.emit [true, true]) (support L))))
                (true :: true :: frame rest)
              refine .draw (i := (⟨255, by omega⟩ : Fin 256)) ?_
              simpa using append_produces (.emit [true, true]) (support L)
                [true, true] (frame rest) (emit_produces _) (ih rest hr)

theorem support_index {n L : ℕ} (hn : n ≤ 2 ^ L)
    (i : Fin n) :
    Produces (meaning (support L)) ((codec n).encode i) := by
  apply support_produces
  have hi : i.val < 2 ^ L := lt_of_lt_of_le i.isLt hn
  simpa only [Nat.size_eq_bits_len] using (Nat.size_le.mpr hi)

theorem support_recursive_shape (n s q₁ q₂ w Q L k : ℕ)
    (hs : 0 < s) :
    Paper2.OutputSkipper.Shape
      (Paper2.GeneratorSource.recursiveCodes n s q₁ q₂ w Q
        (support L) (support L) k).1 ∧
    Paper2.OutputSkipper.Shape
      (Paper2.GeneratorSource.recursiveCodes n s q₁ q₂ w Q
        (support L) (support L) k).2 := by
  exact Paper2.OutputSkipper.shape_recursiveCodes n s q₁ q₂ w Q hs
    (support L) (support L) (support_shape L) (support_shape L) k

#print axioms support_shape
#print axioms support_produces
#print axioms support_index
#print axioms support_recursive_shape

end Paper2.CompactSupportShape
