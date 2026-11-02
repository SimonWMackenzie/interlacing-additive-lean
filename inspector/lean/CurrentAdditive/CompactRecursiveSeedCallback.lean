import CurrentAdditive.CompactPhysicalBaseSize
import Paper2.RecursiveEntries

/-! The physical base program is the final callback after the recursive
navigation has supplied its one seed pair.  The pair is an explicit input to
this theorem; no physical navigation or its clock is hidden here. -/

namespace Paper2.CompactRecursiveSeedCallback

open Paper2.CompactRationalPacket Paper2.RecursiveEntries
open Paper2.CompactPhysicalBaseLookup
open Paper2.CompactPhysicalBaseSize
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Turing Turing.TM2.Stmt

theorem seed_entry_eq_matrix {rows cols : ℕ} {I : Type}
    {s q₁ q₂ w Q : ℕ} [NeZero s]
    (P : Packet rows cols)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin rows) (Fin cols) I s q₁ q₂ w Q)
    (k : ℕ)
    (x : Row (Fin rows) (Fin cols) I s q₁ q₂ w Q k)
    (y : Column (Fin rows) (Fin cols) I s q₁ q₂ w Q k) :
    let sd := seedRequest activity ξ k x y
    P.table.matrix sd.1 sd.2 =
      matrix P.table.matrix activity ξ k x y := by
  dsimp
  calc
    P.table.matrix (seedRequest activity ξ k x y).1
        (seedRequest activity ξ k x y).2 =
        evaluate P.table.matrix activity ξ k x y :=
      (evaluate_eq_seed_entry P.table.matrix activity ξ k x y).symm
    _ = matrix P.table.matrix activity ξ k x y :=
      evaluate_eq_matrix P.table.matrix activity ξ k x y

theorem supplied_seed_lookup {rows cols L : ℕ} {I : Type}
    {s q₁ q₂ w Q : ℕ} [NeZero s]
    (P : Packet rows cols) (hr : rows ≤ 2 ^ L)
    (hc : cols ≤ 2 ^ L)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin rows) (Fin cols) I s q₁ q₂ w Q)
    (k : ℕ)
    (x : Row (Fin rows) (Fin cols) I s q₁ q₂ w Q k)
    (y : Column (Fin rows) (Fin cols) I s q₁ q₂ w Q k) :
    let sd := seedRequest activity ξ k x y
    ∃ t ≤ 2 ^ (4 * L + 12),
      ((advance program)^[t])
        ⟨some start, initial,
          Paper2.ASquare.Post.pbank [] [] (input P sd.1 sd.2)
            Paper2.ASquare.Post.ext0⟩ =
      ⟨none, (Paper2.ASquare.Post.pinit,
          ((false, false), MatrixTableLookup.initial)),
        Paper2.ASquare.Post.pbank
          (List.replicate sd.1.val true) (List.replicate cols true)
          P.table.bits
          (Paper2.ASquare.Post.ext (List.replicate sd.2.val true) [] []
            [matrix P.table.matrix activity ξ k x y] [] [] [] [])⟩ := by
  dsimp
  obtain ⟨t, ht, h⟩ := lookup_run_exponential P hr hc
    (seedRequest activity ξ k x y).1 (seedRequest activity ξ k x y).2
  have he := seed_entry_eq_matrix P activity ξ k x y
  refine ⟨t, ht, ?_⟩
  rw [← he]
  exact h

#print axioms seed_entry_eq_matrix
#print axioms supplied_seed_lookup

end Paper2.CompactRecursiveSeedCallback
