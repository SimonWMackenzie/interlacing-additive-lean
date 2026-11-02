import CurrentAdditive.CanonicalWriterBank

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing Paper2.YaoIndexDecoder
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

/-- First stage of the canonical writer callback: the inherited fixed index
program runs on the actual writer row/column cells and the seven-cell static
bank. It leaves the five decoded numeric coordinates in cells 7..11. -/
theorem canonical_writer_index_run {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d)) :
    ∃ steps ≤ canonicalIndexClock b t d i.val j.val,
      ((advance (program canonicalIndexPlace))^[steps])
        (⟨some startLabel, startControl,
          canonicalReady b t d modulus edges i.val j.val⟩ :
          TM2.Cfg (fun _ : CanonicalCell => Bool) _ _) =
        ⟨none, startControl,
          Function.update (Function.update (Function.update (Function.update
            (Function.update (canonicalReady b t d modulus edges i.val j.val)
              (canonicalIndexPlace 8)
              (List.replicate (((rowIndex v b t).symm i).1.val) true))
            (canonicalIndexPlace 9)
              (List.replicate (((rowIndex v b t).symm i).2.val) true))
            (canonicalIndexPlace 10)
              (List.replicate (((columnIndex b t d).symm j).1.val) true))
            (canonicalIndexPlace 11)
              (List.replicate (((columnIndex b t d).symm j).2.1.val) true))
            (canonicalIndexPlace 12)
              (List.replicate (((columnIndex b t d).symm j).2.2.val) true)⟩ := by
  obtain ⟨h0, h1, h2, h3, h4, hs⟩ :=
    canonicalReady_index_inputs b t d modulus edges i.val j.val
  obtain ⟨steps, ht, hr⟩ := physical_canonical_index_decode
    b t d canonicalIndexPlace
    (canonicalReady b t d modulus edges i.val j.val) i j
    h0 h1 h2 h3 h4 hs
  exact ⟨steps, ht, hr⟩

#print axioms canonical_writer_index_run

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
