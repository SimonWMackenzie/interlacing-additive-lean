import CurrentAdditive.V39RecursiveTable
import Paper2.HeaderA
import Paper2.SeedEntryMachine

/-! Exact physical final lookup and header boundaries for current labels.
Both programs are fixed. The recursive seed-request words and the table
word must be physically produced before these stages can be sequenced into
the complete sampled printer; neither theorem claims that missing join. -/

namespace CurrentAdditive.V39HeaderJoin

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.V39RecursiveGenerator CurrentAdditive.V39RecursiveTable
open Paper2.RecursiveLabelCodecScratch

variable {n p₀ q₁ q₂ s w Q : ℕ} [NeZero s]

/-- One physical seed lookup after the actual recursive request has been
materialised in its two input registers.  Inputs are preserved and all work
registers are cleared by the reused controller. -/
theorem final_seed_lookup
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (k : ℕ) (x : Row n p₀ q₁ q₂ s w Q k)
    (y : Column n p₀ q₁ q₂ s w Q k) :
    let p := seedRequest activity k x y
    let row := (piCodec boolCodec p₀).encode p.1
    let col := (finCodec p₀).encode p.2
    ∃ t ≤ 9 * p₀ + 13,
      Paper2.SeedEntryMachine.run t (Paper2.SeedEntryMachine.initial row col) =
        Paper2.SeedEntryMachine.final row col (matrix activity k x y)
          (Paper2.SeedEntryMachine.readInitial, none) := by
  intro p row col
  have h := Paper2.SeedEntryMachine.run_encoded_pair p₀ p.1 p.2
  have he : Paper2.LookupSeed.matrix p₀ p.1 p.2 = matrix activity k x y :=
    evaluate_eq_matrix activity k x y
  simpa only [he] using h

noncomputable def headerClock (m B : ℕ) : ℕ :=
  UnaryBinaryEncoding.coefficient * (m + 1) ^ 2 +
    UnaryBinaryEncoding.coefficient * (m + 1) ^ 2 +
    UnaryBinaryEncoding.coefficient * (B + 1) ^ 2 +
    (2 * (natField m ++ natField m ++ natField B).length + 2) + 3

/-- The complete literal header stage, with exact current output identity
and a tape-independent bound. Its starting bank already contains the table;
this is not a claim that header serialization computes table entries. -/
theorem physical_header
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (k m B : ℕ) (z : (Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) (suffix : List Bool) :
    ∃ t ≤ headerClock m B, ∃ v F,
      ((advance Paper2.HeaderA.prog)^[t])
        (⟨some Paper2.HeaderA.progStart, Paper2.HeaderA.progCtl,
          Paper2.HeaderA.Hin m m B (sampledTable activity k m z).bits suffix⟩ :
          TM2.Cfg (fun _ : Paper2.HeaderA.HB => Bool) _ _) = ⟨none, v, F⟩ ∧
        F Paper2.HeaderA.outH = outputWord activity k m B z ++ suffix := by
  exact Paper2.HeaderA.header_instance (tableInstance activity k m B z) suffix

#print axioms final_seed_lookup
#print axioms physical_header

end CurrentAdditive.V39HeaderJoin
