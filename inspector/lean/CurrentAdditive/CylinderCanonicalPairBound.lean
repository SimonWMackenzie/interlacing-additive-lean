import CurrentAdditive.CylinderReachableRowClock

/-! A numerical callback bound computed directly from the selected V2 word,
without choosing a source entry.  On an actual word it agrees with the
canonical coordinate split used by the physical callback proof. -/

namespace CurrentAdditive.CylinderCanonicalPairBound

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderCoordinateRowClock

def wordPairBound (i : Nat) (symbol word output : List Bool) : Nat :=
  let xs := (SourceListEncoding.decode word).getD []
  pairBound (xs.take i) (xs[i]?.getD []) (xs.drop (i + 1))
    symbol output

theorem wordPairBound_canonical {q : Nat}
    (entry : (Fin q → Nat) × ℚ) (i : Fin q)
    (symbol output : List Bool) :
    let xs := List.ofFn (fun j : Fin q => (entry.1 j).bits)
    wordPairBound i.val symbol (SourceListEncoding.encode xs) output =
      pairBound (xs.take i.val) (entry.1 i).bits
        (xs.drop (i.val + 1)) symbol output := by
  dsimp [wordPairBound]
  simp [SourceListEncoding.decode_encode]

#print axioms wordPairBound_canonical

end CurrentAdditive.CylinderCanonicalPairBound
