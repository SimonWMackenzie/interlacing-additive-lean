import EthInapproximability.CurrentPaper.Construction
import EthInapproximability.CurrentPaper.MatrixMaterialization

/-!
# Explicit ordinal codes for the variable-bin Stage--4 raw matrix

Source: frozen v8 `03-parameterized-construction.tex`, `eq:paper-B-carriers`,
`eq:paper-B-template`, `eq:paper-B-source`, and
`B-effectivity-details.tex`, `thm:paper-materialization`.

These equivalences fix a row-major target for the *general* Stage--4 matrix
with `s` bins, including its item order and entire `s+1`-coordinate tail.
They are coding semantics, not bit-machine runtime claims.  Subsequent
physical decoders must implement these precise codes on unary/binary stacks.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4Codes

open Construction MatrixMaterialization
open Workspace.Types.CommComplexity

def rows (s L nv nb rx : ℕ) : ℕ := s*L+(nv+nb)*rx

def cols (a s q cy : ℕ) : ℕ :=
  cy^(s+1) * (q*cy^(firstLength a s))^s

def rowCode (s L nv nb rx : ℕ) (order : ItemOrder nv nb) :
    RawRows s L nv nb (Fin rx) ≃ Fin (rows s L nv nb rx) :=
  (rawRowEquiv s L nv nb order).trans
    ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)

def firstWordCode (a s cy : ℕ) :
    FirstColumns a s (Fin cy) ≃ Fin (cy^(firstLength a s)) :=
  tupleCode cy (firstLength a s)

def secondRowCode (a s q cy : ℕ) :
    SecondRows a s q (Fin cy) ≃ Fin (q*cy^(firstLength a s)) :=
  (Equiv.prodCongr (Equiv.refl _) (firstWordCode a s cy)).trans finProdFinEquiv

def thirdColumnCode (a s q cy : ℕ) :
    ThirdColumns a s q (Fin cy) ≃ Fin ((q*cy^(firstLength a s))^s) :=
  (Equiv.arrowCongr (Equiv.refl _) (secondRowCode a s q cy)).trans
    (tupleCode (q*cy^(firstLength a s)) s)

def rawColumnCode (a s q cy : ℕ) :
    RawColumns a s q (Fin cy) ≃ Fin (cols a s q cy) :=
  (Equiv.prodCongr (tupleCode cy (s+1)) (thirdColumnCode a s q cy)).trans
    finProdFinEquiv

variable {rx cy : ℕ}

def encodedRaw (R : Fin rx → Fin cy → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (family : SecondFamily a q L (Fin rx))
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) :
    Fin (rows s L nv nb rx) → Fin (cols a s q cy) → Bool :=
  fun i j => rawMatrix R a s q L nv nb hs family order vectors cap
    ((rowCode s L nv nb rx order).symm i)
    ((rawColumnCode a s q cy).symm j)

def rawTable (R : Fin rx → Fin cy → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (family : SecondFamily a q L (Fin rx))
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) : List Bool :=
  rowMajor (encodedRaw R a s q L nv nb hs family order vectors cap)

@[simp] theorem rawTable_length (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) :
    (rawTable R a s q L nv nb hs family order vectors cap).length =
      rows s L nv nb rx * cols a s q cy := by
  simp [rawTable]

theorem rawTable_entry (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (r : RawRows s L nv nb (Fin rx))
    (c : RawColumns a s q (Fin cy)) :
    (rawTable R a s q L nv nb hs family order vectors cap)[
      (rowCode s L nv nb rx order r).val * cols a s q cy +
      (rawColumnCode a s q cy c).val]? =
        some (rawMatrix R a s q L nv nb hs family order vectors cap r c) := by
  rw [rawTable, rowMajor_entry]
  simp [encodedRaw]

end EthInapproximability.CurrentPaper.MatrixStage4Codes
