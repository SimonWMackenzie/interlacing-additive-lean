import EthInapproximability.CurrentPaper.MatrixTableInterlaceRowReverse

/-!
# Exact numerical coding of the two restorations

Frozen v8 `eq:one-level-exact-carriers` and `def:paper-interlace`.
This identifies the actual one-level matrix entry with two numbered
interlace/row-block-reversal/transpose steps.  It is a coding theorem,
not a claim that the three physical table controllers have yet been joined
by charged bank transfers.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceLevelCodes

open MatrixTableInterlaceRowReverse

def numericSource {X Y : Type} (W : X → Y → Bool)
    (eX : Iteration.Numbering X) (eY : Iteration.Numbering Y) :
    Fin eX.size → Fin eY.size → Bool :=
  fun x y => W (eX.equiv x) (eY.equiv y)

theorem firstRestoration_numeric {X Y : Type} (W : X → Y → Bool)
    (eX : Iteration.Numbering X) (eY : Iteration.Numbering Y)
    (r : ℕ) (c : Fin (eY.size ^ (2^r)))
    (row : Fin ((2^r)*eX.size)) :
    Restoration.output W r ((eY.tuple (2^r)).equiv c)
      (((Iteration.Numbering.fin (2^r)).prod eX).equiv row) =
    numberedRestoration r eX.size eY.size
      (numericSource W eX eY) c row := by
  rw [numberedRestoration_eq, numberedInterlace_eq]
  exact MatrixTableInterlaceNumbering.restoration_numeric W eX eY r c row

theorem secondRestoration_numeric {X Y : Type} (W : X → Y → Bool)
    (eX : Iteration.Numbering X) (eY : Iteration.Numbering Y)
    (r R : ℕ)
    (c : Fin (((2^r)*eX.size) ^ (2^R)))
    (row : Fin ((2^R)*(eY.size ^ (2^r)))) :
    Restoration.output (Restoration.output W r) R
      (((((Iteration.Numbering.fin (2^r)).prod eX).tuple (2^R))).equiv c)
      (((Iteration.Numbering.fin (2^R)).prod
        (eY.tuple (2^r))).equiv row) =
    numberedRestoration R (eY.size ^ (2^r)) ((2^r)*eX.size)
      (numberedRestoration r eX.size eY.size
        (numericSource W eX eY)) c row := by
  let eA := eY.tuple (2^r)
  let eB := (Iteration.Numbering.fin (2^r)).prod eX
  have hfirst :
      (fun x y => Restoration.output W r (eA.equiv x) (eB.equiv y)) =
      numberedRestoration r eX.size eY.size (numericSource W eX eY) := by
    funext x y
    exact firstRestoration_numeric W eX eY r x y
  have h := firstRestoration_numeric (Restoration.output W r) eA eB R c row
  change Restoration.output (Restoration.output W r) R
      ((eB.tuple (2^R)).equiv c)
      (((Iteration.Numbering.fin (2^R)).prod eA).equiv row) =
    numberedRestoration R eA.size eB.size
      (numericSource (Restoration.output W r) eA eB) c row at h
  simpa only [numericSource, hfirst] using h

/-- Exact one-level endpoint: after the protected matrix is numbered by the
explicit protected-row and protected-column enumerations, the two numeric
restoration tables give the literal entry of `Iteration.step`. -/
theorem step_entry_numeric {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (sourceConstant b y i : ℕ) (M : Iteration.Matrix)
    (x : Fin (Iteration.step G sourceConstant b y i M).rows)
    (z : Fin (Iteration.step G sourceConstant b y i M).columns) :
    (Iteration.step G sourceConstant b y i M).entry x z =
      numberedRestoration
        (Iteration.rQ G sourceConstant b y i M)
        ((Iteration.nColNumbering G sourceConstant b y i M).size ^
          (2 ^ Iteration.rq G sourceConstant b y i M))
        ((2 ^ Iteration.rq G sourceConstant b y i M) *
          (Iteration.nRowNumbering G sourceConstant b y i M).size)
        (numberedRestoration
          (Iteration.rq G sourceConstant b y i M)
          (Iteration.nRowNumbering G sourceConstant b y i M).size
          (Iteration.nColNumbering G sourceConstant b y i M).size
          (numericSource (Iteration.protectedMatrix G sourceConstant b y i M)
            (Iteration.nRowNumbering G sourceConstant b y i M)
            (Iteration.nColNumbering G sourceConstant b y i M))) x z := by
  rw [Iteration.step_entry]
  exact secondRestoration_numeric
    (Iteration.protectedMatrix G sourceConstant b y i M)
    (Iteration.nRowNumbering G sourceConstant b y i M)
    (Iteration.nColNumbering G sourceConstant b y i M)
    (Iteration.rq G sourceConstant b y i M)
    (Iteration.rQ G sourceConstant b y i M) x z

end EthInapproximability.CurrentPaper.MatrixTableInterlaceLevelCodes
