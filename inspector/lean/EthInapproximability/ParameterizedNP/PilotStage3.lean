import NPCC.Engine
import NPCC.Relaxed
import NPCC.Upper

/-!
# Parameterized NP route: Stage--3 transcription pilot

This file kernel-checks the exact power-of-two Stage--3 scale used at
`routes/parameterized-np/autoformalization/sections/07-one-level-construction.tex`
(the paragraph beginning "Stage 3 uses `s`") and at Mechanical Step `step:L-05`
in Section 11.  It deliberately exposes bracket nonemptiness as the typed form
of the manuscript's legal-row and rounding checks.
-/

namespace EthInapproximability.ParameterizedNP

open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open NPCC

/-- A nonempty family of restrictions cannot be harder, at its minimum, than
the ambient game.  This is the public facade of the private helper used in
`NPCC.Stage3.M3_lower_bound`.
-/
theorem familyComplexity_le_ambient {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B → Bool) {family : Set (Finset A × Finset B)}
    (hne : family.Nonempty) :
    Dfamily f family ≤ D f := by
  rcases hne with ⟨RC, hRC⟩
  have hmember :
      D (subgame f RC.1 RC.2) ∈
        {d : Nat | ∃ RC' ∈ family, d = D (subgame f RC'.1 RC'.2)} :=
    ⟨RC, hRC, rfl⟩
  exact le_trans (by simpa [Dfamily] using Nat.sInf_le hmember)
    (D_subgame_le f RC.1 RC.2)

/-- **Indexed selector protocol.** This is the typed form of
`lem:indexed-selector-protocol` in Section 3.  Alice announces the coordinate
of a row in `Nat.clog 2 p` bits.  On a fixed selector branch, Bob can locally
evaluate the indexed column record `c ell` at that coordinate, so the residual
game is a pullback of `f` and costs at most `D f`.

The proof treats unused binary codewords as empty row classes, exactly as in
the manuscript.  The only numerical guard is `1 ≤ p`, which supplies a default
coordinate on those unreachable classes.
-/
theorem indexedSelector_upper
    {X Y L : Type*} [Fintype X] [Fintype Y] [Fintype L]
    (f : X → Y → Bool) (p : Nat) (hp : 1 ≤ p)
    (c : L → Fin p → Y) :
    D (fun (row : Fin p × X) (ell : L) => f row.2 (c ell row.1)) ≤
      D f + Nat.clog 2 p := by
  classical
  let selectorBits := Nat.clog 2 p
  have hpCode : p ≤ 2 ^ selectorBits := by
    exact Nat.le_pow_clog one_lt_two p
  let encode : Fin p → Fin (2 ^ selectorBits) := Fin.castLE hpCode
  let decode : Fin (2 ^ selectorBits) → Fin p := fun k =>
    if hk : k.val < p then ⟨k.val, hk⟩ else ⟨0, hp⟩
  have hpartition :
      D (fun (row : Fin p × X) (ell : L) => f row.2 (c ell row.1)) ≤
        selectorBits + D f := by
    refine comp_le_partition
      (fun (row : Fin p × X) (ell : L) => f row.2 (c ell row.1))
      selectorBits (D f) (fun row => encode row.1) ?_
    intro k
    have hmap :
        D (fun (row : {row : Fin p × X // encode row.1 = k})
              (ell : L) => f row.val.2 (c ell (decode k))) ≤ D f :=
      D_mapNodes_le f
        (fun row : {row : Fin p × X // encode row.1 = k} => row.val.2)
        (fun ell : L => c ell (decode k))
    have hbranch :
        (fun (row : {row : Fin p × X // encode row.1 = k})
            (ell : L) => f row.val.2 (c ell row.val.1)) =
        (fun row ell => f row.val.2 (c ell (decode k))) := by
      funext row ell
      have hval : row.val.1.val = k.val := by
        have := congrArg Fin.val row.property
        simpa [encode] using this
      have hk : k.val < p := by
        rw [← hval]
        exact row.val.1.isLt
      have hdecode : decode k = row.val.1 := by
        apply Fin.ext
        simp [decode, hk, hval]
      rw [hdecode]
    rw [hbranch]
    exact hmap
  omega

/-- The exact indexed `Fin L` interface used by the balanced-family Stage--2
construction (`NPCC.relaxedInterlace`). -/
theorem relaxedInterlace_selector_upper
    {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {p L : Nat} (hp : 1 ≤ p)
    (S : Fin L → Fin p → Y) :
    D (relaxedInterlace f S) ≤ D f + Nat.clog 2 p := by
  simpa [relaxedInterlace] using indexedSelector_upper f p hp S

/-- `lem:interlace-selector-protocol` in Section 3, obtained from the indexed
selector theorem by taking the index type to be the full function space and
the accessor to be the identity. -/
theorem interlace_selector_upper
    {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (p : Nat) (hp : 1 ≤ p) :
    D (interlaceFun f p) ≤ D f + Nat.clog 2 p := by
  have hselector :=
    indexedSelector_upper f p hp (fun column : Fin p → Y => column)
  simpa [interlaceFun] using hselector

/-- The standard selector protocol gives the exact additive upper cost `w`
for a `2^w`-fold classical interlace.  This specializes
`lem:indexed-selector-protocol` to the full function-space column index and is
the upper half of Mechanical Step `step:L-05` in Section 11.
-/
theorem powerOfTwoInterlace_upper {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (w : Nat) :
    D (interlaceFun f (2 ^ w)) ≤ D f + w := by
  have hp : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  simpa [Nat.clog_pow, one_lt_two] using
    interlace_selector_upper f (2 ^ w) hp

/-- **Stage--3 exact-scale pilot.** Robustness of the transposed Stage--2
game and `w ≤ b` feed `NPCC.power_of_two_lower`; nonemptiness promotes that
family lower bound to the whole `2^w`-fold interlace, and the selector protocol
gives the reverse inequality.

This is the exact typed argument claimed in Section 7 and in Mechanical Step
`step:L-05` of Section 11.  No near-exact separation theorem is needed for the
complexity equality itself; its remaining role is protocol-structure control.
-/
theorem stage3_exactScale {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {δ b : ℝ}
    (hrobust : IsRobust f δ b)
    (hb : 1 ≤ b) (hδpos : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hcomplex : 2 ≤ D f) (w : Nat) (hwpos : 1 ≤ w)
    (hwdepth : (w : ℝ) ≤ b)
    (hne :
      (bracketGE X Y (2 ^ w)
        ((2 : ℝ) ^ (w : Nat) * (2 : ℝ) ^ (-b))
        ((1 / 2 + δ) ^ 2)).Nonempty) :
    D (interlaceFun f (2 ^ w)) = D f + w := by
  apply le_antisymm (powerOfTwoInterlace_upper f w)
  exact le_trans
    (power_of_two_lower hrobust hb hδpos hδhalf hcomplex w hwpos hwdepth)
    (familyComplexity_le_ambient (interlaceFun f (2 ^ w)) hne)

end EthInapproximability.ParameterizedNP
