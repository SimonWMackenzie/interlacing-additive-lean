import CurrentAdditive.SmallBiasSourceInstance
import CurrentAdditive.CanonicalPrintedTable

/-!
# Source-faithful canonical printed table

Source: v27 `07-yao.tex`, before `yao:main`: `H` is the least power of two
at least `max 1 |E|`. This file uses that exact choice, unlike the earlier
`publicAddressBits` padding variant. The row/column order is the executable
canonical order of `CanonicalPrintedTable`; polynomial running time is a
separate obligation.
-/

noncomputable section

namespace CurrentAdditive.SmallBias

set_option maxHeartbeats 2000000

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open Paper2.YaoCloneSource Paper2.YaoX05Draft
open CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

def exactAddressBits (edgeCount : ℕ) : ℕ :=
  Nat.clog 2 (max 1 edgeCount)

theorem exactAddress_capacity (edgeCount : ℕ) :
    edgeCount ≤ 2 ^ exactAddressBits edgeCount := by
  calc
    edgeCount ≤ max 1 edgeCount := Nat.le_max_right _ _
    _ ≤ 2 ^ exactAddressBits edgeCount :=
      Nat.le_pow_clog (by omega : 1 < 2) _

theorem exactAddress_least (edgeCount k : ℕ)
    (hk : max 1 edgeCount ≤ 2 ^ k) : exactAddressBits edgeCount ≤ k :=
  (Nat.clog_le_iff_le_pow (by omega : 1 < 2)).2 hk

def exactAddressIndex (edgeCount : ℕ) :
    Fin edgeCount ↪ Fin (2 ^ exactAddressBits edgeCount) :=
  Fin.castLEEmb (exactAddress_capacity edgeCount)

def sourceExactAddressWidth (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) : ℕ :=
  exactAddressBits (sourceEdgeCount g G input)

def sourceExactModulus (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) : ℕ :=
  (TrialSearch.firstPassing
    (publicFieldDegree (sourceExactAddressWidth g G input)
      (v27GapParameter g))).getD 0

theorem sourceExactModulus_found (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) :
    TrialSearch.firstPassing
        (publicFieldDegree (sourceExactAddressWidth g G input)
          (v27GapParameter g)) =
      some (sourceExactModulus g G input) := by
  obtain ⟨modulus, hmod, _⟩ :=
    public_firstPassing_correct (sourceExactAddressWidth g G input)
      (v27GapParameter g)
  simp [sourceExactModulus, hmod]

def sourceCanonicalInstance (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) : Instance :=
  let t := v27GapParameter g
  let source := cloneSource t (forbiddenColours t) (G.output input)
  let b := exactAddressBits source.2.1
  CanonicalTable.instanceOfTable b t (publicFieldDegree b t)
    (sourceExactModulus g G input) (exactAddress_capacity source.2.1)
    source.2.2

theorem sourceCanonicalInstance_valid (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) :
    (sourceCanonicalInstance g G input).Valid := by
  unfold sourceCanonicalInstance CanonicalTable.instanceOfTable
  apply Paper2.EncodedSelectedOutput.instanceOf_valid
  · dsimp [CanonicalTable.rowCount]
    exact Nat.mul_pos (draft_clone_source_nonempty G input) (by positivity)
  · dsimp [CanonicalTable.columnCount]
    positivity

theorem sourceCanonicalInstance_yes_no (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) :
    let t := v27GapParameter g
    let b := sourceExactAddressWidth g G input
    let i := sourceCanonicalInstance g G input
    (input ∈ G.L →
      Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table) ≤
        2 * b + 4 * t + 2) ∧
    (input ∉ G.L →
      (2 * b + 4 * t + 2) + g ≤
        Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table)) := by
  dsimp only
  let t := v27GapParameter g
  let source := cloneSource t (forbiddenColours t) (G.output input)
  let b := exactAddressBits source.2.1
  obtain ⟨output, modulus, _, hmod, _, _, hyes, hno⟩ :=
    public_printed_matrix_fixed_gap g b source.2.2
      (exactAddressIndex source.2.1)
  have hsame : modulus = sourceExactModulus g G input := by
    have hfound := sourceExactModulus_found g G input
    have hb : b = sourceExactAddressWidth g G input := rfl
    rw [← hb] at hfound
    exact Option.some.inj (hmod.symm.trans hfound)
  subst modulus
  have htable := CanonicalTable.table_Dalt b t (publicFieldDegree b t)
    (sourceExactModulus g G input) (exactAddress_capacity source.2.1)
    source.2.2 .alice
  have hgame := Paper2.EncodedSelectedOutput.tableGame_eq_matrix
    (CanonicalTable.table b t (publicFieldDegree b t)
      (sourceExactModulus g G input) (exactAddress_capacity source.2.1)
      source.2.2)
  have hcost : Dalt .alice (ProtocolVerifier.tableGame
      (sourceCanonicalInstance g G input).rows
      (sourceCanonicalInstance g G input).cols
      (sourceCanonicalInstance g G input).table) =
      Dalt .alice (matrix (placeEdges source.2.2
        (exactAddressIndex source.2.1))
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (printedPairFieldWord b t (publicFieldDegree b t)
          (sourceExactModulus g G input))) := by
    change Dalt .alice (ProtocolVerifier.tableGame
      (CanonicalTable.rowCount source.1 b t)
      (CanonicalTable.columnCount b t (publicFieldDegree b t))
      (CanonicalTable.table b t (publicFieldDegree b t)
        (sourceExactModulus g G input) (exactAddress_capacity source.2.1)
        source.2.2).bits) = _
    rw [hgame]
    exact htable
  constructor
  · intro hm
    rw [hcost]
    obtain ⟨colour, hbalanced⟩ := draft_clone_source_yes G input hm
    exact hyes colour hbalanced
  · intro hn
    rw [hcost]
    exact hno (draft_clone_source_no G input hn)

#print axioms CurrentAdditive.SmallBias.exactAddress_capacity
#print axioms CurrentAdditive.SmallBias.exactAddress_least
#print axioms CurrentAdditive.SmallBias.sourceCanonicalInstance_valid
#print axioms CurrentAdditive.SmallBias.sourceCanonicalInstance_yes_no

end CurrentAdditive.SmallBias
