import CurrentAdditive.SmallBiasEncodedTable

/-!
# A fixed encoded matrix instance from the source input

Source: v27 `yao:source`, `yao:main`, and `yao:bpp`. The modulus is the
first passing candidate at a degree computed from the public source size.
The table is the row-major printed-bit function. This is an extensional
output specification; a machine implementation and clock are separate.
-/

namespace CurrentAdditive.SmallBias

set_option maxHeartbeats 2000000

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open Paper2.YaoCloneSource Paper2.YaoX05Draft
open CurrentAdditive.FiniteFieldConstructor
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

def sourceEdgeCount (g : ℕ) (G : GLSourceDraft (v27GapParameter g))
    (input : List Bool) : ℕ :=
  (cloneSource (v27GapParameter g)
    (forbiddenColours (v27GapParameter g)) (G.output input)).2.1

def sourceAddressWidth (g : ℕ) (G : GLSourceDraft (v27GapParameter g))
    (input : List Bool) : ℕ :=
  publicAddressBits (sourceEdgeCount g G input)

def sourceModulus (g : ℕ) (G : GLSourceDraft (v27GapParameter g))
    (input : List Bool) : ℕ :=
  (TrialSearch.firstPassing
    (publicFieldDegree (sourceAddressWidth g G input)
      (v27GapParameter g))).getD 0

theorem sourceModulus_found (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) :
    TrialSearch.firstPassing
        (publicFieldDegree (sourceAddressWidth g G input)
          (v27GapParameter g)) =
      some (sourceModulus g G input) := by
  obtain ⟨modulus, hmod, _⟩ :=
    public_firstPassing_correct (sourceAddressWidth g G input)
      (v27GapParameter g)
  simp [sourceModulus, hmod]

noncomputable def sourcePrintedInstance (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) : Instance :=
  let t := v27GapParameter g
  let source := cloneSource t (forbiddenColours t) (G.output input)
  let b := sourceAddressWidth g G input
  printedInstance b t (publicFieldDegree b t) (sourceModulus g G input)
    source.2.2 (publicAddressIndex source.2.1)

theorem sourcePrintedInstance_valid (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) :
    (sourcePrintedInstance g G input).Valid := by
  unfold sourcePrintedInstance
  exact printedInstance_valid (draft_clone_source_nonempty G input)
    _ _ _ _ _ _

theorem sourcePrintedInstance_decode (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) :
    decodeInstance (encodeInstance (sourcePrintedInstance g G input)) =
      some (sourcePrintedInstance g G input) :=
  decode_encode _ (sourcePrintedInstance_valid g G input)

theorem sourcePrintedInstance_yes_no (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) :
    let t := v27GapParameter g
    let b := sourceAddressWidth g G input
    let i := sourcePrintedInstance g G input
    (input ∈ G.L →
      Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table) ≤
        2 * b + 4 * t + 2) ∧
    (input ∉ G.L →
      (2 * b + 4 * t + 2) + g ≤
        Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table)) := by
  dsimp only
  let t := v27GapParameter g
  let source := cloneSource t (forbiddenColours t) (G.output input)
  let b := sourceAddressWidth g G input
  obtain ⟨output, modulus, _, hmod, _, hyes, hno⟩ :=
    gl_source_public_printed_gap g G input
  have hsame : modulus = sourceModulus g G input := by
    have hfound := sourceModulus_found g G input
    have hb : b = publicAddressBits source.2.1 := rfl
    rw [← hb] at hmod
    exact Option.some.inj (hmod.symm.trans hfound)
  subst modulus
  have htable := printedInstance_Dalt b t
    (publicFieldDegree b t) (sourceModulus g G input)
    source.2.2 (publicAddressIndex source.2.1) .alice
  change Dalt .alice (ProtocolVerifier.tableGame
      (sourcePrintedInstance g G input).rows
      (sourcePrintedInstance g G input).cols
      (sourcePrintedInstance g G input).table) =
      Dalt .alice (matrix (placeEdges source.2.2
        (publicAddressIndex source.2.1))
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (printedPairFieldWord b t (publicFieldDegree b t)
          (sourceModulus g G input))) at htable
  constructor
  · intro hm
    rw [htable]
    exact hyes hm
  · intro hn
    rw [htable]
    exact hno hn

#print axioms CurrentAdditive.SmallBias.sourceModulus_found
#print axioms CurrentAdditive.SmallBias.sourcePrintedInstance_valid
#print axioms CurrentAdditive.SmallBias.sourcePrintedInstance_yes_no

end CurrentAdditive.SmallBias
