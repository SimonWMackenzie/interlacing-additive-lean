import Paper2.E3Loops
import Paper2.ECutRun
import Paper2.SubexpBudget

/-!
# Paper A (lock v12), lane `owner:a-eth-3`, segment 1 (obstacle B2): the fixed inner machine of the
# cutter and the physical front cut

Lock v12 `sections/06-reduction.tex` (proof of `thm:quantitative`): "choose
$k=\floor{N/\ceil{\log N}^2}$ ... Both the construction and any fixed polynomial-time estimator take
$n^{O(k+1)}=2^{O(N/\log N)}=2^{o(N)}$". ROOT DECISION R20 and the a-eth-owner-1 KEY DESIGN
CONSTRAINT: no stage before the cut may have a clock depending on the unread tape.

* `innerMachine` (ONE fixed machine): on the literal word `encode F` of EVERY CNF `F` (valid or
  not) it prints `fOut F = pair (encode F) (pair (1^(expLen N)) [])`, `N = F.variables`, within
  `innerTime F` (`inner_outputs`). It is `RawDup ; PairMap Mu ; Swap` with
  `Mu = SourceOriginalVariableCapture.machine ; lenMachine` (admitted variable capture, then the
  a-eth-owner-1 unary length machine applied to `1^N`); every handoff is charged by the admitted
  `composition_outputsWithin`.
* `frontCut = Cut.machine innerMachine 1 1 ; PairMap Fst` (ONE fixed machine): on
  `pair (encode F) t` for EVERY raw tape `t` of ANY length it prints
  `pair (encode F) (t.take (cutLen F))`, `cutLen F = 2|encode F| + 2·expLen N + 3`, within
  `frontTime F`, a bound in `|encode F|` and `N` ONLY (`frontCut_outputs`).
* `cutLen_ge`: `2·expLen N ≤ cutLen F`; `bits_fit`: for `N` large and every
  `n ≤ N·⌈log₂(N+2)⌉^p`, `(n+2)^(K·(kOf N+1)) ≤ expLen N` for every constant `K`; hence the
  selected T24 experiment's `inputBits` at `k = kOf N` is at most `expLen N` (`inputBits_fit`).

No ledger row is closed.
-/

noncomputable section

namespace Paper2.AEth3

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.Unit4Shell.KofLoops

/-- `encode F ↦ 1^(expLen F.variables)`. -/
def Mu : BitMachine.Machine :=
  BitMachineComposition.composition SourceOriginalVariableCapture.machine Paper2.AEth.lenMachine

/-- The clock of `Mu`. -/
def muTime (N : ℕ) : ℕ := 2 * N + 3 + 2 * N + 2 + Paper2.AEth.lenTime N

theorem Mu_outputs (F : EncodedCNF.Formula) :
    Mu.OutputsWithin (EncodedCNF.encode F)
      (List.replicate (Paper2.AEth.expLen F.variables) true) (muTime F.variables) := by
  have h := BitMachineComposition.composition_outputsWithin _ _
    (SourceOriginalVariableCapture.canonical_outputs F)
    (Paper2.AEth.lenMachine_outputs F.variables)
  refine BitMachine.outputsWithin_mono _ h ?_
  simp [muTime]

/-- THE fixed inner machine of the cutter. -/
def innerMachine : BitMachine.Machine :=
  BitMachineComposition.composition RawDup.machine
    (BitMachineComposition.composition (Paper2.Unit4Shell.PairMap.machine Mu) Swap.machine)

/-- The inner machine's printed word: the formula word and the unary cut request. -/
def fOut (F : EncodedCNF.Formula) : List Bool :=
  EncodedComplexity.pair (EncodedCNF.encode F)
    (EncodedComplexity.pair (List.replicate (Paper2.AEth.expLen F.variables) true) [])

/-- The inner clock, in `X = |encode F|`, `N` and `U = expLen N` only. -/
def innerTime (F : EncodedCNF.Formula) : ℕ :=
  5 * (EncodedCNF.encode F).length + 8 + 2 * (4 * (EncodedCNF.encode F).length + 2) + 2 +
    ((2 * (EncodedCNF.encode F).length + muTime F.variables +
        2 * Paper2.AEth.expLen F.variables + 6) +
      2 * (2 * Paper2.AEth.expLen F.variables + 2 * (EncodedCNF.encode F).length + 2) + 2 +
      3 * (2 * Paper2.AEth.expLen F.variables + 2 * (EncodedCNF.encode F).length + 2 + 1))

theorem fOut_length (F : EncodedCNF.Formula) :
    (fOut F).length =
      2 * (EncodedCNF.encode F).length + 2 * Paper2.AEth.expLen F.variables + 2 := by
  simp only [fOut, EncodedComplexity.pair_length, List.length_replicate, List.length_nil]
  omega

/-- **The inner machine is correct and charged** on the literal word of every CNF. -/
theorem inner_outputs (F : EncodedCNF.Formula) :
    innerMachine.OutputsWithin (EncodedCNF.encode F) (fOut F) (innerTime F) := by
  have h1 := RawDup.machine_outputs (EncodedCNF.encode F)
  have h2 := Paper2.Unit4Shell.PairMap.machine_outputs (M := Mu) (EncodedCNF.encode F)
    (List.replicate (Paper2.AEth.expLen F.variables) true)
    (EncodedComplexity.pair (EncodedCNF.encode F) []) _ (Mu_outputs F)
  have h3 := Swap.machine_outputs (List.replicate (Paper2.AEth.expLen F.variables) true)
    (EncodedCNF.encode F) []
  have hC := BitMachineComposition.composition_outputsWithin _ _ h1
    (BitMachineComposition.composition_outputsWithin _ _ h2 h3)
  refine BitMachine.outputsWithin_mono _ hC ?_
  simp only [innerTime, EncodedComplexity.pair_length, List.length_replicate, List.length_nil]
  omega

/-- The cut length. -/
def cutLen (F : EncodedCNF.Formula) : ℕ := (fOut F).length + 1

theorem cutLen_eq (F : EncodedCNF.Formula) :
    cutLen F = 2 * (EncodedCNF.encode F).length + 2 * Paper2.AEth.expLen F.variables + 3 := by
  rw [cutLen, fOut_length]

theorem cutLen_ge (F : EncodedCNF.Formula) :
    2 * Paper2.AEth.expLen F.variables ≤ cutLen F := by
  rw [cutLen_eq]; omega

/-- THE fixed front-cut machine. -/
def frontCut : BitMachine.Machine :=
  BitMachineComposition.composition (Paper2.AEth2.Cut.machine innerMachine 1 1)
    (Paper2.Unit4Shell.PairMap.machine Fst.machine)

/-- The front-cut clock: in `|encode F|` and `N` only. -/
def frontTime (F : EncodedCNF.Formula) : ℕ :=
  Paper2.AEth2.Cut.cutTimeG 1 1 innerMachine.pushBound (EncodedCNF.encode F).length
      (innerTime F) +
    2 * (2 * (fOut F).length + 1 + cutLen F) + 2 +
    (2 * (fOut F).length + (2 * (EncodedCNF.encode F).length + 3) +
      2 * (EncodedCNF.encode F).length + 6)

/-- **The physical front cut.** For every CNF `F` and EVERY raw tape `t` (any length), the fixed
machine `frontCut` prints `pair (encode F) (t.take (cutLen F))` within `frontTime F`, which does
not depend on `t`: the unread rest of the tape is never touched. -/
theorem frontCut_outputs (F : EncodedCNF.Formula) (t : List Bool) :
    frontCut.OutputsWithin (EncodedComplexity.pair (EncodedCNF.encode F) t)
      (EncodedComplexity.pair (EncodedCNF.encode F) (t.take (cutLen F))) (frontTime F) := by
  have h1 := Paper2.AEth2.Cut.cut_outputs_gen innerMachine 1 1 (fun _ => fOut F)
    (fun _ => innerTime F) (EncodedCNF.encode F) (inner_outputs F) t
  have hL : 1 * ((fOut F).length + 1) ^ 1 = cutLen F := by simp [cutLen]
  simp only [hL] at h1
  have hF : Fst.machine.OutputsWithin (fOut F) (EncodedCNF.encode F)
      (2 * (EncodedCNF.encode F).length + 3) :=
    Fst.machine_outputs (EncodedCNF.encode F) _
  have h2 := Paper2.Unit4Shell.PairMap.machine_outputs (M := Fst.machine) (fOut F)
    (EncodedCNF.encode F) (t.take (cutLen F)) _ hF
  have hC := BitMachineComposition.composition_outputsWithin _ _ h1 h2
  refine BitMachine.outputsWithin_mono _ hC ?_
  have htk : (t.take (cutLen F)).length ≤ cutLen F := List.length_take_le _ _
  simp only [frontTime, EncodedComplexity.pair_length]
  omega

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- **Numeric fit at `m = N`.** For constants `K p` there is `N₀` such that for `N ≥ N₀` and every
`n ≤ N·⌈log₂(N+2)⌉^p`: `(n+2)^(K·(kOf N + 1)) ≤ expLen N` (the a-eth-owner-1 numeric core
`Paper2.AEth.budget_numeric` at `m = N`). -/
theorem bits_fit (K p : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n, n ≤ N * Nat.clog 2 (N + 2) ^ p →
      (n + 2) ^ (K * (kOf N + 1)) ≤ Paper2.AEth.expLen N := by
  obtain ⟨N₀, h⟩ := Paper2.AEth.budget_numeric K p
  refine ⟨N₀, fun N hN n hn => h N hN n N hn le_rfl ?_⟩
  calc N ≤ N + 2 := by omega
    _ = (N + 2) ^ 1 := (pow_one _).symm
    _ ≤ (N + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)

/-- **The reduction's random bits fit below the cut request.** For every density `cs` there is
`N₀` such that for every sparse valid `Φ` with `N ≥ N₀`: `1 ≤ kOf N` and the selected T24
experiment at `k = kOf N` uses at most `expLen N` random bits. -/
theorem inputBits_fit (cs : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables → 1 ≤ kOf Φ.val.variables ∧
      (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).inputBits ≤
      Paper2.AEth.expLen Φ.val.variables := by
  obtain ⟨N₁, hN₁⟩ := bits_fit 160 (D.sizeExponent + 2)
  refine ⟨max N₁ (max 36
    (2 ^ (2 ^ (D.sizeExponent + 1) * Paper2.Unit4Shell.T10Size.t45C D B cs))), ?_⟩
  intro Φ hsp hN
  have h1 : N₁ ≤ Φ.val.variables := le_trans (le_max_left _ _) hN
  have h2 : 36 ≤ Φ.val.variables := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have h4 : 2 ^ (2 ^ (D.sizeExponent + 1) * Paper2.Unit4Shell.T10Size.t45C D B cs) ≤
      Φ.val.variables := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hk1 : 1 ≤ kOf Φ.val.variables := Paper2.Unit4Shell.AsymptoticsExplicit.kOf_pos _ h2
  have hbits := Paper2.Unit4Shell.RandomBits.inputBits_le_resource D B Φ (kOf Φ.val.variables) hk1
  have hsize := Paper2.Unit4Shell.T10Size.t45_shell_form D B cs Φ hsp h4
  exact ⟨hk1, le_trans hbits (hN₁ Φ.val.variables h1 _ hsize)⟩

end Paper2.AEth3

#print axioms Paper2.AEth3.Mu_outputs
#print axioms Paper2.AEth3.inner_outputs
#print axioms Paper2.AEth3.cutLen_ge
#print axioms Paper2.AEth3.frontCut_outputs
#print axioms Paper2.AEth3.bits_fit
#print axioms Paper2.AEth3.inputBits_fit
