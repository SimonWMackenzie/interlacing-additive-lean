import EthInapproximability.CurrentPaper.G5bRoundClockNamed
import EthInapproximability.CurrentPaper.KShell
import EthInapproximability.CurrentPaper.EntryPrepFamilyComposeJ

/-!
# The arbitrary-`k` physical shell: named premises of `KShell.shell_run`
(private lane owner:b-g5-3; a copy of the frozen `b-g5-owner-2/G5bShellNamed.lean` under a NEW
module name and namespace, with the docstring corrected (audit finding F1); the Lean text below the
docstring is unchanged apart from the namespace name)

For ARBITRARY `k` and ARBITRARY `p ≥ clog(n+2)`, if every round level `1 ≤ j < k` of the
physical run satisfies the named premise `LevelNamed` (the source names of that level record, the
output carrier names, and the next-state names), then `shell_premises_named` gives the two
premises `hW` (through the admitted `EntryPrepFamilyJ.kshell_hW_F`) and `hT` of the admitted
`KShell.shell_run` with the ONE writer clock `Tw = (n + |enc G| + 2)^Cw + 2^(Cw p)` and the ONE
round clock `T = Tw + roundRest (|enc G|) p`.

EXACT proved clock (no more is claimed here). Fed to `KShell.shell_run`, the shell run is bounded
by
  `level0BoundP + installBoundP 0 + 1 + ((k - 1) * (T + 1) + 1) + 1`,
  `T = (n + |enc G| + 2)^Cw + 2^(Cw p) + roundRest(|enc G|, p)`,
i.e. `(k - 1) * (poly(n, |enc G|) + 2^{O(p)})`: a PRODUCT of `k - 1` with terms polynomial in
`|enc G|` (`roundRest` contains `(800(|enc G|+1)+2)^C`, `|enc G|^18`,
`(|enc G| + 205*2^(4p) + 1)^9`, `(3*2^p + 2|enc G| + 7)^2`). This is NOT by itself the lock's
additive shape `(n + |enc G| + 1)^{O(1)} + (k+1) 2^{O(p)}`; the additive round part is derived
in `G5cAdditiveClock` only under the extra premise `|enc G| + 1 ≤ (n+2)^D` (fixed `D`), which is
stated there. The level-0 part (`level0BoundP` with its writer spec `hW₀`) is not bounded here.
The constants `Cw C ps ps3 K` are quantified BEFORE the clock machine `M` and the vertex/edge
types (uniform).

NOT claimed: producing the `k-1` fuel or `p` from an input; the parser; the padding join; `y_k`
emission; the level-0 named bound; any total machine for `thm:paper-materialization`.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5cShellNamed

open Turing EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EntryClockPoly3 ActualOrderFromCarrier

/-- The named premise at round level `j` of the physical run (`b` the source depth). -/
def LevelNamed {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (c b j p : ℕ) : Prop :=
  SourceNames ⟨V, E, G, c, b, StepP.yP G c b j, j, StepP.MP G c b j⟩ p ∧
  Nat.clog 2 (Iteration.step G c b (StepP.yP G c b j) j (StepP.MP G c b j)).rows ≤ p ∧
  Nat.clog 2 (Iteration.step G c b (StepP.yP G c b j) j (StepP.MP G c b j)).columns ≤ p ∧
  Nat.clog 2 c ≤ p ∧ b ≤ p ∧
  Nat.clog 2 ((PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).budget +
    (j + 1)) ≤ p ∧
  Nat.clog 2 (PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).matrix.rows ≤ p ∧
  Nat.clog 2 (PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).matrix.columns ≤ p

theorem shell_premises_named [Fintype OuterLevel0Bridge.BStack]
    [Fintype MatrixTableInterlaceProtectedBridge.Label] :
    ∃ Cw C ps ps3 K : ℕ, ∀ (M : BitMachine.Machine) {V E : Type} [Fintype V] [DecidableEq V]
      [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (n c k p : ℕ),
      1 ≤ c → Nat.clog 2 (n + 2) ≤ p →
      (∀ j, 1 ≤ j → j < k → LevelNamed G c (EffectiveIteration.sourceDepth n) j p) →
      (∀ j, 1 ≤ j → j < k →
        EntryWriter22J.writerBound_j G c (EffectiveIteration.sourceDepth n)
          (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
          (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
          (EntryPrepFamilyJ.TFJ G c (EffectiveIteration.sourceDepth n)
            (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
            (StepP.MP G c (EffectiveIteration.sourceDepth n) j)) ≤
        (n + ell3 G + 2) ^ Cw + 2 ^ (Cw * p)) ∧
      (∀ j, 1 ≤ j → j < k →
        StepP.roundBoundP G c (EffectiveIteration.sourceDepth n) j (Level0Install.mb1 M G n c)
            (MatrixMaterialization.rowMajor
              (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry)
            ((n + ell3 G + 2) ^ Cw + 2 ^ (Cw * p)) +
          StepP.installBoundP G c (EffectiveIteration.sourceDepth n) j + 1 ≤
        ((n + ell3 G + 2) ^ Cw + 2 ^ (Cw * p)) +
          G5bRoundClockNamed.roundRest C ps ps3 K (ell3 G) p) := by
  obtain ⟨Cw, hW⟩ := ActualWriterClock.writer_full_clock_source
  obtain ⟨C, ps, ps3, K, hR⟩ := G5bRoundClockNamed.round_named
  refine ⟨Cw, C, ps, ps3, K, fun M {V E} _ _ _ _ G n c k p hc hfloor hnamed => ⟨?_, ?_⟩⟩
  · intro j hj1 hjk
    obtain ⟨h, -⟩ := hnamed j hj1 hjk
    exact hW ⟨V, E, G, c, EffectiveIteration.sourceDepth n,
      StepP.yP G c (EffectiveIteration.sourceDepth n) j, j,
      StepP.MP G c (EffectiveIteration.sourceDepth n) j⟩ n p hfloor h
  · intro j hj1 hjk
    obtain ⟨h, hrows, hcols, hcc, hb, hy, hr, hcol⟩ := hnamed j hj1 hjk
    have hN : Level0Install.mb1 M G n c .N = [] := by simp [Level0Install.mb1]
    exact hR G c (EffectiveIteration.sourceDepth n) j p _ (Level0Install.mb1 M G n c) hc hN h
      hrows hcols hcc hb hy hr hcol

#print axioms shell_premises_named

end EthInapproximability.CurrentPaper.G5cShellNamed
