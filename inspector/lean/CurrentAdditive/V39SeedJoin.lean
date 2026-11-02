import CurrentAdditive.V39RLoop
import Paper2.SeedEntryMachine

/-! Unit 3, segment (3): the seed join. ONE fixed program
`entryProg = BitMachineRawSequence.program rloop seedL`: the k-fold request loop,
then (one charged handoff) the frozen `SeedEntryMachine.program` (private lane
`a-seed-entry-machine`, hash-verified) placed on the loop bank with its row cell =
`r1 Xc` and its column cell = `r1 Yc` (the level-0 pair words left by the loop),
its answer cell and scratch on blank `r2` vector cells. The run ends with the one-bit
word `[V39RecursiveTable.matrix activity K x y]` in the answer
cell and every other cell equal to the level-0 loop bank. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39RLoop

noncomputable section

open Paper2
open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries
open BitMachineRawSequence (leftLabel)
open Paper2.TemplateStep (J RS nC r1 r2)

/-- A blank vector cell of the second request bank. -/
def rv (q : Fin 8) : JL := jC (r2 (.inr (.inr q)))

def ιSf : Fin 9 → JL :=
  ![rv 0, rv 1, rv 2, jC (r1 RequestSelect.Xc), rv 3, rv 4, rv 5, jC (r1 RequestSelect.Yc), rv 6]

theorem ιSf_injective : Function.Injective ιSf := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    first
    | rfl
    | (simp [ιSf, rv, jC, r1, r2, RequestSelect.Xc, RequestSelect.Yc] at h)

def ιS : Fin 9 ↪ JL := ⟨ιSf, ιSf_injective⟩

/-- The answer cell. -/
def ansC : JL := rv 4

def seedL := fun l => stackStmt ιS (SeedEntryMachine.program l)

/-- Loop, then seed lookup: ONE fixed program. -/
def entryProg := BitMachineRawSequence.program rloop seedL (.inl .scan)
  ((none : Option Bool), bodyCtl) (SeedEntryMachine.readInitial, (none : Option Bool))

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

theorem seed_join (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K : ℕ)
    (x : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (y : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    let activity := V39EdgeSourceFront.edgeActivity g hg (by omega) r hq
    let sd := V39RecursiveTable.seedRequest activity K x y
    ∃ t ≤ K * (loopBd g hg hs r hq ξ K x y + 2) + 1 + (9 * p + 13) + 1, ∃ v,
      ((advance entryProg)^[t])
        (⟨some (leftLabel (.inl ())),
          (((none : Option Bool), bodyCtl), (SeedEntryMachine.readInitial, (none : Option Bool))),
          bankCurrent g r K x y⟩ : TM2.Cfg (fun _ : JL => Bool) _ _) =
        ⟨none, v, Function.update
          (bankCurrent (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
            g r 0 sd.1 sd.2) ansC
          [V39RecursiveTable.matrix activity K x y]⟩ := by
  intro activity sd
  obtain ⟨t1, ht1, c1, r1run⟩ := request_loop g hg hp hs r hq ξ K x y ((none : Option Bool), bodyCtl)
  set B0 := bankCurrent (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    g r 0 sd.1 sd.2 with hB0
  obtain ⟨t2, ht2, r2run⟩ := SeedEntryMachine.run_encoded_pair p sd.1 sd.2
  have hS : ∀ i : Fin 9, (![[], [], [], (piCodec boolCodec p).encode sd.1, [], [], [],
      (finCodec p).encode sd.2, []] : Fin 9 → List Bool) i = B0 (ιS i) := by
    intro i
    fin_cases i <;> rfl
  have r2L := liftL ιS SeedEntryMachine.program B0 _ _ hS _ _ _ _ r2run
  obtain ⟨u, hu, hrun⟩ := BitMachineRawSequence.runs rloop seedL (.inl ()) (.inl .scan)
    ((none : Option Bool), bodyCtl) c1 (SeedEntryMachine.readInitial, (none : Option Bool))
    (SeedEntryMachine.readInitial, (none : Option Bool)) (bankCurrent g r K x y) B0 _ t1 t2 r1run r2L
  refine ⟨u, by omega, (((none : Option Bool), bodyCtl), (SeedEntryMachine.readInitial, (none : Option Bool))), ?_⟩
  refine hrun.trans ?_
  have hans : LookupSeed.matrix p sd.1 sd.2 =
      V39RecursiveTable.matrix activity K x y := by
    exact V39RecursiveTable.evaluate_eq_matrix activity K x y
  rw [← hans]
  congr 1
  funext a
  by_cases ha : ∃ i, ιS i = a
  · obtain ⟨i, rfl⟩ := ha
    rw [bank_at]
    fin_cases i
    all_goals first
      | (show _ = Function.update B0 (rv 4) _ (rv 4); rw [Function.update_self]; rfl)
      | (rw [Function.update_of_ne (by
            simp [ιS, ιSf, rv, ansC, jC, r1, r2, RequestSelect.Xc, RequestSelect.Yc])]; rfl)
  · rw [bank_outside ιS B0 _ a ha, Function.update_of_ne]
    rintro rfl
    exact ha ⟨5, rfl⟩

end

#print axioms ιSf_injective
#print axioms seed_join

end CurrentAdditive.V39RLoop
