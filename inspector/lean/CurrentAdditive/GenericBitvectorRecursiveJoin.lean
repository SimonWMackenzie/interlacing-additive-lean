import CurrentAdditive.GenericBitvectorPhysicalEntry
import Paper2.RLoopCanonLoop
import Paper2.SeedEntryMachine

/-! A single seed-shaped recursive evaluator: the actual graph request loop
is followed by a physical lookup in supplied base-table bytes. It is scoped
to the `(Fin p → Bool) × Fin p` base carrier used by `RLoop`; no claim is made
for arbitrary `Fin nr × Fin nc` bases or for the separate CodeD successor. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.GenericBitvectorRecursiveJoin

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
open Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries
open Paper2.RLoop
open Paper2.TemplateStep (r1)
open Paper2.SourceProfileParameters

abbrev Bank := JL ⊕ Fin 12
abbrev LoopLabel := Unit ⊕ (type_of% bodyStart)
abbrev LoopControl := Option Bool × (type_of% bodyCtl)

def loopι : JL ↪ Bank := ⟨Sum.inl, Sum.inl_injective⟩

def baseιFun : Fin 14 → Bank :=
  ![.inl (jC (r1 RequestSelect.Xc)), .inr 0, .inr 1, .inr 2, .inr 3,
    .inl (jC (r1 RequestSelect.Yc)), .inr 4, .inr 5, .inr 6, .inr 7,
    .inr 8, .inr 9, .inr 10, .inr 11]

theorem baseιFun_injective : Function.Injective baseιFun := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    first
    | rfl
    | (simp [baseιFun, jC, r1, RequestSelect.Xc, RequestSelect.Yc] at h)

def baseι : Fin 14 ↪ Bank := ⟨baseιFun, baseιFun_injective⟩

def extra (p : ℕ) (bits : List Bool) : Fin 12 → List Bool :=
  ![[], [], [], [], List.replicate (p + 1) true, bits,
    [], [], [], [], [], []]

def rowBank (p : ℕ) (bits : List Bool)
    (x : Fin p → Bool) (y : Fin p) : Fin 14 → List Bool :=
  ![List.ofFn x, [], [], [], [], (finCodec p).encode y,
    List.replicate (p + 1) true, bits, [], [], [], [], [], []]

def loopProgram := fun l => stackStmt loopι (rloop l)
def baseProgram := fun l => stackStmt baseι
  (GenericBitvectorPhysicalEntry.program l)

def program := BitMachineRawSequence.program loopProgram baseProgram
  GenericBitvectorPhysicalEntry.start ((none : Option Bool), bodyCtl)
  GenericBitvectorPhysicalEntry.initial

def baseBound (p : ℕ) (F : (Fin p → Bool) → Fin p → Bool)
    (x : Fin p → Bool) (y : Fin p) : ℕ :=
  let row := List.ofFn x
  let col := (finCodec p).encode y
  let bits := GenericBitvectorPaddedTable.paddedBits p F
  2 * row.length + 2 + MatrixBinaryAddress.workFrom 0 row + 1 +
    (2 * col.length + 2) + 1 +
    32 * (MatrixBinaryAddress.valueFrom 0 row + (p + 1) + col.length +
      bits.length + 1) ^ 2 + 1

theorem lift_base_run (p : ℕ)
    (F : (Fin p → Bool) → Fin p → Bool)
    (x : Fin p → Bool) (y : Fin p)
    (B : JL → List Bool)
    (hx : B (jC (r1 RequestSelect.Xc)) = List.ofFn x)
    (hy : B (jC (r1 RequestSelect.Yc)) = (finCodec p).encode y) :
    let bits := GenericBitvectorPaddedTable.paddedBits p F
    let S : Bank → List Bool := Sum.elim B (extra p bits)
    let T := Function.update
      (Function.update
        (Function.update (rowBank p bits x y) 1
          (List.replicate (MatrixBinaryAddress.valueFrom 0 (List.ofFn x)) true))
        8 (List.replicate ((finCodec p).encode y).length true)) 11 [F x y]
    ∃ t ≤ baseBound p F x y,
      ((advance baseProgram)^[t])
        (⟨some GenericBitvectorPhysicalEntry.start,
          GenericBitvectorPhysicalEntry.initial, S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, GenericBitvectorPhysicalEntry.initial, bank baseι S T⟩ := by
  intro bits S T
  obtain ⟨t, ht, hr⟩ := GenericBitvectorPhysicalEntry.supplied_entry p F x y
  change t ≤ baseBound p F x y at ht
  change ((advance GenericBitvectorPhysicalEntry.program)^[t])
    (⟨some GenericBitvectorPhysicalEntry.start,
      GenericBitvectorPhysicalEntry.initial, rowBank p bits x y⟩ :
      TM2.Cfg (fun _ : Fin 14 => Bool) _ _) =
    ⟨none, GenericBitvectorPhysicalEntry.initial, T⟩ at hr
  have hcells : ∀ k, (rowBank p bits x y) k = S (baseι k) := by
    intro k
    fin_cases k <;>
      simp [rowBank, S, extra, baseι, baseιFun, hx, hy]
  have hs := BitMachineStackRun.run baseι S
    GenericBitvectorPhysicalEntry.program
    (⟨some GenericBitvectorPhysicalEntry.start,
      GenericBitvectorPhysicalEntry.initial, rowBank p bits x y⟩ :
      TM2.Cfg (fun _ : Fin 14 => Bool) _ _) t
  rw [hr] at hs
  have hstart : stackCfg baseι S
      (⟨some GenericBitvectorPhysicalEntry.start,
        GenericBitvectorPhysicalEntry.initial, rowBank p bits x y⟩ :
        TM2.Cfg (fun _ : Fin 14 => Bool) _ _) =
      (⟨some GenericBitvectorPhysicalEntry.start,
        GenericBitvectorPhysicalEntry.initial, S⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) := by
    simp only [stackCfg]
    congr 1
    exact bank_eq_self baseι S _ hcells
  rw [hstart] at hs
  exact ⟨t, ht, by simpa only [baseProgram, stackCfg] using hs⟩

theorem loop_bank (A B : JL → List Bool) (E : Fin 12 → List Bool) :
    bank loopι (Sum.elim A E) B = Sum.elim B E := by
  funext z
  rcases z with j | e
  · exact bank_at loopι (Sum.elim A E) B j
  · exact bank_outside loopι (Sum.elim A E) B (.inr e)
      (by rintro ⟨j, h⟩; cases h)

theorem recursive_entry (L w Q r : ℕ)
    (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] (hn : 0 < g.vertices) (hw : 0 < w) (hQ : 0 < Q)
    [NeZero (width L)] [NeZero (width L - 2)]
    [NeZero (outerWidth L)] [NeZero w] [NeZero Q]
    (hq : outerWidth L = SourceItems.sourceQ0
      (Fin (4 * width L)) (Fin g.edges.length) * r)
    (F : (Fin (LookupSeed.width L) → Bool) →
      Fin (LookupSeed.width L) → Bool)
    (K : ℕ)
    (x : Row (Fin (LookupSeed.width L) → Bool)
      (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices))
      (width L) (width L - 2) (outerWidth L) w Q K)
    (y : Column (Fin (LookupSeed.width L) → Bool)
      (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices))
      (width L) (width L - 2) (outerWidth L) w Q K) :
    let p := LookupSeed.width L
    let ξ := CanonicalDefaultSource.canonicalDefaultTails
      L g.vertices w Q hn hw hQ
    let activity := SourceActiveRank.scanAtCanonical
      (CanonicalEdgeTape.graphEdge g hg)
      (by have := SourceProfiles.width_ge_four L; omega) hq
    let sd := RecursiveEntries.seedRequest activity ξ K x y
    let bits := GenericBitvectorPaddedTable.paddedBits p F
    let S : Bank → List Bool := Sum.elim (bankL g r K x y) (extra p bits)
    ∃ t ≤ K * (loopBd g hg (SourceProfiles.width_ge_four L)
        r hq ξ K x y + 2) + 1 + baseBound p F sd.1 sd.2 + 1,
      ∃ v, ∃ B : Bank → List Bool,
        ((advance program)^[t])
          (⟨some (BitMachineRawSequence.leftLabel (.inl ())),
            (((none : Option Bool), bodyCtl),
              GenericBitvectorPhysicalEntry.initial), S⟩ :
            TM2.Cfg (fun _ : Bank => Bool) _ _) =
          ⟨none, v, B⟩ ∧
        B (baseι 11) =
          [RecursiveEntries.matrix F activity ξ K x y] := by
  intro p ξ activity sd bits S
  let B0 := bankL (n := g.vertices) (p := p) (s := width L)
    (q₁ := width L - 2) (q₂ := outerWidth L) (w := w) (Q := Q)
    g r 0 sd.1 sd.2
  let S0 : Bank → List Bool := Sum.elim B0 (extra p bits)
  obtain ⟨ta, hta, ca, hra⟩ :=
    RLoopCanonLoop.request_loop_canonical L w Q r g hg hn hw hQ hq
      K x y ((none : Option Bool), bodyCtl)
  have hloop := BitMachineStackRun.run loopι S rloop
    (⟨some (Sum.inl ()), ((none : Option Bool), bodyCtl), bankL g r K x y⟩ :
      TM2.Cfg (fun _ : JL => Bool) LoopLabel LoopControl) ta
  rw [hra] at hloop
  have hstart : stackCfg loopι S
      (⟨some (Sum.inl ()), ((none : Option Bool), bodyCtl), bankL g r K x y⟩ :
        TM2.Cfg (fun _ : JL => Bool) LoopLabel LoopControl) =
      (⟨some (Sum.inl ()), ((none : Option Bool), bodyCtl), S⟩ :
        TM2.Cfg (fun _ : Bank => Bool) LoopLabel LoopControl) := by
    have hbank := bank_eq_self loopι S (bankL g r K x y) (fun _ => rfl)
    exact congrArg (fun T : Bank → List Bool =>
      (⟨some (Sum.inl ()), ((none : Option Bool), bodyCtl), T⟩ :
        TM2.Cfg (fun _ : Bank => Bool) LoopLabel LoopControl)) hbank
  rw [hstart] at hloop
  have hend : bank loopι S B0 = S0 := by
    simpa only [S, S0] using
      loop_bank (bankL g r K x y) B0 (extra p bits)
  have hexit : stackCfg loopι S (⟨none, ca, B0⟩ :
      TM2.Cfg (fun _ : JL => Bool) LoopLabel LoopControl) =
      (⟨none, ca, S0⟩ : TM2.Cfg (fun _ : Bank => Bool) LoopLabel LoopControl) := by
    exact congrArg (fun T : Bank → List Bool =>
      (⟨none, ca, T⟩ : TM2.Cfg (fun _ : Bank => Bool) LoopLabel LoopControl)) hend
  change _ = stackCfg loopι S (⟨none, ca, B0⟩ :
    TM2.Cfg (fun _ : JL => Bool) LoopLabel LoopControl) at hloop
  rw [hexit] at hloop
  have hx : B0 (jC (r1 RequestSelect.Xc)) = List.ofFn sd.1 := by
    change (piCodec boolCodec p).encode sd.1 = List.ofFn sd.1
    exact SeedEntryMachine.bool_pi_encode p sd.1
  have hy : B0 (jC (r1 RequestSelect.Yc)) = (finCodec p).encode sd.2 := rfl
  obtain ⟨tb, htb, hrb⟩ := lift_base_run p F sd.1 sd.2 B0 hx hy
  change ((advance baseProgram)^[tb])
    (⟨some GenericBitvectorPhysicalEntry.start,
      GenericBitvectorPhysicalEntry.initial, S0⟩ :
      TM2.Cfg (fun _ : Bank => Bool) _ _) = _ at hrb
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    loopProgram baseProgram (Sum.inl ()) GenericBitvectorPhysicalEntry.start
    ((none : Option Bool), bodyCtl) ca
    GenericBitvectorPhysicalEntry.initial GenericBitvectorPhysicalEntry.initial
    S S0 _ ta tb hloop hrb
  change ta ≤ K * (loopBd g hg (SourceProfiles.width_ge_four L)
    r hq ξ K x y + 2) + 1 at hta
  refine ⟨t, by omega, _, _, by simpa only [program] using hrun, ?_⟩
  have hanswer :
      (bank baseι S0 (Function.update
        (Function.update
          (Function.update (rowBank p bits sd.1 sd.2) 1
            (List.replicate
              (MatrixBinaryAddress.valueFrom 0 (List.ofFn sd.1)) true))
          8 (List.replicate ((finCodec p).encode sd.2).length true))
        11 [F sd.1 sd.2])) (baseι 11) = [F sd.1 sd.2] := by
    rw [bank_at]
    simp
  rw [hanswer]
  exact congrArg List.singleton
    (RecursiveEntries.evaluate_eq_seed_entry F activity ξ K x y |>.symm.trans
      (RecursiveEntries.evaluate_eq_matrix F activity ξ K x y))

#print axioms lift_base_run
#print axioms recursive_entry

end

end Paper2.GenericBitvectorRecursiveJoin
