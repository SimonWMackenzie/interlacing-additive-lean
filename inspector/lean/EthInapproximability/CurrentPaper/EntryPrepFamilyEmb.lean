import EthInapproximability.CurrentPaper.EntryPrepFamilyGrow

/-!
# Lane owner:b-stage4-entry-program-8: the re-run workspace (A3, reuse reading)

The workspace of the level-controller re-run is the stack `EntryFamilyLevel.Stack =
WeightedLevelColumnSave.Stack ⊕ EntryFamilyAssembly.ACell` (260 + 61 = 321 cells). Only 176
known-blank non-writer cells lie outside the tail region, so the workspace REUSES tail-region
cells that are structurally blank at `midBank4`: the 217 `Rest` cells of the entry bank (every
entry-bank cell other than the 19 common words; `EntryRunsRaw.cellBank` is `[]` there for EVERY
word record). `Free = Rest ⊕ Out` (217 + 176 = 393 cells), `fmap : Free → HStack` injective,
every image blank at `midBank4` (`mid4_free`), never a common-word tail cell, a level-writer
cell or a raw master `C, B, Y, E, Gw`.

`FamIdx = LS ⊕ (Fin 28 ⊕ (PrimeFromWords.Stack ⊕ Fin 5))` (card 321) codes the workspace
(`enc`, injective: explicit codes for the 28 `FamilyRowBody.Cell` and 5 `EntryFamilyAssembly.X`
constructors, which have no `Fintype` instance); `emb0 : FamIdx ↪ Free` is ONE fixed classical
embedding (card 321 ≤ 393, the same kind of fixed choice as the admitted `regionEmb0`);
`ι = fmap ∘ emb0 ∘ enc`. `cellsF` enumerates the 321 cells `fmap (emb0 x)` for the clear.
-/

namespace EthInapproximability.CurrentPaper.EntryPrepFamily

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy EntryPrepVec

abbrev Rest := EntryRunsRaw.Rest

/-- Tail index of the entry-bank cell `r` (not a common word). -/
noncomputable def rj (r : Rest) : TSt := .inl (.inl (.inl (EntryRunsRaw.eo (.inr r))))

abbrev Free := Rest ⊕ Out

noncomputable def fmap : Free → HStack
  | .inl r => tailEmb (rj r)
  | .inr o => nwMap o.1

theorem fmap_inj : Function.Injective fmap := by
  intro a b h
  rcases a with r | o <;> rcases b with r' | o'
  · have h1 := tailEmb.injective h
    simp only [rj, Sum.inl.injEq, EmbeddingLike.apply_eq_iff_eq] at h1
    rw [Sum.inr.inj h1]
  · exact absurd ⟨_, nwMap_inj h⟩ o'.2
  · exact absurd ⟨_, (nwMap_inj h).symm⟩ o.2
  · exact congrArg Sum.inr (Subtype.ext (nwMap_inj h))

theorem fmap_ne_tj (f : Free) (i : Fin 19) : fmap f ≠ tailEmb (tj i) := by
  rcases f with r | o
  · intro h
    have h1 := tailEmb.injective h
    simp [rj, tj] at h1
  · intro h
    exact o.2 ⟨_, (nwMap_inj h).symm⟩

theorem fmap_ne_wj (f : Free) (k : Fin 64) : fmap f ≠ tailEmb (wj k) := by
  rcases f with r | o
  · intro h
    have h1 := tailEmb.injective h
    simp [rj, wj] at h1
  · exact nwMap_ne_wcell _ k

theorem nwMap_ne_m (z : NWIdx) (a : WeightedRawWords.Aux)
    (ha : a = .C ∨ a = .B ∨ a = .Y ∨ a = .E ∨ a = .Gw) : nwMap z ≠ mcell a := by
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
  · rcases z with x | r
    · intro h; cases h
    · rcases r with y | u | d | j | u | i | i | e <;> intro h <;> cases h

theorem fmap_ne_m (f : Free) (a : WeightedRawWords.Aux)
    (ha : a = .C ∨ a = .B ∨ a = .Y ∨ a = .E ∨ a = .Gw) : fmap f ≠ mcell a := by
  rcases f with r | o
  · exact nwMap_ne_m _ a ha
  · exact nwMap_ne_m _ a ha

theorem tail_ne_m (j : TSt) (a : WeightedRawWords.Aux)
    (ha : a = .C ∨ a = .B ∨ a = .Y ∨ a = .E ∨ a = .Gw) : tailEmb j ≠ mcell a := by
  rcases j with x | k | i
  · exact nwMap_ne_m _ a ha
  · intro h; cases h
  · exact nwMap_ne_m _ a ha

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem mid4_tail (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (j : TSt) :
    midBank4 Mm G n c F Q P (tailEmb j) =
      RawTableTail.startBank (EntryRunsRaw.cellBank (wMid4 G n c)) (r0 G n c) (c0 G n c)
        (Wlvl Mm G n c F Q P) j := by
  unfold midBank4
  rw [bank_at]

theorem mid4_free (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (f : Free) : midBank4 Mm G n c F Q P (fmap f) = [] := by
  rcases f with r | o
  · show midBank4 Mm G n c F Q P (tailEmb (rj r)) = []
    rw [mid4_tail]
    simp only [rj, RawTableTail.startBank, RawTableTail.glob, MatrixTableWriter.Data.contents,
      MatrixTableWriter.Data.cell, MatrixTableWriter.ready, EntryRunsRaw.cellBank, Sum.elim_inl,
      Equiv.symm_apply_apply, Sum.elim_inr]
  · show midBank4 Mm G n c F Q P (nwMap o.1) = []
    unfold midBank4
    rw [bank_outside _ _ _ _ (fun ⟨j, hj⟩ => by
      rcases j with x | k | i
      · exact o.2 ⟨_, nwMap_inj hj⟩
      · exact nwMap_ne_wcell _ k hj.symm
      · exact o.2 ⟨_, nwMap_inj hj⟩)]
    exact exit_blank_nw Mm G n c F Q P _

theorem mid4_master (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (a : WeightedRawWords.Aux) (ha : a = .C ∨ a = .B ∨ a = .Y ∨ a = .E ∨ a = .Gw) :
    midBank4 Mm G n c F Q P (mcell a) = WeightedLevel0Rows.masterC Mm G n c a := by
  unfold midBank4
  rw [bank_outside _ _ _ _ (fun ⟨j, hj⟩ => tail_ne_m j a ha hj)]
  show G4 (level0RowsBank Mm G n c F Q P) (Sum.inl (mc a)) = _
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact WeightedLevel0Masters.ready_master Mm G n c F Q P .C (by decide) (by decide)
      (fun m h => by cases h)
  · exact WeightedLevel0Masters.ready_master Mm G n c F Q P .B (by decide) (by decide)
      (fun m h => by cases h)
  · exact WeightedLevel0Masters.ready_master Mm G n c F Q P .Y (by decide) (by decide)
      (fun m h => by cases h)
  · exact WeightedLevel0Masters.ready_master Mm G n c F Q P .E (by decide) (by decide)
      (fun m h => by cases h)
  · exact WeightedLevel0Masters.ready_master Mm G n c F Q P .Gw (by decide) (by decide)
      (fun m h => by cases h)

/-! ## The workspace code -/

def cellCode : FamilyRowBody.Cell → Fin 28
  | .cnt => 0 | .prime => 1 | .order => 2 | .q => 3 | .rx => 4 | .w => 5 | .m => 6
  | .x => 7 | .dcount => 8 | .dsaved => 9 | .cs => 10
  | .e i => ⟨11 + i.val, by omega⟩
  | .quo => 22 | .rem => 23 | .wc => 24 | .sv => 25 | .first => 26 | .row => 27

theorem cellCode_inj : Function.Injective cellCode := by
  intro a b h
  have h' := congrArg Fin.val h
  cases a <;> cases b <;> simp [cellCode] at h' <;>
    first | rfl | omega | exact congrArg _ h' | exact congrArg _ (Fin.ext h') |
      exact congrArg _ (Fin.ext (by omega))

def xCode : EntryFamilyAssembly.X → Fin 5
  | .a => 0 | .L => 1 | .s0 => 2 | .s1 => 3 | .s2 => 4

theorem xCode_inj : Function.Injective xCode := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [xCode] at h)

abbrev FamIdx := WeightedLevelColumnSave.Stack ⊕ (Fin 28 ⊕ (PrimeFromWords.Stack ⊕ Fin 5))

def enc : EntryFamilyLevel.Stack → FamIdx
  | .inl j => .inl j
  | .inr (.inl c) => .inr (.inl (cellCode c))
  | .inr (.inr (.inl k)) => .inr (.inr (.inl k))
  | .inr (.inr (.inr x)) => .inr (.inr (.inr (xCode x)))

theorem enc_inj : Function.Injective enc := by
  intro a b h
  rcases a with j | c | k | x <;> rcases b with j' | c' | k' | x' <;>
    simp only [enc, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
  · rw [h]
  · rw [cellCode_inj h]
  · rw [h]
  · rw [xCode_inj h]

theorem card_rest : Fintype.card Rest = 217 := by
  simp only [Rest, EntryRunsRaw.Rest, Fintype.card_sum, Fintype.card_fin]

theorem card_famIdx : Fintype.card FamIdx = 321 := by
  rw [Fintype.card_sum, card_LS, Fintype.card_sum, Fintype.card_fin, Fintype.card_sum, card_prime,
    Fintype.card_fin]

theorem card_free : Fintype.card Free = 393 := by
  rw [Fintype.card_sum, card_rest, card_Out]

theorem card_le : Fintype.card FamIdx ≤ Fintype.card Free := by
  rw [card_famIdx, card_free]; decide

/-- ONE fixed classical placement of the workspace code into the free cells. -/
noncomputable def emb0 : FamIdx ↪ Free :=
  Classical.choice (Function.Embedding.nonempty_of_card_le card_le)

/-- The workspace embedding. -/
noncomputable def ι : EntryFamilyLevel.Stack ↪ HStack :=
  ⟨fun x => fmap (emb0 (enc x)), fun a b h => enc_inj (emb0.injective (fmap_inj h))⟩

theorem ι_apply (x : EntryFamilyLevel.Stack) : ι x = fmap (emb0 (enc x)) := rfl

noncomputable def nF : ℕ := Fintype.card FamIdx
noncomputable def cellsF (i : Fin nF) : HStack := fmap (emb0 ((Fintype.equivFin FamIdx).symm i))

theorem cellsF_inj : Function.Injective cellsF :=
  fun a b h => (Fintype.equivFin FamIdx).symm.injective (emb0.injective (fmap_inj h))

theorem ι_mem (x : EntryFamilyLevel.Stack) : ∃ i, cellsF i = ι x :=
  ⟨Fintype.equivFin FamIdx (enc x), by simp [cellsF, ι_apply]⟩

#print axioms fmap_inj
#print axioms mid4_free
#print axioms mid4_master
#print axioms enc_inj
#print axioms card_le
#print axioms ι_mem

end EthInapproximability.CurrentPaper.EntryPrepFamily
