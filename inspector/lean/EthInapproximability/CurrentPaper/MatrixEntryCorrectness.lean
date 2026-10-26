import EthInapproximability.CurrentPaper.MatrixEntryData

/-!
# Correctness of the complete finite matrix-entry program

Source: locked v8 Appendix B, `thm:paper-materialization`.
The proof follows physical preparation, finite dispatch, literal array
evaluation, and charged workspace cleanup. It does not assume an entry
oracle or a precomputed source/template branch.
-/

namespace EthInapproximability.CurrentPaper.MatrixEntryCorrectness

open Turing BitMachineEncoding
open MatrixEntryProgram
open MatrixEntryData

def preparationBound {N₂ n d N₁ : ℕ}
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁) : ℕ :=
  14 * (MatrixMaterialization.rowCode N₂ n r).val +
    66 * (MatrixMaterialization.columnCode d N₁ c).val +
    16 * N₂ + 12 * (d * N₁) + 12 * N₁ + 12 * d + 72

theorem preparation_run {N₂ n d N₁ : ℕ} (a : ℕ)
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁)
    (data : MatrixMaterialization.ExactBitData) (out : List Bool) :
    ∃ t ≤ preparationBound r c,
      run t (cfg (some start) initial
        (input a d N₁ N₂ (MatrixMaterialization.rowCode N₂ n r).val
          (MatrixMaterialization.columnCode d N₁ c).val data out)) =
      cfg (some .dispatch) (.prepare (MatrixEntryPreparation.preparedControl r c), none)
        (prepared a r c data out [] [] [] []) := by
  let S := input a d N₁ N₂ (MatrixMaterialization.rowCode N₂ n r).val
    (MatrixMaterialization.columnCode d N₁ c).val data out
  let v := MatrixEntryPreparation.inputData (MatrixMaterialization.rowCode N₂ n r).val
    (MatrixMaterialization.columnCode d N₁ c).val N₂ d N₁ []
  let localInput : MatrixEntryPreparation.Config :=
    ⟨some (.inl .scan), MatrixEntryPreparation.initialControl, v.contents⟩
  let localOutput : MatrixEntryPreparation.Config :=
    ⟨none, MatrixEntryPreparation.preparedControl r c,
      (MatrixEntryPreparation.preparedData v r c).contents⟩
  obtain ⟨k, hk, hr⟩ := MatrixEntryPreparation.prepare_run r
    (MatrixMaterialization.columnCode d N₁ c) []
  simp only [Equiv.symm_apply_apply] at hr
  change ((advance MatrixEntryPreparation.program)^[k]) localInput = localOutput at hr
  have hh : (((advance MatrixEntryPreparation.program)^[k]) localInput).l = none := by
    rw [hr]
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs preparationSlots S Label.prepare
    (fun v => (.prepare v, none)) getPreparation (fun _ => rfl) (some .dispatch)
    MatrixEntryPreparation.program program (fun _ => rfl) localInput k hh
  rw [hr] at he
  have hi : BitMachineStackEmbedding.cfg preparationSlots S Label.prepare
      (fun v => (.prepare v, none)) (some .dispatch) localInput =
      cfg (some start) initial S := by
    change (⟨_, _, BitMachineStackEmbedding.bank preparationSlots S v.contents⟩ : Config) = _
    rw [BitMachineStackEmbedding.bank_eq_self preparationSlots S v.contents (fun j =>
      (input_preparation a d N₁ N₂ _ _ data out j).symm)]
    rfl
  have ho : BitMachineStackEmbedding.cfg preparationSlots S Label.prepare
      (fun v => (.prepare v, none)) (some .dispatch) localOutput =
      cfg (some .dispatch) (.prepare (MatrixEntryPreparation.preparedControl r c), none)
        (prepared a r c data out [] [] [] []) := by
    change (⟨_, _, BitMachineStackEmbedding.bank preparationSlots S
      (MatrixEntryPreparation.preparedData v r c).contents⟩ : Config) = _
    rw [preparation_bank]
    rfl
  exact ⟨t, ht.trans hk, by simpa only [hi, ho, run] using he⟩

theorem dispatch_template {N₂ n d N₁ : ℕ} (p : Fin 4) (z : Fin N₂)
    (c : ExactConstruction.Columns d N₁) (S : Stack → List Bool) :
    run 2 (cfg (some .dispatch)
      (.prepare (MatrixEntryPreparation.preparedControl (n := n) (.inl (p,z)) c), none) S) =
      cfg (some (.template p MatrixTemplateEntry.start)) (.template MatrixTemplateEntry.base, none) S := rfl

theorem dispatch_source {N₂ n d N₁ : ℕ} (i : Fin n)
    (c : ExactConstruction.Columns d N₁) (S : Stack → List Bool) :
    let h := MatrixMaterializationMachine.header (decide (ExactConstruction.aligned c)) c.1
    run 2 (cfg (some .dispatch)
      (.prepare (MatrixEntryPreparation.preparedControl (N₂ := N₂) (.inr i) c), none) S) =
      cfg (some (.sourceCopy h .scan)) (.copy none, none) S := rfl

theorem source_initialize (h : Header) (S : Stack → List Bool) :
    run 1 (cfg (some (.sourceInit h)) (.copy none, none) S) =
      cfg (some (.source MatrixSourceEntry.start)) (.source (sourceInitial h), none) S := rfl

theorem finish_run {N₂ n d N₁ : ℕ} (a : ℕ)
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁)
    (data : MatrixMaterialization.ExactBitData) (out addr₁ mid addr₂ idx : List Bool) (s : State) :
    run (cleanupBound a r c data out addr₁ mid addr₂ idx)
      (cfg (some (.clear 0)) (s, none) (prepared a r c data out addr₁ mid addr₂ idx)) =
      cfg none initial (input a d N₁ N₂ (MatrixMaterialization.rowCode N₂ n r).val
        (MatrixMaterialization.columnCode d N₁ c).val data out) := by
  rw [cleanupBound, clear_run, cleared_prepared]

theorem template_query {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (p : Fin 4) (z : Fin N₂) (c : ExactConstruction.Columns d N₁) (out : List Bool) :
    let q := ExactConstruction.prefixLength a
    let ell := (c.2 p).2.val
    let alpha := (c.2 p).1.val
    let data := MatrixMaterialization.storeBits C₁ C₂ v
    let answer := ExactConstruction.matrix ha C₁ C₂ v cap (.inl (p,z)) c
    ∃ t ≤ MatrixTemplateEntry.bound ell (q+3) z.val d alpha a q data.first.length data.second.length,
      run t (cfg (some (.template p MatrixTemplateEntry.start))
        (.template MatrixTemplateEntry.base, none)
        (prepared (n := n) a (.inl (p,z)) c data out [] [] [] [])) =
      cfg (some (.clear 0)) (.template MatrixTemplateEntry.base, none)
        (prepared (n := n) a (.inl (p,z)) c data (answer::out)
          (List.replicate (ell*(q+3)+q) true) (List.replicate (z.val*d+alpha) true)
          (List.replicate ((z.val*d+alpha)*a+a) true) []) := by
  dsimp only
  let q := ExactConstruction.prefixLength a
  let ell := (c.2 p).2.val
  let alpha := (c.2 p).1.val
  let data := MatrixMaterialization.storeBits C₁ C₂ v
  let answer := ExactConstruction.matrix ha C₁ C₂ v cap (.inl (p,z)) c
  let S := prepared (n := n) a (.inl (p,z)) c data out [] [] [] []
  let localInput := MatrixTemplateEntry.cfg (some MatrixTemplateEntry.start) MatrixTemplateEntry.base
    (MatrixTemplateEntry.contents ell (q+3) z.val d alpha a q data.first data.second out
      [] [] [] [] [] [] [])
  let localOutput := MatrixTemplateEntry.cfg none MatrixTemplateEntry.base
    (MatrixTemplateEntry.contents ell (q+3) z.val d alpha a q data.first data.second (answer::out)
      (List.replicate (ell*(q+3)+q) true) (List.replicate (z.val*d+alpha) true)
      (List.replicate ((z.val*d+alpha)*a+a) true) [] [] [] [])
  obtain ⟨k, hk, hr⟩ := MatrixTemplateEntry.template_run ha C₁ C₂ v cap p z c out
  change ((advance MatrixTemplateEntry.program)^[k]) localInput = localOutput at hr
  have hh : (((advance MatrixTemplateEntry.program)^[k]) localInput).l = none := by
    rw [hr]; rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs (templateSlots p) S (Label.template p)
    (fun v => (.template v, none)) getTemplate (fun _ => rfl) (some (.clear 0))
    MatrixTemplateEntry.program program (fun _ => rfl) localInput k hh
  rw [hr] at he
  have hi : BitMachineStackEmbedding.cfg (templateSlots p) S (Label.template p)
      (fun v => (.template v, none)) (some (.clear 0)) localInput =
      cfg (some (.template p MatrixTemplateEntry.start)) (.template MatrixTemplateEntry.base, none) S := by
    change (⟨_, _, BitMachineStackEmbedding.bank (templateSlots p) S
      (MatrixTemplateEntry.contents ell (q+3) z.val d alpha a q data.first data.second out
        [] [] [] [] [] [] [])⟩ : Config) = _
    rw [template_bank]
    rfl
  have ho : BitMachineStackEmbedding.cfg (templateSlots p) S (Label.template p)
      (fun v => (.template v, none)) (some (.clear 0)) localOutput =
      cfg (some (.clear 0)) (.template MatrixTemplateEntry.base, none)
        (prepared (n := n) a (.inl (p,z)) c data (answer::out)
          (List.replicate (ell*(q+3)+q) true) (List.replicate (z.val*d+alpha) true)
          (List.replicate ((z.val*d+alpha)*a+a) true) []) := by
    change (⟨_, _, BitMachineStackEmbedding.bank (templateSlots p) S
      (MatrixTemplateEntry.contents ell (q+3) z.val d alpha a q data.first data.second (answer::out)
        (List.replicate (ell*(q+3)+q) true) (List.replicate (z.val*d+alpha) true)
        (List.replicate ((z.val*d+alpha)*a+a) true) [] [] [] [])⟩ : Config) = _
    rw [template_bank]
    rfl
  exact ⟨t, ht.trans hk, by simpa only [hi, ho, run] using he⟩

theorem source_copy {N₂ n d N₁ : ℕ} (a : ℕ) (i : Fin n)
    (c : ExactConstruction.Columns d N₁) (data : MatrixMaterialization.ExactBitData)
    (out : List Bool) :
    let h := MatrixMaterializationMachine.header (decide (ExactConstruction.aligned c)) c.1
    let idx := List.replicate (c.2 0).1.val true
    ∃ t ≤ 2*(c.2 0).1.val+2,
      run t (cfg (some (.sourceCopy h .scan)) (.copy none, none)
        (prepared (N₂ := N₂) a (.inr i) c data out [] [] [] [])) =
      cfg (some (.sourceInit h)) (.copy none, none)
        (prepared (N₂ := N₂) a (.inr i) c data out [] [] [] idx) := by
  dsimp only
  let h := MatrixMaterializationMachine.header (decide (ExactConstruction.aligned c)) c.1
  let idx := List.replicate (c.2 0).1.val true
  let S := prepared (N₂ := N₂) a (.inr i) c data out [] [] [] []
  let localInput := BitMachineCopy.cfg (some .scan) none idx [] []
  let localOutput := BitMachineCopy.cfg none none idx idx []
  have hr : ((advance BitMachineCopy.program)^[2*idx.length+2]) localInput = localOutput := by
    simpa only [BitMachineCopy.run, List.append_nil] using BitMachineCopy.run_correct none idx []
  have hh : (((advance BitMachineCopy.program)^[2*idx.length+2]) localInput).l = none := by
    rw [hr]; rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs sourceCopySlots S (Label.sourceCopy h)
    (fun v => (.copy v, none)) getCopy (fun _ => rfl) (some (.sourceInit h))
    BitMachineCopy.program program (fun _ => rfl) localInput (2*idx.length+2) hh
  rw [hr] at he
  have hi : BitMachineStackEmbedding.cfg sourceCopySlots S (Label.sourceCopy h)
      (fun v => (.copy v, none)) (some (.sourceInit h)) localInput =
      cfg (some (.sourceCopy h .scan)) (.copy none, none) S := by
    change (⟨_, _, BitMachineStackEmbedding.bank sourceCopySlots S
      (BitMachineCopy.cfg none none idx [] []).stk⟩ : Config) = _
    rw [source_copy_bank]
    rfl
  have ho : BitMachineStackEmbedding.cfg sourceCopySlots S (Label.sourceCopy h)
      (fun v => (.copy v, none)) (some (.sourceInit h)) localOutput =
      cfg (some (.sourceInit h)) (.copy none, none)
        (prepared (N₂ := N₂) a (.inr i) c data out [] [] [] idx) := by
    change (⟨_, _, BitMachineStackEmbedding.bank sourceCopySlots S
      (BitMachineCopy.cfg none none idx idx []).stk⟩ : Config) = _
    rw [source_copy_bank]
    rfl
  refine ⟨t, ?_, by simpa only [hi, ho, run] using he⟩
  simpa only [idx, List.length_replicate] using ht

def sourceQueryBound {n d N₁ : ℕ} (i : Fin n) (c : ExactConstruction.Columns d N₁) : ℕ :=
  (i.val+1) * (3*((c.2 0).1.val+(i.val+1)*d)+3*(n*d)+2*d+12)+3*i.val+5

theorem source_query {a N₂ n d N₁ : ℕ}
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (i : Fin n) (c : ExactConstruction.Columns d N₁) (out : List Bool) :
    let data := MatrixMaterialization.storeBits C₁ C₂ v
    let h := MatrixMaterializationMachine.header (decide (ExactConstruction.aligned c)) c.1
    ∃ t ≤ sourceQueryBound i c,
      run t (cfg (some (.source MatrixSourceEntry.start)) (.source (sourceInitial h), none)
        (prepared (N₂ := N₂) a (.inr i) c data out [] [] []
          (List.replicate (c.2 0).1.val true))) =
      cfg (some (.clear 0)) (.source MatrixSourceEntry.finalControl, none)
        (prepared (N₂ := N₂) a (.inr i) c data (ExactConstruction.vectorEntry v cap i c::out)
          [] [] [] (List.replicate ((c.2 0).1.val+(i.val+1)*d) true)) := by
  dsimp only
  let data := MatrixMaterialization.storeBits C₁ C₂ v
  let h := MatrixMaterializationMachine.header (decide (ExactConstruction.aligned c)) c.1
  let idx := List.replicate (c.2 0).1.val true
  let S := prepared (N₂ := N₂) a (.inr i) c data out [] [] [] idx
  let localInput := MatrixSourceEntry.cfg (some MatrixSourceEntry.start) h none
    idx data.source [] [] (List.replicate d true) out (List.replicate i.val true) []
  let localOutput := MatrixSourceEntry.cfg none {} none
    (List.replicate ((c.2 0).1.val+(i.val+1)*d) true) data.source [] [] (List.replicate d true)
    (ExactConstruction.vectorEntry v cap i c::out) (List.replicate i.val true) []
  obtain ⟨k, hk, hr⟩ := MatrixSourceEntry.source_run v cap i c out
  change ((advance MatrixSourceEntry.program)^[k]) localInput = localOutput at hr
  have hh : (((advance MatrixSourceEntry.program)^[k]) localInput).l = none := by rw [hr]; rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs sourceSlots S Label.source
    (fun v => (.source v, none)) getSource (fun _ => rfl) (some (.clear 0))
    MatrixSourceEntry.program program (fun _ => rfl) localInput k hh
  rw [hr] at he
  have hi : BitMachineStackEmbedding.cfg sourceSlots S Label.source
      (fun v => (.source v, none)) (some (.clear 0)) localInput =
      cfg (some (.source MatrixSourceEntry.start)) (.source (sourceInitial h), none) S := by
    change (⟨_, _, BitMachineStackEmbedding.bank sourceSlots S
      (MatrixSourceEntry.cfg none {} none idx data.source [] [] (List.replicate d true)
        out (List.replicate i.val true) []).stk⟩ : Config) = _
    rw [source_bank]
    rfl
  have ho : BitMachineStackEmbedding.cfg sourceSlots S Label.source
      (fun v => (.source v, none)) (some (.clear 0)) localOutput =
      cfg (some (.clear 0)) (.source MatrixSourceEntry.finalControl, none)
        (prepared (N₂ := N₂) a (.inr i) c data (ExactConstruction.vectorEntry v cap i c::out)
          [] [] [] (List.replicate ((c.2 0).1.val+(i.val+1)*d) true)) := by
    change (⟨_, _, BitMachineStackEmbedding.bank sourceSlots S
      (MatrixSourceEntry.cfg none {} none
        (List.replicate ((c.2 0).1.val+(i.val+1)*d) true) data.source [] [] (List.replicate d true)
        (ExactConstruction.vectorEntry v cap i c::out) (List.replicate i.val true) []).stk⟩ : Config) = _
    rw [source_bank]
    rfl
  exact ⟨t, ht.trans hk, by simpa only [hi, ho, run] using he⟩


/-- Branch costs include dispatch, every literal array operation, and the
lengths of all cells actually discarded by cleanup. -/
def queryBound {N₂ n d N₁ : ℕ} (a : ℕ) (data : MatrixMaterialization.ExactBitData) :
    ((Fin 4 × Fin N₂) ⊕ Fin n) → ExactConstruction.Columns d N₁ → ℕ
  | .inl (p,z), c =>
      let q := ExactConstruction.prefixLength a
      let ell := (c.2 p).2.val
      let alpha := (c.2 p).1.val
      2 + MatrixTemplateEntry.bound ell (q+3) z.val d alpha a q
        data.first.length data.second.length +
        cleanupSize (n := n) (.inl (p,z)) c
          (List.replicate (ell*(q+3)+q) true) (List.replicate (z.val*d+alpha) true)
          (List.replicate ((z.val*d+alpha)*a+a) true) []
  | .inr i, c =>
      2*(c.2 0).1.val + 5 + sourceQueryBound i c +
        cleanupSize (N₂ := N₂) (.inr i) c [] [] []
          (List.replicate ((c.2 0).1.val+(i.val+1)*d) true)

def entryBound {N₂ n d N₁ : ℕ} (a : ℕ) (data : MatrixMaterialization.ExactBitData)
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁) : ℕ :=
  preparationBound r c + queryBound a data r c

/-- A single fixed finite controller computes every entry of the exact
matrix from literal row/column counters and the three literal data arrays.
It preserves all input counters and parameters, prepends the answer to an
arbitrary output suffix, empties its work stacks, and resets its control. -/
theorem entry_run {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁) (out : List Bool) :
    let data := MatrixMaterialization.storeBits C₁ C₂ v
    ∃ t ≤ entryBound a data r c,
      run t (cfg (some start) initial
        (input a d N₁ N₂ (MatrixMaterialization.rowCode N₂ n r).val
          (MatrixMaterialization.columnCode d N₁ c).val data out)) =
      cfg none initial
        (input a d N₁ N₂ (MatrixMaterialization.rowCode N₂ n r).val
          (MatrixMaterialization.columnCode d N₁ c).val data
          (ExactConstruction.matrix ha C₁ C₂ v cap r c :: out)) := by
  dsimp only
  let data := MatrixMaterialization.storeBits C₁ C₂ v
  obtain ⟨tp, htp, hp⟩ := preparation_run a r c data out
  rcases r with ⟨p,z⟩ | i
  · let q := ExactConstruction.prefixLength a
    let ell := (c.2 p).2.val
    let alpha := (c.2 p).1.val
    let answer := ExactConstruction.matrix ha C₁ C₂ v cap (.inl (p,z)) c
    let addr₁ := List.replicate (ell*(q+3)+q) true
    let mid := List.replicate (z.val*d+alpha) true
    let addr₂ := List.replicate ((z.val*d+alpha)*a+a) true
    let cleanup := cleanupSize (n := n) (.inl (p,z)) c addr₁ mid addr₂ []
    have hd := dispatch_template (n := n) p z c (prepared (n := n) a (.inl (p,z)) c data out [] [] [] [])
    obtain ⟨tq, htq, hq⟩ := template_query ha C₁ C₂ v cap p z c out
    have hf := finish_run (n := n) a (.inl (p,z)) c data (answer::out) addr₁ mid addr₂ []
      (.template MatrixTemplateEntry.base)
    rw [cleanupBound_eq] at hf
    refine ⟨tp + 2 + tq + cleanup, ?_, ?_⟩
    · change tp + 2 + tq + cleanup ≤ preparationBound (.inl (p,z)) c +
        (2 + MatrixTemplateEntry.bound ell (q+3) z.val d alpha a q
          data.first.length data.second.length + cleanup)
      change tq ≤ MatrixTemplateEntry.bound ell (q+3) z.val d alpha a q
        data.first.length data.second.length at htq
      omega
    · exact (run_add ((run_add ((run_add hp 2).trans hd) tq).trans hq) cleanup).trans hf
  · let answer := ExactConstruction.vectorEntry v cap i c
    let idx := List.replicate ((c.2 0).1.val+(i.val+1)*d) true
    let cleanup := cleanupSize (N₂ := N₂) (.inr i) c [] [] [] idx
    let h := MatrixMaterializationMachine.header (decide (ExactConstruction.aligned c)) c.1
    have hd := dispatch_source (N₂ := N₂) i c (prepared (N₂ := N₂) a (.inr i) c data out [] [] [] [])
    obtain ⟨tc, htc, hc⟩ := source_copy (N₂ := N₂) a i c data out
    have hi := source_initialize h
      (prepared (N₂ := N₂) a (.inr i) c data out [] [] [] (List.replicate (c.2 0).1.val true))
    obtain ⟨tq, htq, hq⟩ := source_query C₁ C₂ v cap i c out
    have hf := finish_run (N₂ := N₂) a (.inr i) c data (answer::out) [] [] [] idx
      (.source MatrixSourceEntry.finalControl)
    rw [cleanupBound_eq] at hf
    refine ⟨tp + 2 + tc + 1 + tq + cleanup, ?_, ?_⟩
    · change tp + 2 + tc + 1 + tq + cleanup ≤ preparationBound (.inr i) c +
        (2*(c.2 0).1.val+5+sourceQueryBound i c+cleanup)
      omega
    · exact (run_add ((run_add ((run_add ((run_add ((run_add hp 2).trans hd) tc).trans hc)
        1).trans hi) tq).trans hq) cleanup).trans hf

end EthInapproximability.CurrentPaper.MatrixEntryCorrectness
