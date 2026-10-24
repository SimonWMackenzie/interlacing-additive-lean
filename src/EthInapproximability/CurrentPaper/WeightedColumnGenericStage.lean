import EthInapproximability.CurrentPaper.ColumnInputStaging

/-! The frozen three-copy controller on an arbitrary reached writer bank.
Only the six genuine scalar inputs and three empty copy temporaries matter;
foreign writer contents are not replaced by a semantic oracle bank. -/

namespace EthInapproximability.CurrentPaper.WeightedColumnGenericStage

open Turing BitMachineEncoding BitMachineStackEmbedding
open ColumnInputStaging

noncomputable section

def partialBank (B : Fin 64 → List Bool) (a q L : ℕ) :
    Fin 64 → List Bool :=
  bank ColumnWriterJoin.slots B (ColumnInputStaging.partialLocalBank a q L)

theorem partial_live (B : Fin 64 → List Bool) (a q L s rx cy : ℕ)
    (hs : B 28 = List.replicate s true)
    (hrx : B 17 = List.replicate rx true)
    (hcy : B 27 = List.replicate cy true) :
    partialBank B a q L 28 = List.replicate s true ∧
    partialBank B a q L 17 = List.replicate rx true ∧
    partialBank B a q L 27 = List.replicate cy true := by
  have h28 : ¬ ∃ i : Fin 40, ColumnWriterJoin.slots i = (28 : Fin 64) := by decide
  have h17 : ¬ ∃ i : Fin 40, ColumnWriterJoin.slots i = (17 : Fin 64) := by decide
  have h27 : ¬ ∃ i : Fin 40, ColumnWriterJoin.slots i = (27 : Fin 64) := by decide
  simp [partialBank, bank_outside _ _ _ _ h28,
    bank_outside _ _ _ _ h17, bank_outside _ _ _ _ h27, hs, hrx, hcy]

theorem partial_blank (B : Fin 64 → List Bool) (a q L : ℕ)
    (h61 : B 61 = []) (h62 : B 62 = []) (h63 : B 63 = []) :
    partialBank B a q L 55 = [] ∧
    partialBank B a q L 58 = [] ∧
    partialBank B a q L 59 = [] ∧
    partialBank B a q L 61 = [] ∧
    partialBank B a q L 62 = [] ∧
    partialBank B a q L 63 = [] := by
  have h61' : ¬ ∃ i : Fin 40, ColumnWriterJoin.slots i = (61 : Fin 64) := by decide
  have h62' : ¬ ∃ i : Fin 40, ColumnWriterJoin.slots i = (62 : Fin 64) := by decide
  have h63' : ¬ ∃ i : Fin 40, ColumnWriterJoin.slots i = (63 : Fin 64) := by decide
  simp [partialBank,
    show (55 : Fin 64) = ColumnWriterJoin.slots 1 from rfl,
    show (58 : Fin 64) = ColumnWriterJoin.slots 4 from rfl,
    show (59 : Fin 64) = ColumnWriterJoin.slots 5 from rfl,
    bank_at, ColumnInputStaging.partialLocalBank,
    bank_outside _ _ _ _ h61', bank_outside _ _ _ _ h62',
    bank_outside _ _ _ _ h63', h61, h62, h63]

theorem s_run (B : Fin 64 → List Bool) (a q L s rx cy : ℕ)
    (hs : B 28 = List.replicate s true)
    (hrx : B 17 = List.replicate rx true)
    (hcy : B 27 = List.replicate cy true)
    (h61 : B 61 = []) (h62 : B 62 = []) (h63 : B 63 = []) :
    ((advance ColumnInputStaging.sProgram)^[2*s+2])
      (⟨some .scan, none, partialBank B a q L⟩ :
        TM2.Cfg (fun _ : Fin 64 => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, ColumnInputStaging.afterS (partialBank B a q L) s⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run ColumnInputStaging.sSlots
    (partialBank B a q L) (partial_blank B a q L h61 h62 h63).2.2.2.1
  have hsource := (partial_live B a q L s rx cy hs hrx hcy).1
  have htarget := (partial_blank B a q L h61 h62 h63).1
  simpa [ColumnInputStaging.sProgram, ColumnInputStaging.sSlots,
    hsource, htarget, ColumnInputStaging.afterS] using h

theorem rx_run (B : Fin 64 → List Bool) (a q L s rx cy : ℕ)
    (hs : B 28 = List.replicate s true)
    (hrx : B 17 = List.replicate rx true)
    (hcy : B 27 = List.replicate cy true)
    (h61 : B 61 = []) (h62 : B 62 = []) (h63 : B 63 = []) :
    ((advance ColumnInputStaging.rxProgram)^[2*rx+2])
      (⟨some .scan, none, ColumnInputStaging.afterS (partialBank B a q L) s⟩ :
        TM2.Cfg (fun _ : Fin 64 => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, ColumnInputStaging.afterRx
        (ColumnInputStaging.afterS (partialBank B a q L) s) rx⟩ := by
  let S := ColumnInputStaging.afterS (partialBank B a q L) s
  have he : S (ColumnInputStaging.rxSlots 2) = [] := by
    simp [S,ColumnInputStaging.afterS,ColumnInputStaging.rxSlots,
      (partial_blank B a q L h61 h62 h63).2.2.2.2.1]
  have hsource : S (ColumnInputStaging.rxSlots 0) = List.replicate rx true := by
    simp [S,ColumnInputStaging.afterS,ColumnInputStaging.rxSlots,
      (partial_live B a q L s rx cy hs hrx hcy).2.1]
  have htarget : S (ColumnInputStaging.rxSlots 1) = [] := by
    simp [S,ColumnInputStaging.afterS,ColumnInputStaging.rxSlots,
      (partial_blank B a q L h61 h62 h63).2.1]
  have h := MatrixStage4ScalarPreparationOps.copy_run
    ColumnInputStaging.rxSlots S he
  simpa only [ColumnInputStaging.rxProgram, hsource, htarget,
    List.length_replicate, List.append_nil, ColumnInputStaging.afterRx, S] using h

theorem cy_run (B : Fin 64 → List Bool) (a q L s rx cy : ℕ)
    (hs : B 28 = List.replicate s true)
    (hrx : B 17 = List.replicate rx true)
    (hcy : B 27 = List.replicate cy true)
    (h61 : B 61 = []) (h62 : B 62 = []) (h63 : B 63 = []) :
    ((advance ColumnInputStaging.cyProgram)^[2*cy+2])
      (⟨some .scan, none, ColumnInputStaging.afterRx
        (ColumnInputStaging.afterS (partialBank B a q L) s) rx⟩ :
        TM2.Cfg (fun _ : Fin 64 => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, ColumnInputStaging.afterCy
        (ColumnInputStaging.afterRx
          (ColumnInputStaging.afterS (partialBank B a q L) s) rx) cy⟩ := by
  let S := ColumnInputStaging.afterRx
    (ColumnInputStaging.afterS (partialBank B a q L) s) rx
  have he : S (ColumnInputStaging.cySlots 2) = [] := by
    simp [S,ColumnInputStaging.afterS,ColumnInputStaging.afterRx,
      ColumnInputStaging.cySlots,
      (partial_blank B a q L h61 h62 h63).2.2.2.2.2]
  have hsource : S (ColumnInputStaging.cySlots 0) = List.replicate cy true := by
    simp [S,ColumnInputStaging.afterS,ColumnInputStaging.afterRx,
      ColumnInputStaging.cySlots,
      (partial_live B a q L s rx cy hs hrx hcy).2.2]
  have htarget : S (ColumnInputStaging.cySlots 1) = [] := by
    simp [S,ColumnInputStaging.afterS,ColumnInputStaging.afterRx,
      ColumnInputStaging.cySlots,
      (partial_blank B a q L h61 h62 h63).2.2.1]
  have h := MatrixStage4ScalarPreparationOps.copy_run
    ColumnInputStaging.cySlots S he
  simpa only [ColumnInputStaging.cyProgram, hsource, htarget,
    List.length_replicate, List.append_nil, ColumnInputStaging.afterCy, S] using h

theorem after_three_eq_full (B : Fin 64 → List Bool)
    (a s q L rx cy : ℕ) :
    ColumnInputStaging.afterCy
      (ColumnInputStaging.afterRx
        (ColumnInputStaging.afterS (partialBank B a q L) s) rx) cy =
      ColumnWriterJoin.sourceBank B a s q L rx cy := by
  simp only [ColumnInputStaging.afterCy, ColumnInputStaging.afterRx,
    ColumnInputStaging.afterS, partialBank, ColumnWriterJoin.sourceBank,
    show (55 : Fin 64) = ColumnWriterJoin.slots 1 from rfl,
    show (58 : Fin 64) = ColumnWriterJoin.slots 4 from rfl,
    show (59 : Fin 64) = ColumnWriterJoin.slots 5 from rfl,
    ← bank_update]
  congr 1
  funext i
  fin_cases i <;> simp [ColumnInputStaging.partialLocalBank,
    ColumnScalarPrefix.inputBank]

theorem three_run (B : Fin 64 → List Bool) (a s q L rx cy : ℕ)
    (hs : B 28 = List.replicate s true)
    (hrx : B 17 = List.replicate rx true)
    (hcy : B 27 = List.replicate cy true)
    (h61 : B 61 = []) (h62 : B 62 = []) (h63 : B 63 = []) :
    ∃ t ≤ ColumnInputStaging.stageCost s rx cy,
      ((advance ColumnInputStaging.P123)^[t])
        ⟨some (ColumnInputStaging.Raw.leftLabel
          (ColumnInputStaging.Raw.leftLabel BitMachineCopy.Label.scan)),
          ((none,none),none), partialBank B a q L⟩ =
      ⟨none,((none,none),none),
        ColumnWriterJoin.sourceBank B a s q L rx cy⟩ := by
  have h1 := s_run B a q L s rx cy hs hrx hcy h61 h62 h63
  have h2 := rx_run B a q L s rx cy hs hrx hcy h61 h62 h63
  have h3 := cy_run B a q L s rx cy hs hrx hcy h61 h62 h63
  obtain ⟨u,hu,h12⟩ := ColumnInputStaging.Raw.runs
    ColumnInputStaging.sProgram ColumnInputStaging.rxProgram
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan
    none none none none
    (partialBank B a q L)
    (ColumnInputStaging.afterS (partialBank B a q L) s)
    (ColumnInputStaging.afterRx
      (ColumnInputStaging.afterS (partialBank B a q L) s) rx)
    (2*s+2) (2*rx+2) h1 h2
  obtain ⟨v,hv,h123⟩ := ColumnInputStaging.Raw.runs
    ColumnInputStaging.P12 ColumnInputStaging.cyProgram
    (ColumnInputStaging.Raw.leftLabel BitMachineCopy.Label.scan)
    BitMachineCopy.Label.scan
    (none,none) (none,none) none none
    (partialBank B a q L)
    (ColumnInputStaging.afterRx
      (ColumnInputStaging.afterS (partialBank B a q L) s) rx)
    (ColumnInputStaging.afterCy
      (ColumnInputStaging.afterRx
        (ColumnInputStaging.afterS (partialBank B a q L) s) rx) cy)
    u (2*cy+2) (by simpa only [ColumnInputStaging.P12] using h12) h3
  refine ⟨v, ?_, ?_⟩
  · dsimp [ColumnInputStaging.stageCost]; omega
  · rw [after_three_eq_full] at h123
    simpa only [ColumnInputStaging.P123] using h123

#print axioms three_run

end
end EthInapproximability.CurrentPaper.WeightedColumnGenericStage
