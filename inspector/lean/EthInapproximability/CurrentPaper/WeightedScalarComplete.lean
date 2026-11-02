import EthInapproximability.CurrentPaper.WeightedActualSizeSuffix
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Single fixed weighted scalar sequence from one raw-six parameter bank,
one literal guarded graph code, and an already physical row-count word at
writer17. It computes bins, graph order/counts, q, a, t, m, threshold and L.
The row-count input is an explicit remaining matrix-dimension staging seam. -/

namespace EthInapproximability.CurrentPaper.WeightedScalarComplete

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev Stack := WeightedActualSizeSuffix.Stack
def prefixSlots : WeightedPrefixAT.Stack ↪ Stack :=
  ⟨fun j => .inl (.inl j),by
    intro a b h
    exact Sum.inl_injective (Sum.inl_injective h)⟩
def writer (k : Fin 64) : Stack :=
  WeightedActualSizeSuffix.writer k
def initialBank (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) : Stack → List Bool :=
  WeightedActualSizeSuffix.initialBank
    (WeightedPrefixAT.initialBank i g W)
def afterPrefix (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) : Stack → List Bool :=
  WeightedActualSizeSuffix.initialBank
    (WeightedPrefixAT.finalBank i g W F Q)
def finalBank (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool)
    (P : ChosenPrimeRaw.Stack → List Bool) (rx q : ℕ) :
    Stack → List Bool :=
  WeightedActualSizeSuffix.finalBank
    (WeightedPrefixAT.finalBank i g W F Q)
    (Parameters.firstExponent i) rx q (Parameters.balanceOrder i) P
def prefixProgram := fun l => stackStmt prefixSlots
  (WeightedPrefixAT.program l)
def program := BitMachineRawSequence.program prefixProgram
  WeightedActualSizeSuffix.program
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (Sum.inr false)))))))
  WeightedPrefixAT.initialControl
  WeightedActualSizeSuffix.initialControl
def initialControl :=
  (WeightedPrefixAT.initialControl,
    WeightedActualSizeSuffix.initialControl)
def bound (i : Parameters.Input) (g : EncodedGraph.Graph)
    (e rx q : ℕ) : ℕ :=
  WeightedPrefixAT.bound i g e +
  WeightedActualSizeSuffix.bound (Parameters.firstExponent i) rx q
    (Parameters.balanceOrder i) + 1

theorem source_run {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (i : Parameters.Input)
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (W : Fin 64 → List Bool) (rx : ℕ)
    (hrx : W 17 = List.replicate rx true)
    (h28 : W 28 = []) (h61 : W 61 = [])
    (h7 : W 7 = []) (h8 : W 8 = []) (h9 : W 9 = [])
    (h10 : W 10 = []) (h11 : W 11 = []) (h12 : W 12 = [])
    (h13 : W 13 = []) (h14 : W 14 = [])
    (h15 : W 15 = []) (h18 : W 18 = [])
    (h54 : W 54 = []) (h55 : W 55 = []) (h56 : W 56 = [])
    (h57 : W 57 = []) (h58 : W 58 = []) (h60 : W 60 = []) :
    let g := EncodedETHSource.serializeGraph G
    let q := ParameterizedNP.GuardedSourceSlab.q2 G (Parameters.bins i)
    ∃ u ≤ bound i g (Fintype.card E) rx q,
      ∃ v : Fin ETHBinsStandaloneScratch.machine.controlCount,
      ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
      ∃ Q : WeightedGraphQJoined.Stack → List Bool,
      ∃ P : ChosenPrimeRaw.Stack → List Bool,
        ((advance program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  BinsWriterAssembly.binStart)))),
            initialControl,initialBank i g W⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,initialControl,finalBank i g W F Q P rx q⟩ ∧
        (finalBank i g W F Q P rx q) (writer 54) =
          List.replicate (Parameters.firstExponent i) true ∧
        (finalBank i g W F Q P rx q) (writer 56) =
          List.replicate q true ∧
        (finalBank i g W F Q P rx q) (writer 57) =
          List.replicate
            (PrimeSampler.size q (Parameters.balanceOrder i)
              (Construction.qOne (Parameters.firstExponent i) * rx)) true ∧
        (finalBank i g W F Q P rx q) (writer 17) =
          List.replicate rx true := by
  let g := EncodedETHSource.serializeGraph G
  let q := ParameterizedNP.GuardedSourceSlab.q2 G (Parameters.bins i)
  obtain ⟨up,hup,v,F,Q,hprefix,ha,ht,hq,h17,h57pre⟩ :=
    WeightedPrefixAT.source_run i G W h28 h61
      h7 h8 h9 h10 h11 h12 h13 h14 h15 h18
      h54 h55 h56 h57 h58 h60
  let S := WeightedPrefixAT.finalBank i g W F Q
  have hrxS : S (WeightedPrefixAT.writer 17) =
      List.replicate rx true := h17.trans hrx
  have h57S : S (WeightedPrefixAT.writer 57) = [] :=
    h57pre.trans h57
  obtain ⟨uz,huz,P,hsize,hwriter⟩ :=
    WeightedActualSizeSuffix.run S
      (Parameters.firstExponent i) rx q (Parameters.balanceOrder i)
      ha hrxS hq ht h57S
  have hLift :
      ((advance prefixProgram)^[up])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart))),
          WeightedPrefixAT.initialControl,initialBank i g W⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,WeightedPrefixAT.initialControl,
          afterPrefix i g W F Q⟩ := by
    have he := BitMachineStackRun.run prefixSlots
      (initialBank i g W) WeightedPrefixAT.program
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart))),
        WeightedPrefixAT.initialControl,
        WeightedPrefixAT.initialBank i g W⟩ :
        TM2.Cfg (fun _ : WeightedPrefixAT.Stack => Bool) _ _) up
    rw [hprefix] at he
    have hi : bank prefixSlots (initialBank i g W)
        (WeightedPrefixAT.initialBank i g W) =
        initialBank i g W :=
      bank_eq_self prefixSlots _ _ (fun _ => rfl)
    have ho : bank prefixSlots (initialBank i g W)
        (WeightedPrefixAT.finalBank i g W F Q) =
        afterPrefix i g W F Q := by
      funext j
      cases j with
      | inl j =>
          cases j with
          | inl j => exact bank_at prefixSlots _ _ j
          | inr j =>
              rw [bank_outside]
              · rfl
              · rintro ⟨k,h⟩; cases h
      | inr j =>
          rw [bank_outside]
          · rfl
          · rintro ⟨k,h⟩; cases h
    simpa only [prefixProgram,stackCfg,hi,ho,g]
      using he
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    prefixProgram WeightedActualSizeSuffix.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart)))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (Sum.inr false)))))))
    WeightedPrefixAT.initialControl WeightedPrefixAT.initialControl
    WeightedActualSizeSuffix.initialControl
    WeightedActualSizeSuffix.initialControl
    (initialBank i g W) (afterPrefix i g W F Q)
    (finalBank i g W F Q P rx q)
    up uz hLift (by simpa only [finalBank,S] using hsize)
  refine ⟨u,?_,v,F,Q,P,?_,?_,?_,?_,?_⟩
  · change u ≤ WeightedPrefixAT.bound i g (Fintype.card E) +
      WeightedActualSizeSuffix.bound (Parameters.firstExponent i) rx q
        (Parameters.balanceOrder i) + 1
    have hup' : up ≤ WeightedPrefixAT.bound i g (Fintype.card E) := by
      simpa only [g] using hup
    omega
  · simpa only [program,initialControl] using hr
  · have hw := hwriter 54
    simpa [Function.update_of_ne (by decide : (54 : Fin 64) ≠ 57)] using
      hw.trans ha
  · have hw := hwriter 56
    simpa [Function.update_of_ne (by decide : (56 : Fin 64) ≠ 57)] using
      hw.trans hq
  · have hw := hwriter 57
    simpa using hw
  · have hw := hwriter 17
    simpa [Function.update_of_ne (by decide : (17 : Fin 64) ≠ 57)] using
      hw.trans hrxS

#print axioms source_run

end
end EthInapproximability.CurrentPaper.WeightedScalarComplete
