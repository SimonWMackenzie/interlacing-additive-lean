import Paper2.YaoPayloadWidthJoin
import EthInapproximability.CurrentPaper.MatrixTemplateAddressSetup
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! Direct physical selector-address arithmetic on the retained scalar
bank. Slots 2--5 of the existing setup controller are the *actual* z,Q,g,b
cells; no copies or desired selector address are placed in the initial bank.
Fresh cells 0,1,6--11 are initially empty. -/

namespace Paper2.YaoEntryParameterJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.YaoParameterBank
open Paper2.YaoLowerBound
open Paper2.YaoLookup

abbrev SelectorStack (t lambda : ℕ) := Stack t lambda ⊕ Fin 8

noncomputable def selectorSlot (t lambda : ℕ) : Fin 12 ↪ SelectorStack t lambda where
  toFun := ![
    .inr 0, .inr 1,
    .inl (.inl (.inl (.inr 0))),
    .inl (.inl (.inr 0)),
    .inl (.inl (.inl (.inr 1))),
    .inl (.inl (.inl (.inl (.inl bitsCell)))),
    .inr 2, .inr 3, .inr 4, .inr 5, .inr 6, .inr 7]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      simp_all [Fin.ext_iff]

noncomputable def selectorProgram (t lambda : ℕ) (l : MatrixTemplateAddressSetup.Label) :
    TM2.Stmt (fun _ : SelectorStack t lambda => Bool)
      MatrixTemplateAddressSetup.Label Bool :=
  BitMachineStackEmbedding.stmt (selectorSlot t lambda) id id id none
    (MatrixTemplateAddressSetup.program l)

/-- The existing three-phase finite controller computes the selector offset
directly from the four actual retained source cells. The first dummy phase
uses physical empty cells (zero), and the two address phases write and reuse
the intermediate `z*Q+g`; all remaining cells survive. -/
theorem selector_address_phase (t lambda e z g : ℕ)
    (W : Stack t lambda → List Bool)
    (hB : W (.inl (.inl (.inl (.inl bitsCell)))) =
      List.replicate (paddedEdgeBits e) true)
    (hZ : W (.inl (.inl (.inr 0))) = List.replicate z true)
    (hG : W (.inl (.inl (.inr 1))) = List.replicate g true)
    (hQ : W (.inl (.inr 0)) = List.replicate (fixedQ t) true) :
    ∃ steps ≤ MatrixTemplateAddressSetup.bound
      0 0 z (fixedQ t) g (paddedEdgeBits e),
      let S : SelectorStack t lambda → List Bool := Sum.elim W (fun _ => [])
      ((advance (selectorProgram t lambda))^[steps])
        (⟨some (0,.outer),false,S⟩ :
          TM2.Cfg (fun _ : SelectorStack t lambda => Bool)
            MatrixTemplateAddressSetup.Label Bool) =
      ⟨none,false,
        Function.update
          (Function.update S (selectorSlot t lambda 10)
            (List.replicate (z * fixedQ t + g) true))
          (selectorSlot t lambda 11)
          (List.replicate ((z * fixedQ t + g) * paddedEdgeBits e) true)⟩ := by
  let ι := selectorSlot t lambda
  let S : SelectorStack t lambda → List Bool := Sum.elim W (fun _ => [])
  let c := MatrixTemplateAddressSetup.cfg (some (0,.outer)) false
    (MatrixTemplateAddressSetup.contents 0 0 z (fixedQ t) g
      (paddedEdgeBits e) [] [] [])
  let d := MatrixTemplateAddressSetup.cfg none false
    (MatrixTemplateAddressSetup.contents 0 0 z (fixedQ t) g
      (paddedEdgeBits e) []
      (List.replicate (z * fixedQ t + g) true)
      (List.replicate ((z * fixedQ t + g) * paddedEdgeBits e) true))
  obtain ⟨n,hn,hr⟩ := MatrixTemplateAddressSetup.setup_run
    0 0 z (fixedQ t) g (paddedEdgeBits e) false [] []
  have hhalt : (((advance MatrixTemplateAddressSetup.program)^[n]) c).l = none := by
    rw [← MatrixTemplateAddressSetup.run, hr]
    rfl
  obtain ⟨steps,hsteps,hembed⟩ := BitMachineStackEmbedding.outputs
    ι S id id id (by intro x; rfl) none
    MatrixTemplateAddressSetup.program (selectorProgram t lambda)
    (by intro l; rfl) c n hhalt
  have hbank : BitMachineStackEmbedding.bank ι S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;>
      simp [c, MatrixTemplateAddressSetup.cfg,
        MatrixTemplateAddressSetup.contents, S, ι, selectorSlot,
        hB, hZ, hG, hQ]
  have hlocal : d.stk =
      Function.update (Function.update c.stk 10
        (List.replicate (z * fixedQ t + g) true)) 11
        (List.replicate ((z * fixedQ t + g) * paddedEdgeBits e) true) := by
    funext k
    fin_cases k <;>
      simp [c, d, MatrixTemplateAddressSetup.cfg,
        MatrixTemplateAddressSetup.contents, Function.update]
  have hfinish : BitMachineStackEmbedding.cfg ι S id id none d =
      ⟨none,false,
        Function.update
          (Function.update S (ι 10)
            (List.replicate (z * fixedQ t + g) true))
          (ι 11)
          (List.replicate ((z * fixedQ t + g) * paddedEdgeBits e) true)⟩ := by
    have hstk : BitMachineStackEmbedding.bank ι S d.stk =
        Function.update
          (Function.update S (ι 10)
            (List.replicate (z * fixedQ t + g) true))
          (ι 11)
          (List.replicate ((z * fixedQ t + g) * paddedEdgeBits e) true) := by
      rw [hlocal, BitMachineStackEmbedding.bank_update,
        BitMachineStackEmbedding.bank_update, hbank]
    exact congrArg (fun X : SelectorStack t lambda → List Bool =>
      (⟨none,false,X⟩ : TM2.Cfg (fun _ : SelectorStack t lambda => Bool)
        MatrixTemplateAddressSetup.Label Bool)) hstk
  refine ⟨steps, by omega,?_⟩
  dsimp only
  have hstart : BitMachineStackEmbedding.cfg ι S id id none c =
      (⟨some (0,.outer),false,S⟩ :
        TM2.Cfg (fun _ : SelectorStack t lambda => Bool)
          MatrixTemplateAddressSetup.Label Bool) := by
    change (⟨some (0,.outer),false,BitMachineStackEmbedding.bank ι S c.stk⟩ :
      TM2.Cfg (fun _ : SelectorStack t lambda => Bool)
        MatrixTemplateAddressSetup.Label Bool) = _
    rw [hbank]
  have hr' : ((advance MatrixTemplateAddressSetup.program)^[n]) c = d := by
    simpa [MatrixTemplateAddressSetup.run, c, d] using hr
  rw [← hstart]
  rw [hr'] at hembed
  simpa only [hfinish] using hembed

#print axioms selector_address_phase

end Paper2.YaoEntryParameterJoin
