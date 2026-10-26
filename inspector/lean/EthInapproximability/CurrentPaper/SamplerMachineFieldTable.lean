import EthInapproximability.CurrentPaper.SamplerMachineTable
import EthInapproximability.CurrentPaper.SamplerMachineChosenWord
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Fixed-machine modulus selection followed by the exact sampler table

Source: locked v8 Appendix E, `lem:exact-families`. The first phase computes
the canonical polynomial word on the same Boolean stacks used by the table
phase. A fixed stack injection maps its sole surviving word to the table's
modulus bank. The persistent unary row length is outside that injection.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineFieldTable

open Turing Turing.TM2.Stmt BitMachineEncoding

def rowModulus : SamplerMachineRow.Stack := .inl (.inl (.inl (.inr 0)))

def prepareFin : SamplerMachineFactorPrepare.Stack ≃ Fin 9 where
  toFun
    | .candidate => 0 | .factorU => 1 | .factorV => 2
    | .target => 3 | .paddedU => 4 | .reversedV => 5
    | .zeroA => 6 | .zeroM => 7 | .work => 8
  invFun i := match i with
    | 0 => .candidate | 1 => .factorU | 2 => .factorV
    | 3 => .target | 4 => .paddedU | 5 => .reversedV
    | 6 => .zeroA | 7 => .zeroM | _ => .work
  left_inv := by intro k; cases k <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def unitFin : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv := by intro u; cases u; rfl
  right_inv := by intro i; fin_cases i; rfl

def sumUnitFin {K : Type*} {n : ℕ} (e : K ≃ Fin n) :
    (K ⊕ Unit) ≃ Fin (n + 1) :=
  (Equiv.sumCongr e unitFin).trans finSumFinEquiv

def chosenFin : SamplerMachineChosenWord.Stack ≃ Fin 14 :=
  sumUnitFin (sumUnitFin (sumUnitFin (sumUnitFin (sumUnitFin prepareFin))))

def productFin : SamplerMachineProduct.Stack ≃ Fin 6 := finSumFinEquiv

def rowFin : SamplerMachineRow.Stack ≃ Fin 14 :=
  (Equiv.sumCongr (sumUnitFin (sumUnitFin productFin)) (Equiv.refl (Fin 6))).trans
    finSumFinEquiv

def baseEquiv : SamplerMachineChosenWord.Stack ≃ SamplerMachineRow.Stack :=
  chosenFin.trans rowFin.symm

def rowEquiv : SamplerMachineChosenWord.Stack ≃ SamplerMachineRow.Stack :=
  baseEquiv.trans (Equiv.swap (baseEquiv SamplerMachineChosenWord.source) rowModulus)

def stackEmbed : SamplerMachineChosenWord.Stack ↪ SamplerMachineTable.Stack :=
  (rowEquiv.toEmbedding).trans <|
    ⟨fun k => .inl (.inl (.inl k)), by intro a b h; exact Sum.inl.inj (Sum.inl.inj (Sum.inl.inj h))⟩

theorem embed_source : stackEmbed SamplerMachineChosenWord.source = SamplerMachineTable.modulus := by
  simp [stackEmbed, rowEquiv, rowModulus, SamplerMachineTable.modulus]

abbrev Stack := SamplerMachineTable.Stack
abbrev Label := SamplerMachineChosenWord.Label ⊕ (Unit ⊕ SamplerMachineTable.Label)
abbrev Control := SamplerMachineChosenWord.Control ⊕ SamplerMachineTable.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def chooseRead : Control → SamplerMachineChosenWord.Control :=
  Sum.elim id (fun _ => SamplerMachineChosenWord.initial)
def tableRead : Control → SamplerMachineTable.Control :=
  Sum.elim (fun _ => SamplerMachineTable.initial) id

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt stackEmbed Sum.inl Sum.inl chooseRead
      (some (.inr (.inl ()))) (SamplerMachineChosenWord.program l)
  | .inr (.inl ()) => load (fun _ => .inr SamplerMachineTable.initial)
      (goto (fun _ => .inr (.inr (.inr .fill))))
  | .inr (.inr l) => BitMachineInline.stmt (fun x => .inr (.inr x)) Sum.inr tableRead none
      (SamplerMachineTable.program l)

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

private theorem chosen_bank (l : Option SamplerMachineChosenWord.Label)
    (s : SamplerMachineChosenWord.Control) (c : List Bool) :
    (SamplerMachineChosenWord.cfg l s c [] []).stk =
      Function.update (fun _ : SamplerMachineChosenWord.Stack => [])
        SamplerMachineChosenWord.source c := by
  funext k
  rcases k with k | k
  · rcases k with k | k
    · change (Function.update (fun _ : SamplerMachineIrreducibility.Stack => [])
          SamplerMachineIrreducibility.source c) k =
          Function.update (fun _ : SamplerMachineChosenWord.Stack => [])
            SamplerMachineChosenWord.source c (.inl (.inl k))
      by_cases h : k = SamplerMachineIrreducibility.source
      · subst k
        simp [SamplerMachineChosenWord.source]
      · simp [SamplerMachineChosenWord.source, h]
    · change ([] : List Bool) =
        Function.update (fun _ : SamplerMachineChosenWord.Stack => [])
          SamplerMachineChosenWord.source c (.inl (.inr k))
      simp [SamplerMachineChosenWord.source]
  · change ([] : List Bool) =
      Function.update (fun _ : SamplerMachineChosenWord.Stack => [])
        SamplerMachineChosenWord.source c (.inr k)
    simp [SamplerMachineChosenWord.source]

private theorem table_bank (c : List Bool) (L : ℕ) :
    (SamplerMachineTable.cfg none SamplerMachineTable.initial c []
      (List.replicate L true) [] [] []).stk =
    Function.update
      (Function.update (fun _ : Stack => []) SamplerMachineTable.lengthSource
        (List.replicate L true)) SamplerMachineTable.modulus c := by
  funext k
  fin_cases k <;> rfl

def baseBank (L : ℕ) : Stack → List Bool :=
  Function.update (fun _ => []) SamplerMachineTable.lengthSource (List.replicate L true)

private theorem embed_ne_length (k : SamplerMachineChosenWord.Stack) :
    stackEmbed k ≠ SamplerMachineTable.lengthSource := by
  simp [stackEmbed, SamplerMachineTable.lengthSource,
    SamplerMachineSeedRow.lengthSource]

private theorem base_image_empty (L : ℕ) (k : SamplerMachineChosenWord.Stack) :
    baseBank L (stackEmbed k) = [] := by
  simp [baseBank, embed_ne_length]

private theorem embedded_bank (c : List Bool) (L : ℕ) :
    BitMachineStackEmbedding.bank stackEmbed (baseBank L)
      (Function.update (fun _ : SamplerMachineChosenWord.Stack => [])
        SamplerMachineChosenWord.source c) =
    Function.update (baseBank L) SamplerMachineTable.modulus c := by
  funext j
  by_cases h : ∃ k, stackEmbed k = j
  · obtain ⟨k, rfl⟩ := h
    rw [BitMachineStackEmbedding.bank_at]
    by_cases hs : k = SamplerMachineChosenWord.source
    · subst k
      rw [embed_source]
      simp
    · have hj : stackEmbed k ≠ SamplerMachineTable.modulus := by
        intro he
        exact hs (stackEmbed.injective (he.trans embed_source.symm))
      simp [hs, hj, base_image_empty]
  · have hj : j ≠ SamplerMachineTable.modulus := by
      intro he
      exact h ⟨SamplerMachineChosenWord.source, by rw [embed_source, he]⟩
    rw [BitMachineStackEmbedding.bank_outside stackEmbed (baseBank L) _ j h]
    simp [hj]

def input (bits : List Bool) (L : ℕ) : Config :=
  ⟨some (.inl (.inr .scan)), .inl SamplerMachineChosenWord.initial,
    (SamplerMachineTable.cfg none SamplerMachineTable.initial bits []
      (List.replicate L true) [] [] []).stk⟩

theorem input_bank (bits : List Bool) (L : ℕ) :
    (input bits L).stk =
      (SamplerMachineTable.cfg none SamplerMachineTable.initial bits []
        (List.replicate L true) [] [] []).stk := by
  rfl

private theorem input_embedding (bits : List Bool) (L : ℕ) :
    input bits L =
      BitMachineStackEmbedding.cfg stackEmbed (baseBank L) Sum.inl Sum.inl
        (some (.inr (.inl ())))
        (SamplerMachineChosenWord.cfg (some (.inr .scan))
          SamplerMachineChosenWord.initial bits [] []) := by
  simp only [input, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  congr 1
  rw [chosen_bank, embedded_bank]
  simpa only [table_bank, baseBank]

private theorem chosen_phase (bits : List Bool) (L : ℕ) :
    ∃ (t : ℕ) (s : SamplerMachineChosenWord.Control),
      t ≤ SamplerMachineChosenWord.timeBound bits.length ∧
      run t (input bits L) =
        ⟨some (.inr (.inl ())), .inl s,
          (SamplerMachineTable.cfg none SamplerMachineTable.initial
            (SamplerMachine.encodeWord
              (ExecutableSmallBiasSampler.chosenWord bits.length)) []
            (List.replicate L true) [] [] []).stk⟩ := by
  obtain ⟨t, s, ht, hr⟩ := SamplerMachineChosenWord.run_chosenWord bits
  have hh : (((advance SamplerMachineChosenWord.program)^[t])
      (SamplerMachineChosenWord.cfg (some (.inr .scan))
        SamplerMachineChosenWord.initial bits [] [])).l = none := by
    rw [← SamplerMachineChosenWord.run, hr]
    rfl
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs stackEmbed (baseBank L)
    Sum.inl Sum.inl chooseRead (by intro v; rfl) (some (.inr (.inl ())))
    SamplerMachineChosenWord.program program (by intro l; rfl)
    (SamplerMachineChosenWord.cfg (some (.inr .scan))
      SamplerMachineChosenWord.initial bits [] []) t hh
  rw [← SamplerMachineChosenWord.run, hr] at he
  refine ⟨u, s, hu.trans ht, ?_⟩
  rw [← input_embedding bits L] at he
  change run u (input bits L) = _ at he ⊢
  have hbank := embedded_bank
    (SamplerMachine.encodeWord (ExecutableSmallBiasSampler.chosenWord bits.length)) L
  simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg] at he
  rw [chosen_bank, hbank] at he
  simpa only [table_bank, baseBank] using he

private theorem switch_step (s : SamplerMachineChosenWord.Control)
    (S : Stack → List Bool) :
    run 1 ⟨some (.inr (.inl ())), .inl s, S⟩ =
      ⟨some (.inr (.inr (.inr .fill))), .inr SamplerMachineTable.initial, S⟩ := by
  simp [run, Function.iterate_one, advance, TM2.step, TM2.stepAux, program]

private theorem table_phase (n L : ℕ) :
    ∃ u ≤ SamplerMachineTable.timeBound n L,
      run u ⟨some (.inr (.inr (.inr .fill))), .inr SamplerMachineTable.initial,
        (SamplerMachineTable.cfg none SamplerMachineTable.initial
          (SamplerMachine.encodeWord (ExecutableSmallBiasSampler.chosenWord n)) []
          (List.replicate L true) [] [] []).stk⟩ =
        ⟨none, .inr SamplerMachineTable.initial,
          (SamplerMachineTable.cfg none SamplerMachineTable.initial
            (SamplerMachine.encodeWord (ExecutableSmallBiasSampler.chosenWord n)) []
            (List.replicate L true) [] []
            (SamplerSeedEnumeration.counterTraceTable n L)).stk⟩ := by
  obtain ⟨t, ht, hr⟩ := SamplerMachineTable.run_table n L
  have hh : (((advance SamplerMachineTable.program)^[t])
      (SamplerMachineTable.cfg (some (.inr .fill)) SamplerMachineTable.initial
        (SamplerMachine.encodeWord (ExecutableSmallBiasSampler.chosenWord n)) []
        (List.replicate L true) [] [] [])).l = none := by
    rw [← SamplerMachineTable.run, hr]
    rfl
  obtain ⟨u, hu, he⟩ := BitMachineInline.outputs (fun l => .inr (.inr l))
    Sum.inr tableRead (by intro v; rfl) none SamplerMachineTable.program program
    (by intro l; rfl)
    (SamplerMachineTable.cfg (some (.inr .fill)) SamplerMachineTable.initial
      (SamplerMachine.encodeWord (ExecutableSmallBiasSampler.chosenWord n)) []
      (List.replicate L true) [] [] []) t hh
  rw [← SamplerMachineTable.run, hr] at he
  refine ⟨u, hu.trans ht, ?_⟩
  simpa only [run, BitMachineInline.cfg] using he

private theorem run_add (t s : ℕ) (q : Config) :
    run (t + s) q = run t (run s q) := Function.iterate_add_apply _ _ _ _

def timeBound (n L : ℕ) : ℕ :=
  SamplerMachineChosenWord.timeBound n + 1 + SamplerMachineTable.timeBound n L

/-- One fixed program performs the canonical modulus search and then writes
the complete ordered sampler table. The only nonempty input banks are the
raw degree word and the persistent unary row length. -/
theorem run_fieldTable (bits : List Bool) (L : ℕ) :
    ∃ t ≤ timeBound bits.length L,
      run t (input bits L) =
        ⟨none, .inr SamplerMachineTable.initial,
          (SamplerMachineTable.cfg none SamplerMachineTable.initial
            (SamplerMachine.encodeWord
              (ExecutableSmallBiasSampler.chosenWord bits.length)) []
            (List.replicate L true) [] []
            (SamplerSeedEnumeration.counterTraceTable bits.length L)).stk⟩ := by
  obtain ⟨tc, s, htc, hc⟩ := chosen_phase bits L
  obtain ⟨tt, htt, ht⟩ := table_phase bits.length L
  refine ⟨tt + (1 + tc), ?_, ?_⟩
  · unfold timeBound
    omega
  · rw [run_add tt (1 + tc), run_add 1 tc, hc]
    rw [switch_step]
    exact ht

end EthInapproximability.CurrentPaper.SamplerMachineFieldTable
