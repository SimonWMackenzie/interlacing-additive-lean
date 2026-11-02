import EthInapproximability.CurrentPaper.MatrixWeightedCanonicalOrderCost
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Charged insertion of the canonical graph-item order into the weighted bank

The source count words `v`, `s - 3`, and `4*s` are explicit inputs here.
The fixed Fin9 canonical-order controller constructs the entire serialized
order word; this wrapper embeds it into the weighted controller's global
slot 60 and physically clears all eight local input/work slots.  Deriving
the three count words from an original graph encoding is separate.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedOrderPreparation

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open MatrixWeightedCanonicalOrderMachine MatrixWeightedCanonicalOrderRun

abbrev Stack := Fin 64
abbrev Control := Option Bool × Option Bool

def slots : Fin 9 ↪ Stack :=
  ⟨![7,8,9,10,11,12,13,14,60], by decide⟩

def scratchSlots : Fin 8 ↪ Stack :=
  ⟨![7,8,9,10,11,12,13,14], by decide⟩

theorem slots_castSucc (i : Fin 8) :
    slots i.castSucc = scratchSlots i := by
  fin_cases i <;> rfl

inductive Label where
  | order (l : MatrixWeightedCanonicalOrderMachine.Label)
  | clear (i : Fin 9)
  | done

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .order l => stmt slots Label.order (fun v => (v, none)) Prod.fst
      (some (.clear 0)) (MatrixWeightedCanonicalOrderMachine.program l)
  | .clear i => if h : i.val < 8 then
      BitMachineClearBank.clearStep (scratchSlots ⟨i.val, h⟩)
        (.clear i) (.clear ⟨i.val + 1, by omega⟩)
    else BitMachineClearBank.finishStep (fun _ => none) .done
  | .done => halt

def start : Label := .order MatrixWeightedCanonicalOrderMachine.start
def initial : Control := (none, none)
def cfg (l : Option Label) (v : Control) (S : Stack → List Bool) : Config :=
  ⟨l, v, S⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

noncomputable def sourceBank (base : Stack → List Bool) (v a K : ℕ) :
    Stack → List Bool :=
  bank slots base (MatrixWeightedCanonicalOrderMachine.initialBank v a K)

noncomputable def producedBank (base : Stack → List Bool) (v a K : ℕ) :
    Stack → List Bool :=
  bank slots base (outputBank v a K)

noncomputable def readyBank (base : Stack → List Bool) (v a K : ℕ) :
    Stack → List Bool :=
  BitMachineClearBank.cleared scratchSlots (producedBank base v a K)

def clearCost (S : Stack → List Bool) : ℕ :=
  (∑ i : Fin 8, (S (scratchSlots i)).length) + 10

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem clear_run (S : Stack → List Bool) :
    run (clearCost S) (cfg (some (.clear 0)) initial S) =
      cfg none initial (BitMachineClearBank.cleared scratchSlots S) := by
  have hs (i : Fin 8) : program (.clear i.castSucc) =
      BitMachineClearBank.clearStep (scratchSlots i)
        (.clear i.castSucc) (.clear i.succ) := by
    simp only [program, Fin.val_castSucc, dif_pos i.isLt]
    rfl
  have hf : program (.clear (Fin.last 8)) =
      BitMachineClearBank.finishStep (fun _ => none) .done := by
    simp only [program, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
  have hr := BitMachineClearBank.clear_bank_run program
    (fun _ => none) .done 8 scratchSlots scratchSlots.injective
    Label.clear hs hf (none : Option Bool) S
  have hd : run 1
      (cfg (some .done) initial (BitMachineClearBank.cleared scratchSlots S)) =
      cfg none initial (BitMachineClearBank.cleared scratchSlots S) := rfl
  simpa only [clearCost, Nat.add_assoc] using (run_add hr 1).trans hd

theorem canonical_order_run (base : Stack → List Bool) (v a K : ℕ) :
    ∃ t ≤ MatrixWeightedCanonicalOrderCost.polynomialCost v a K +
        clearCost (producedBank base v a K),
      run t (cfg (some start) initial (sourceBank base v a K)) =
        cfg none initial (readyBank base v a K) := by
  obtain ⟨n, hn, hr⟩ := complete_run v a K
  change ((advance MatrixWeightedCanonicalOrderMachine.program)^[n])
    ⟨some MatrixWeightedCanonicalOrderMachine.start, none,
      MatrixWeightedCanonicalOrderMachine.initialBank v a K⟩ =
    ⟨none, none, outputBank v a K⟩ at hr
  have hhalt :
      (((advance MatrixWeightedCanonicalOrderMachine.program)^[n])
        ⟨some MatrixWeightedCanonicalOrderMachine.start, none,
          MatrixWeightedCanonicalOrderMachine.initialBank v a K⟩).l = none := by
    rw [hr]
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs slots base
    Label.order (fun q : Option Bool => (q, none)) Prod.fst
    (by intro q; rfl) (some (.clear 0))
    MatrixWeightedCanonicalOrderMachine.program program (by intro l; rfl)
    ⟨some MatrixWeightedCanonicalOrderMachine.start, none,
      MatrixWeightedCanonicalOrderMachine.initialBank v a K⟩ n hhalt
  rw [hr] at he
  have hphase : run u (cfg (some start) initial (sourceBank base v a K)) =
      cfg (some (.clear 0)) initial (producedBank base v a K) := by
    simpa only [run, cfg, start, initial, sourceBank, producedBank,
      BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg] using he
  have hclear := clear_run (producedBank base v a K)
  refine ⟨u + clearCost (producedBank base v a K), ?_, ?_⟩
  · have hpoly := MatrixWeightedCanonicalOrderCost.totalCost_le_polynomial v a K
    omega
  · exact (run_add hphase _).trans hclear

theorem readyBank_order (base : Stack → List Bool) (v a K : ℕ) :
    readyBank base v a K 60 =
      MatrixWeightedCanonicalOrderMachine.canonicalWord v a K := by
  have h60 : ¬ ∃ i : Fin 8, scratchSlots i = (60 : Stack) := by decide
  change (if ∃ i : Fin 8, scratchSlots i = (60 : Stack) then []
      else producedBank base v a K 60) =
    MatrixWeightedCanonicalOrderMachine.canonicalWord v a K
  simp only [if_neg h60]
  change (bank slots base (outputBank v a K)) (slots 8) =
    MatrixWeightedCanonicalOrderMachine.canonicalWord v a K
  rw [bank_at, outputBank_table]

theorem readyBank_scratch (base : Stack → List Bool) (v a K : ℕ)
    (i : Fin 8) : readyBank base v a K (scratchSlots i) = [] := by
  change (if ∃ j : Fin 8, scratchSlots j = scratchSlots i then []
      else producedBank base v a K (scratchSlots i)) = []
  simp only [if_pos (show ∃ j : Fin 8, scratchSlots j = scratchSlots i from
    ⟨i, rfl⟩)]

theorem readyBank_frame (base : Stack → List Bool) (v a K : ℕ)
    (k : Stack) (hk : ∀ i : Fin 9, slots i ≠ k) :
    readyBank base v a K k = base k := by
  have hscratch : ¬ ∃ i : Fin 8, scratchSlots i = k := by
    rintro ⟨i, hi⟩
    have hslot : slots i.castSucc = scratchSlots i := by
      fin_cases i <;> rfl
    exact hk i.castSucc (hslot.trans hi)
  change (if ∃ i : Fin 8, scratchSlots i = k then []
      else producedBank base v a K k) = base k
  simp only [if_neg hscratch]
  exact bank_outside slots base (outputBank v a K) k
    (by rintro ⟨i, hi⟩; exact hk i hi)

theorem clearCost_produced (base : Stack → List Bool) (v a K : ℕ) :
    clearCost (producedBank base v a K) =
      v + a + K + (v + K * (a + v)) + 10 := by
  have hslot (i : Fin 8) : scratchSlots i = slots i.castSucc := by
    fin_cases i <;> rfl
  have hread (i : Fin 8) :
      producedBank base v a K (scratchSlots i) = outputBank v a K i.castSucc := by
    rw [hslot]
    exact bank_at slots base (outputBank v a K) i.castSucc
  simp_rw [clearCost, hread]
  simp [Fin.sum_univ_succ, outputBank]
  omega

def prepCost (v a K : ℕ) : ℕ :=
  MatrixWeightedCanonicalOrderCost.polynomialCost v a K +
    v + a + K + (v + K * (a + v)) + 10

theorem canonical_order_polynomial_run
    (base : Stack → List Bool) (v a K : ℕ) :
    ∃ t ≤ prepCost v a K,
      run t (cfg (some start) initial (sourceBank base v a K)) =
        cfg none initial (readyBank base v a K) := by
  obtain ⟨t, ht, he⟩ := canonical_order_run base v a K
  refine ⟨t, ?_, he⟩
  rw [clearCost_produced] at ht
  simpa only [prepCost, Nat.add_assoc] using ht

theorem readyBank_eq_base (base : Stack → List Bool) (v a K : ℕ)
    (hword : base 60 = MatrixWeightedCanonicalOrderMachine.canonicalWord v a K)
    (hscratch : ∀ i : Fin 8, base (scratchSlots i) = []) :
    readyBank base v a K = base := by
  funext k
  by_cases hk60 : k = 60
  · subst k
    exact (readyBank_order base v a K).trans hword.symm
  by_cases hscratchAt : ∃ i : Fin 8, scratchSlots i = k
  · obtain ⟨i, hi⟩ := hscratchAt
    rw [← hi, readyBank_scratch, hscratch]
  · have houtside : ∀ i : Fin 9, slots i ≠ k := by
      intro i hi
      by_cases hi8 : i.val < 8
      · let j : Fin 8 := ⟨i.val, hi8⟩
        have hij : i = j.castSucc := Fin.ext rfl
        rw [hij] at hi
        exact hscratchAt ⟨j, (slots_castSucc j).symm.trans hi⟩
      · have hiLast : i = (8 : Fin 9) := Fin.ext (by omega)
        rw [hiLast] at hi
        exact hk60 hi.symm
    exact readyBank_frame base v a K k houtside

theorem graph_order_word {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (base : Stack → List Bool)
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (s : ℕ) :
    readyBank base (Fintype.card V) (s - 3) (4 * s) 60 =
      MatrixWeightedRowOrderLookup.orderWord (GraphVectors.itemOrder G s) := by
  rw [readyBank_order,
    MatrixWeightedCanonicalOrderBridge.canonicalWord_itemOrder G s]

end EthInapproximability.CurrentPaper.MatrixWeightedOrderPreparation
