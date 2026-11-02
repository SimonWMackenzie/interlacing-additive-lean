import EthInapproximability.CurrentPaper.MatrixRestorationWidthMachineProduct
import EthInapproximability.CurrentPaper.ExactParameterMachineLog
import EthInapproximability.CurrentPaper.MatrixUnaryPower
import EthInapproximability.CurrentPaper.BitMachineComposition
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Physical restoration-width scalar producer

Source: locked v8 `F-parameter-choices.tex`, Eq. (F.3):
`Q = 2^ceil(log₂(80 b⁺/δ_U)) = 2^clog₂(1280 b⁺ c_src s q)`.
The inputs here are four separate physical unary words for `b,c,s,q`.
The fixed product machine writes the target, then two existing fixed
machines physically compute its ceiling logarithm and power of two. Both
intermediate words are transferred one Boolean cell per transition.
-/

namespace EthInapproximability.CurrentPaper.MatrixRestorationWidthMachine

open Turing BitMachineEncoding BitMachineComposition

noncomputable def productMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 12) (8 : Fin 12)
    MatrixRestorationWidthMachineProduct.Label.constant false
    MatrixRestorationWidthMachineProduct.program

noncomputable def postMachine : BitMachine.Machine :=
  BitMachineComposition.composition ExactParameterMachineLog.machine
    MatrixUnaryPower.machine

abbrev Stack := BitMachineComposition.Stack productMachine postMachine
abbrev Label := BitMachineComposition.Label productMachine postMachine
abbrev Control := BitMachineComposition.Control productMachine postMachine
abbrev Config := BitMachineComposition.Config productMachine postMachine

noncomputable def program : Label →
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineComposition.program productMachine postMachine

def unary (n : ℕ) : List Bool := List.replicate n true
def target (b c s q : ℕ) : ℕ := 1280*b*c*s*q
def width (b c s q : ℕ) : ℕ := 2 ^ Nat.clog 2 (target b c s q)

noncomputable def productStart (b c s q : ℕ) : productMachine.Config :=
  renameCfg (Fintype.equivFin MatrixRestorationWidthMachineProduct.Stack)
    (Fintype.equivFin MatrixRestorationWidthMachineProduct.Label)
    (Fintype.equivFin MatrixRestorationWidthMachineProduct.Control)
    (MatrixRestorationWidthMachineProduct.cfg (some .constant) false
      (MatrixRestorationWidthMachineProduct.inputBank b c s q))

noncomputable def productEnd (b c s q : ℕ) : productMachine.Config :=
  renameCfg (Fintype.equivFin MatrixRestorationWidthMachineProduct.Stack)
    (Fintype.equivFin MatrixRestorationWidthMachineProduct.Label)
    (Fintype.equivFin MatrixRestorationWidthMachineProduct.Control)
    (MatrixRestorationWidthMachineProduct.cfg none false
      (MatrixRestorationWidthMachineProduct.outputBank b c s q))

noncomputable def startCfg (b c s q : ℕ) : Config :=
  BitMachineComposition.leftCfg productMachine postMachine
    (productStart b c s q)

noncomputable def outputStack : Stack := .inr (.inl postMachine.output)

noncomputable def startLabel : Label := .inl productMachine.start
noncomputable def initialControl : Control :=
  (productMachine.initial, postMachine.initial, none)

noncomputable def inputStack (i : Fin 4) : Stack :=
  .inl (Fintype.equivFin MatrixRestorationWidthMachineProduct.Stack
    ⟨i.val, by omega⟩)

theorem startCfg_label (b c s q : ℕ) :
    (startCfg b c s q).l = some startLabel := rfl

theorem startCfg_control (b c s q : ℕ) :
    (startCfg b c s q).var = initialControl := rfl

theorem startCfg_input (b c s q : ℕ) (i : Fin 4) :
    (startCfg b c s q).stk (inputStack i) =
      unary (![b,c,s,q] i) := by
  change (MatrixRestorationWidthMachineProduct.inputBank b c s q)
    ((Fintype.equivFin (Fin 12)).symm
      ((Fintype.equivFin (Fin 12)) ⟨i.val, by omega⟩)) = _
  rw [Equiv.symm_apply_apply]
  fin_cases i <;> rfl

theorem startCfg_post_empty (b c s q : ℕ)
    (k : Fin postMachine.stackCount ⊕ Unit) :
    (startCfg b c s q).stk (.inr k) = [] := rfl

def productTime (b c s q : ℕ) : ℕ :=
  MatrixRestorationWidthMachineProduct.productTime b c s q

noncomputable def postTime (b c s q : ℕ) : ℕ :=
  let t := target b c s q
  let e := Nat.clog 2 t
  (UnaryBinaryEncoding.coefficient + 6) * (t+1)^2 +
    2*e+2+16*width b c s q

noncomputable def totalTime (b c s q : ℕ) : ℕ :=
  productTime b c s q + 2*target b c s q+2 + postTime b c s q

theorem product_run (b c s q : ℕ) :
    ∃ t ≤ productTime b c s q,
      productMachine.run t (productStart b c s q) = productEnd b c s q := by
  obtain ⟨t, ht, hr⟩ := MatrixRestorationWidthMachineProduct.product_run b c s q
  refine ⟨t, ht, ?_⟩
  simpa only [productMachine, productStart, productEnd, productTime,
    BitMachineEncoding.ofFinite_run] using
    (BitMachineEncoding.ofFinite_run
      (0 : Fin 12) (8 : Fin 12)
      MatrixRestorationWidthMachineProduct.Label.constant false
      MatrixRestorationWidthMachineProduct.program
      (MatrixRestorationWidthMachineProduct.cfg (some .constant) false
        (MatrixRestorationWidthMachineProduct.inputBank b c s q)) t).trans
      (congrArg
        (renameCfg (Fintype.equivFin MatrixRestorationWidthMachineProduct.Stack)
          (Fintype.equivFin MatrixRestorationWidthMachineProduct.Label)
          (Fintype.equivFin MatrixRestorationWidthMachineProduct.Control)) hr)

theorem productEnd_output (b c s q : ℕ) :
    (productEnd b c s q).stk productMachine.output = unary (target b c s q) := by
  change (MatrixRestorationWidthMachineProduct.outputBank b c s q)
    ((Fintype.equivFin (Fin 12)).symm ((Fintype.equivFin (Fin 12)) 8)) = _
  rw [Equiv.symm_apply_apply]
  change MatrixRestorationWidthMachineProduct.unary (1280*b*c*s*q) =
    unary (target b c s q)
  rfl

theorem post_outputs (b c s q : ℕ) :
    postMachine.OutputsWithin (unary (target b c s q))
      (unary (width b c s q)) (postTime b c s q) := by
  let t := target b c s q
  let e := Nat.clog 2 t
  have hlog := ExactParameterMachineLog.outputs t
  have hpow := MatrixUnaryPower.outputs (unary e)
  have hcomp := BitMachineComposition.composition_outputsWithin
    ExactParameterMachineLog.machine MatrixUnaryPower.machine hlog hpow
  simpa only [postMachine, postTime, target, width, unary,
    List.length_replicate, t, e] using hcomp

/-- An actual fixed finite-bank run from four unary input banks to unary
`Q`. The final state is the exact right-machine configuration, so every
private bank can be inspected and charged by later consumers. -/
theorem width_run (b c s q : ℕ) :
    ∃ t ≤ totalTime b c s q, ∃ v ≤ postTime b c s q, ∃ cfinal : Config,
      ((advance program)^[t]) (startCfg b c s q) = cfinal ∧
      cfinal = BitMachineComposition.rightCfg productMachine postMachine
        (productEnd b c s q).var
        (Function.update (productEnd b c s q).stk productMachine.output [])
        (postMachine.run v (postMachine.init (unary (target b c s q)))) ∧
      cfinal.l = none ∧ cfinal.stk outputStack = unary (width b c s q) := by
  let A := productMachine
  let B := postMachine
  let x := unary (target b c s q)
  obtain ⟨u, hu, hur⟩ := product_run b c s q
  obtain ⟨a, ha, hah, hae, hafirst⟩ :=
    BitMachineSubroutine.first_halt_cfg A.program (productStart b c s q) u
      (by change (A.run u (productStart b c s q)).l = none
          rw [hur]
          rfl)
  have hae' : A.run a (productStart b c s q) = productEnd b c s q := by
    change A.run a (productStart b c s q) = A.run u (productStart b c s q) at hae
    rw [hur] at hae
    exact hae
  have hleft := BitMachineComposition.left_run A B (productStart b c s q) a
    (by simpa only [BitMachine.Machine.run] using hafirst)
  have htransfer := BitMachineComposition.transfer_run A B
    (productEnd b c s q) rfl
  obtain ⟨v, hv, hvhalt, hvout⟩ := post_outputs b c s q
  let d := B.run v (B.init x)
  have hright := BitMachineComposition.right_run A B
    (productEnd b c s q).var
    (Function.update (productEnd b c s q).stk A.output []) (B.init x) v
  let cfinal := BitMachineComposition.rightCfg A B (productEnd b c s q).var
    (Function.update (productEnd b c s q).stk A.output []) d
  have hx : (productEnd b c s q).stk A.output = x :=
    productEnd_output b c s q
  have hr : ((advance program)^[a+2*x.length+2+v]) (startCfg b c s q) = cfinal := by
    change ((advance (BitMachineComposition.program A B))^[a+2*x.length+2+v])
      (BitMachineComposition.leftCfg A B (productStart b c s q)) = cfinal
    rw [show a+2*x.length+2+v =
      v+((x.length+1+(x.length+1))+a) by omega,
      Function.iterate_add_apply, Function.iterate_add_apply, hleft, hae']
    rw [← hx, htransfer, hx, hright]
  refine ⟨a+2*x.length+2+v, by
    have hxlen : x.length = target b c s q := by simp [x, unary]
    change a+2*x.length+2+v ≤
      productTime b c s q + 2*target b c s q+2 + postTime b c s q
    rw [hxlen]
    omega, v, hv, cfinal, hr, rfl, ?_, ?_⟩
  · have hd : d.l = none := hvhalt
    simp only [cfinal, BitMachineComposition.rightCfg,
      renameCfg, liftCfg, hd, Option.map_none]
  · simpa only [cfinal, outputStack,
      BitMachineComposition.rightCfg, renameCfg, liftCfg,
      BitMachineComposition.stackSwap, Equiv.symm_apply_apply,
      Sum.elim_inl, d] using hvout

set_option maxHeartbeats 1000000 in
-- Nonlinear polynomial accounting combines four physical multiplication phases
-- with the charged logarithm/power composition in one arithmetic certificate.
theorem totalTime_output_poly (b c s q : ℕ) :
    let H := b+c+s+q+width b c s q+1
    totalTime b c s q ≤ (3000+4*UnaryBinaryEncoding.coefficient)*H^4 := by
  let Q := width b c s q
  let H := b+c+s+q+Q+1
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hb : b ≤ H := by dsimp [H]; omega
  have hc : c ≤ H := by dsimp [H]; omega
  have hs : s ≤ H := by dsimp [H]; omega
  have hq : q ≤ H := by dsimp [H]; omega
  have hQ : Q ≤ H := by dsimp [H]; omega
  have hTQ : target b c s q ≤ Q :=
    Nat.le_pow_clog (by decide : 1 < 2) (target b c s q)
  have hT : target b c s q ≤ H := hTQ.trans hQ
  have hbc : b*c ≤ H^2 := by
    calc b*c ≤ H*H := Nat.mul_le_mul hb hc
      _ = H^2 := by ring
  have hbcs : b*c*s ≤ H^3 := by
    calc b*c*s ≤ H^2*H := Nat.mul_le_mul hbc hs
      _ = H^3 := by ring
  have hbcsq : b*c*s*q ≤ H^4 := by
    calc b*c*s*q ≤ H^3*H := Nat.mul_le_mul hbcs hq
      _ = H^4 := by ring
  have h1 : 1 ≤ H^4 := Nat.one_le_pow _ _ hH
  have hpow1 : H ≤ H^4 := by
    simpa using Nat.pow_le_pow_right hH (show 1 ≤ 4 by omega)
  have hpow2 : H^2 ≤ H^4 := Nat.pow_le_pow_right hH (by omega)
  have hpow3 : H^3 ≤ H^4 := Nat.pow_le_pow_right hH (by omega)
  have hproduct : productTime b c s q ≤ 2600*H^4 := by
    have hbc4 := hbc.trans hpow2
    have hbcs4 := hbcs.trans hpow3
    have hb4 := hb.trans hpow1
    have hf : productTime b c s q =
        17 + 4*b + 6*(b*c) + 6*(b*c*s) + 2566*(b*c*s*q) := by
      dsimp [productTime, MatrixRestorationWidthMachineProduct.productTime,
        MatrixAddressMachine.exactTime]
      ring
    rw [hf]
    omega
  have he : Nat.clog 2 (target b c s q) ≤ Q := by
    have hh : Nat.clog 2 (target b c s q) <
        2 ^ Nat.clog 2 (target b c s q) := Nat.lt_two_pow_self
    change Nat.clog 2 (target b c s q) < Q at hh
    omega
  have heH : Nat.clog 2 (target b c s q) ≤ H := he.trans hQ
  have hT1 : target b c s q + 1 ≤ 2*H := by omega
  have hsquare : (target b c s q + 1)^2 ≤ 4*H^2 := by nlinarith
  have hpost : postTime b c s q ≤
      (4*UnaryBinaryEncoding.coefficient+100)*H^4 := by
    dsimp [postTime]
    have hm := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient+6) hsquare
    nlinarith [hT, hQ, heH, h1, hpow1, hpow2]
  have htotal : totalTime b c s q =
      productTime b c s q + 2*target b c s q+2 + postTime b c s q := rfl
  rw [htotal]
  change productTime b c s q + 2*target b c s q+2 + postTime b c s q ≤
    (3000+4*UnaryBinaryEncoding.coefficient)*H^4
  nlinarith [hproduct, hpost, hT, hpow1, h1]

theorem width_run_output_poly (b c s q : ℕ) :
    let H := b+c+s+q+width b c s q+1
    ∃ t ≤ (3000+4*UnaryBinaryEncoding.coefficient)*H^4, ∃ cfinal : Config,
      ((advance program)^[t]) (startCfg b c s q) = cfinal ∧
      cfinal.l = none ∧ cfinal.stk outputStack = unary (width b c s q) := by
  obtain ⟨t, ht, v, hv, cf, hr, he, hh, ho⟩ := width_run b c s q
  exact ⟨t, ht.trans (totalTime_output_poly b c s q), cf, hr, hh, ho⟩

noncomputable def embeddedProgram {K : Type*} [DecidableEq K]
    (ι : Stack ↪ K) : Label → TM2.Stmt (fun _ : K => Bool) Label Control :=
  fun l => BitMachineStackEmbedding.stmt ι id id id none (program l)

/-- The same fixed computation runs inside arbitrary larger finite banks.
Every ambient bank outside the selected injection retains its original
contents, including nonempty source or matrix state. -/
theorem embedded_width_run {K : Type*} [DecidableEq K]
    (ι : Stack ↪ K) (foreign : K → List Bool) (b c s q : ℕ) :
    let H := b+c+s+q+width b c s q+1
    ∃ t ≤ (3000+4*UnaryBinaryEncoding.coefficient)*H^4,
      ∃ v ≤ postTime b c s q, ∃ cf : Config,
      ((advance (embeddedProgram ι))^[t])
        (BitMachineStackEmbedding.cfg ι foreign id id none (startCfg b c s q)) =
          BitMachineStackEmbedding.cfg ι foreign id id none cf ∧
      cf = BitMachineComposition.rightCfg productMachine postMachine
        (productEnd b c s q).var
        (Function.update (productEnd b c s q).stk productMachine.output [])
        (postMachine.run v (postMachine.init (unary (target b c s q)))) ∧
      cf.l = none ∧ cf.stk outputStack = unary (width b c s q) := by
  obtain ⟨u, hu, v, hv, cf, hr, he, hh, ho⟩ := width_run b c s q
  have hhalt : (((advance program)^[u]) (startCfg b c s q)).l = none := by
    rw [hr]
    exact hh
  obtain ⟨t, ht, hem⟩ := BitMachineStackEmbedding.outputs
    ι foreign id id id (fun _ => rfl) none program
    (embeddedProgram ι) (fun _ => rfl) (startCfg b c s q) u hhalt
  refine ⟨t, (ht.trans hu).trans (totalTime_output_poly b c s q),
    v, hv, cf, ?_, he, hh, ho⟩
  simpa only [hr] using hem

theorem width_eq_parameters (i : Parameters.Input) :
    width i.nextDepth i.sourceConstant (Parameters.bins i)
      (Parameters.outerWidth i) = Parameters.restorationWidth i := rfl

end EthInapproximability.CurrentPaper.MatrixRestorationWidthMachine
