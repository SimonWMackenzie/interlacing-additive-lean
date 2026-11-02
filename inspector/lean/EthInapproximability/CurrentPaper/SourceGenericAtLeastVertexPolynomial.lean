import EthInapproximability.CurrentPaper.SourceGenericPairUnitEnvelope
import EthInapproximability.CurrentPaper.GenericAtLeastLoop

/-! Charged polynomial clock for one physical generic at-least-one vertex
callback, `AtLeastClock.cost`: the opening negative unit, all `a` ordered
positive OR gates, and the closing positive unit, each with its physical
cleanup charged from the literal per-transition stack growth of the
preceding run. The saved and count words grow inside the callback; every
phase is bounded at the largest bank it can see. Coefficients depend only
on the fixed alphabet `a` and arity `q`, never on `n`, the vertex, or the
bank words. No premise on `a`, `q`, the bank, or the run is added. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixClock

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceGenericPrefixMachine SourceBooleanPrefix
open SourceClauseEncoding EncodedCNF
open scoped Classical
set_option maxHeartbeats 2000000

/-! ## Gate preparation and row-writer phase -/

theorem at_gate_pre_le_poly (n a r s slot w : Nat) (sign : Bool) :
    GateOperands.cost a s w (List.replicate r true) +
      SourceClauseRowGate.cost r a s n s slot w sign + 1 ≤
      100000*(UnaryBinaryEncoding.coefficient+1)*
        (n+a+r+s+slot+w+5)^4 := by
  let M := n+a+r+s+slot+w+5
  have hm : 5 ≤ M := by dsimp [M]; omega
  have hn : n ≤ M := by dsimp [M]; omega
  have ha : a ≤ M := by dsimp [M]; omega
  have hr : r ≤ M := by dsimp [M]; omega
  have hs : s ≤ M := by dsimp [M]; omega
  have hslot : slot ≤ M := by dsimp [M]; omega
  have hw : w ≤ M := by dsimp [M]; omega
  have hsize (i : Fin 5) : GateOperands.constantSize a s w i ≤ M := by
    fin_cases i <;> simp [GateOperands.constantSize] <;> omega
  have hbatch := SourceClauseCallbackPrimitivePolynomial.costPrefix_le
    (GateOperands.constantSize a s w) M hsize 5
  have hra : r*a ≤ M^2 := by
    have h := Nat.mul_le_mul hr ha
    simpa [pow_two] using h
  have hna : n*a ≤ M^2 := by
    have h := Nat.mul_le_mul hn ha
    simpa [pow_two] using h
  have hsw : slot*w ≤ M^2 := by
    have h := Nat.mul_le_mul hslot hw
    simpa [pow_two] using h
  have hm2 : M ≤ M^2 := by nlinarith
  have hp1 : r*a+s+1 ≤ 2*M^2 := by omega
  have hp2 : slot*w+(n*a+s)+1 ≤ 3*M^2 := by omega
  have hsq1 : (r*a+s+1)^2 ≤ 4*M^4 := by
    have h := Nat.mul_le_mul hp1 hp1
    nlinarith only [h]
  have hsq2 : (slot*w+(n*a+s)+1)^2 ≤ 9*M^4 := by
    have h := Nat.mul_le_mul hp2 hp2
    nlinarith only [h]
  have hbits1 : (r*a+s).bits.length ≤ 2*M^2 := by
    have h := ClockStepSemantics.bits_length_le (r*a+s)
    omega
  have hbits2 : (slot*w+(n*a+s)).bits.length ≤ 3*M^2 := by
    have h := ClockStepSemantics.bits_length_le (slot*w+(n*a+s))
    omega
  have hbits3 : (slot*w+(n*a+s)+1).bits.length ≤ 3*M^2 := by
    have h := ClockStepSemantics.bits_length_le (slot*w+(n*a+s)+1)
    omega
  have hbits4 : (n*a+s).bits.length ≤ 2*M^2 := by
    have h := ClockStepSemantics.bits_length_le (n*a+s)
    omega
  have hm24 : M^2 ≤ M^4 := by
    calc
      M^2 = M*M := by ring
      _ ≤ M^2*M^2 := Nat.mul_le_mul hm2 hm2
      _ = M^4 := by ring
  have hm14 : M ≤ M^4 := hm2.trans hm24
  have hm04 : 1 ≤ M^4 := by omega
  have hcoeff1 := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hsq1
  have hcoeff2 := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hsq2
  change _ ≤ 100000*(UnaryBinaryEncoding.coefficient+1)*M^4
  simp only [GateOperands.cost, SourceClauseRowGate.cost,
    SourceClauseGateSlotAddress.cost, SourceLiteralWriter.emitTime,
    SourceLiteralWriter.words, SourceClauseGatePrepare.firstClause,
    SourceClauseGatePrepare.secondClause,
    SourceClauseGatePrepare.thirdClause,
    MatrixAddressMachine.exactTime,
    SourceClauseEncoding.positive, SourceClauseEncoding.negative,
    SourceClauseEncoding.negate, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, List.length_replicate]
  nlinarith only [hbatch, hsq1, hsq2, hbits1, hbits2, hbits3,
    hbits4, hna, hra, hsw, hn, ha, hr, hs, hslot, hw,
    hm14, hm24, hm04, hcoeff1, hcoeff2,
    Nat.zero_le (UnaryBinaryEncoding.coefficient*M^4)]

/-! ## Gate phase including its physical cleanup -/

noncomputable def atGatePre {n a : Nat} (q : Nat) (v : Fin n) (s : Fin a) :
    Nat :=
  GateOperands.cost a s.val (SourceBooleanEncoding.width a q + 1)
      (List.replicate v.val true) +
    SourceClauseRowGate.cost v.val a s.val n s.val v.val
      (SourceBooleanEncoding.width a q + 1) true + 1

theorem at_gate_cost_le_envelope {n a q : Nat} (v : Fin n) (s : Fin a)
    (saved output count : List Bool) :
    AtLeastClock.gateCost (q := q) v s saved output count ≤
      atGatePre q v s +
      PrefixLoopCost.workCount *
        ((n+v.val+saved.length+output.length+count.length) +
          BitMachineStackGrowth.perStep
            (GateCycle.pairProgram a s.val
              (SourceBooleanEncoding.width a q + 1)) *
            atGatePre q v s) +
      PrefixLoopCost.workCount+3 := by
  obtain ⟨t,ht,hr⟩ := GateCycle.pair_run (q := q) v s saved output count
  have hc := PrefixLoopCost.clear_after_run
    (GateCycle.pairProgram a s.val (SourceBooleanEncoding.width a q + 1))
    _ _ (PrefixGateReady.blank n v.val saved output count) _
    t (atGatePre q v s)
    (n+v.val+saved.length+output.length+count.length)
    ht hr (PrefixLoopCost.blank_word_bound n v.val saved output count)
  have hpre : atGatePre q v s =
      GateOperands.cost a s.val (SourceBooleanEncoding.width a q + 1)
          (List.replicate v.val true) +
        SourceClauseRowGate.cost v.val a s.val n s.val v.val
          (SourceBooleanEncoding.width a q + 1) true + 1 := rfl
  dsimp only [AtLeastClock.gateCost]
  omega

/-! ## Fixed-(a,q) per-transition growth coefficients -/

noncomputable def atUnitStep (a q : Nat) : Nat :=
  BitMachineStackGrowth.perStep
      (UnitCycle.pairProgram a (SourceBooleanEncoding.width a q+1) 0 false) +
    BitMachineStackGrowth.perStep
      (UnitCycle.pairProgram a (SourceBooleanEncoding.width a q+1) a true)

/-- The sum over the `a` fixed gate programs; it is a function of the fixed
`a,q` only. -/
noncomputable def atGateStep (a q : Nat) : Nat :=
  ∑ s : Fin a, BitMachineStackGrowth.perStep
    (GateCycle.pairProgram a s.val (SourceBooleanEncoding.width a q + 1))

theorem at_gate_step_le (a q : Nat) (s : Fin a) :
    BitMachineStackGrowth.perStep
      (GateCycle.pairProgram a s.val (SourceBooleanEncoding.width a q + 1)) ≤
      atGateStep a q :=
  Finset.single_le_sum
    (f := fun s : Fin a => BitMachineStackGrowth.perStep
      (GateCycle.pairProgram a s.val (SourceBooleanEncoding.width a q + 1)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)

/-- Size used for one vertex callback, at bank-length bounds `S O C`. -/
def atSize (n a q S O C : Nat) : Nat :=
  3*n+2*a+SourceBooleanEncoding.width a q+6+S+O+C

noncomputable def atUnitCoefficient (a q : Nat) : Nat :=
  (16*UnaryBinaryEncoding.coefficient+100)*
    (1+PrefixLoopCost.workCount*atUnitStep a q)+
    2*PrefixLoopCost.workCount+4

noncomputable def atGateCoefficient (a q : Nat) : Nat :=
  100000*(UnaryBinaryEncoding.coefficient+1)*
    (1+PrefixLoopCost.workCount*atGateStep a q)+
    2*PrefixLoopCost.workCount+4

private theorem one_le_pow_four {Z : Nat} (hZ : 1 ≤ Z) :
    Z ≤ Z^4 ∧ 1 ≤ Z^4 := by
  have h2 : Z ≤ Z^2 := by nlinarith
  have h24 : Z^2 ≤ Z^4 := by
    calc
      Z^2 = Z*Z := by ring
      _ ≤ Z^2*Z^2 := Nat.mul_le_mul h2 h2
      _ = Z^4 := by ring
  exact ⟨h2.trans h24, by omega⟩

theorem at_unit_cost_le_poly {n a q : Nat} (v : Fin n) (ell : Nat)
    (sign : Bool) (saved output count : List Bool) (S O C : Nat)
    (hcase : (ell=0 ∧ sign=false) ∨ (ell=a ∧ sign=true))
    (hS : saved.length ≤ S) (hO : output.length ≤ O)
    (hC : count.length ≤ C) :
    UnitCycle.cost n a v.val (SourceBooleanEncoding.width a q+1) ell sign
      saved output count ≤
    atUnitCoefficient a q * (atSize n a q S O C)^4 := by
  have hD : BitMachineStackGrowth.perStep
      (UnitCycle.pairProgram a (SourceBooleanEncoding.width a q+1) ell sign) ≤
      atUnitStep a q := by
    rcases hcase with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rw [h1,h2]
      dsimp only [atUnitStep]
      omega
    · rw [h1,h2]
      dsimp only [atUnitStep]
      omega
  have hell : ell ≤ a := by
    rcases hcase with ⟨h1,_⟩ | ⟨h1,_⟩ <;> omega
  let w := SourceBooleanEncoding.width a q+1
  let Z := atSize n a q S O C
  let P := UnitCycle.pairCost n a v.val w ell saved output count
  let D := BitMachineStackGrowth.perStep (UnitCycle.pairProgram a w ell sign)
  let H := n+v.val+saved.length+output.length+count.length
  let K := 16*UnaryBinaryEncoding.coefficient+100
  let W := PrefixLoopCost.workCount
  have hv := v.isLt
  have hM : n+a+v.val+w+ell+1 ≤ Z := by
    dsimp [Z,atSize,w]
    omega
  have hP : P ≤ K*Z^4 := by
    have hp := SourceGenericPairEnumeration.unit_pairCost_le_poly
      n a v.val w ell saved output count
    have hm := pow_le_pow_left₀ (by omega) hM 4
    exact hp.trans (Nat.mul_le_mul_left K hm)
  have hH : H ≤ Z := by dsimp [H,Z,atSize]; omega
  have hZ1 : 1 ≤ Z := by dsimp [Z,atSize]; omega
  obtain ⟨hZ4,hZ41⟩ := one_le_pow_four hZ1
  have henv := SourceGenericPairEnumeration.unit_cost_le_envelope
    n a v.val w ell sign saved output count
  have hdp := Nat.mul_le_mul hD hP
  have hmass := Nat.mul_le_mul_left W
    (show H+D*P ≤ (1+atUnitStep a q*K)*Z^4 by
      nlinarith only [hH,hZ4,hdp])
  change UnitCycle.cost n a v.val w ell sign saved output count ≤
    (K*(1+W*atUnitStep a q)+2*W+4)*Z^4
  change UnitCycle.cost n a v.val w ell sign saved output count ≤
    P+W*(H+D*P)+W+3 at henv
  have hextra : W+3 ≤ (W+4)*Z^4 := by
    have hW := Nat.mul_le_mul_left W hZ41
    have h4 := Nat.mul_le_mul_left 4 hZ41
    calc
      W+3 ≤ W*Z^4+4*Z^4 := by omega
      _ = (W+4)*Z^4 := by ring
  calc
    _ ≤ P+W*(H+D*P)+W+3 := henv
    _ ≤ K*Z^4+W*((1+atUnitStep a q*K)*Z^4)+(W+4)*Z^4 := by omega
    _ = (K*(1+W*atUnitStep a q)+2*W+4)*Z^4 := by ring

theorem at_gate_cost_le_poly {n a q : Nat} (v : Fin n) (s : Fin a)
    (saved output count : List Bool) (S O C : Nat)
    (hS : saved.length ≤ S) (hO : output.length ≤ O)
    (hC : count.length ≤ C) :
    AtLeastClock.gateCost (q := q) v s saved output count ≤
      atGateCoefficient a q * (atSize n a q S O C)^4 := by
  let w := SourceBooleanEncoding.width a q+1
  let Z := atSize n a q S O C
  let P := atGatePre q v s
  let D := BitMachineStackGrowth.perStep (GateCycle.pairProgram a s.val w)
  let H := n+v.val+saved.length+output.length+count.length
  let K := 100000*(UnaryBinaryEncoding.coefficient+1)
  let W := PrefixLoopCost.workCount
  have hv := v.isLt
  have hs := s.isLt
  have hM : n+a+v.val+s.val+v.val+w+5 ≤ Z := by
    dsimp [Z,atSize,w]
    omega
  have hP : P ≤ K*Z^4 := by
    have hp := at_gate_pre_le_poly n a v.val s.val v.val w true
    have hm := pow_le_pow_left₀ (by omega) hM 4
    exact hp.trans (Nat.mul_le_mul_left K hm)
  have hD : D ≤ atGateStep a q := at_gate_step_le a q s
  have hH : H ≤ Z := by dsimp [H,Z,atSize]; omega
  have hZ1 : 1 ≤ Z := by dsimp [Z,atSize]; omega
  obtain ⟨hZ4,hZ41⟩ := one_le_pow_four hZ1
  have henv := at_gate_cost_le_envelope (q := q) v s saved output count
  have hdp := Nat.mul_le_mul hD hP
  have hmass := Nat.mul_le_mul_left W
    (show H+D*P ≤ (1+atGateStep a q*K)*Z^4 by
      nlinarith only [hH,hZ4,hdp])
  change AtLeastClock.gateCost (q := q) v s saved output count ≤
    (K*(1+W*atGateStep a q)+2*W+4)*Z^4
  change AtLeastClock.gateCost (q := q) v s saved output count ≤
    P+W*(H+D*P)+W+3 at henv
  have hextra : W+3 ≤ (W+4)*Z^4 := by
    have hW := Nat.mul_le_mul_left W hZ41
    have h4 := Nat.mul_le_mul_left 4 hZ41
    calc
      W+3 ≤ W*Z^4+4*Z^4 := by omega
      _ = (W+4)*Z^4 := by ring
  calc
    _ ≤ P+W*(H+D*P)+W+3 := henv
    _ ≤ K*Z^4+W*((1+atGateStep a q*K)*Z^4)+(W+4)*Z^4 := by omega
    _ = (K*(1+W*atGateStep a q)+2*W+4)*Z^4 := by ring

/-! ## All `a` gates of one vertex, with the growing bank charged -/

theorem at_gateList_cost_le {n a q : Nat} (v : Fin n)
    (output : List Bool) (S C E : Nat)
    (hE : ∀ (s : Fin a) (saved count : List Bool),
      saved.length ≤ S → count.length ≤ C →
        AtLeastClock.gateCost (q := q) v s saved output count ≤ E) :
    ∀ (ss : List (Fin a)) (saved count : List Bool),
      saved.length +
          (ss.flatMap (AtLeastCircuit.gatePayload (q := q) v)).length ≤ S →
      count.length + 3*ss.length ≤ C →
      AtLeastClock.gateListCost (q := q) v ss saved output count ≤
        ss.length*(E+1)+1 := by
  intro ss
  induction ss with
  | nil =>
      intro saved count _ _
      simp [AtLeastClock.gateListCost]
  | cons s ss ih =>
      intro saved count hS hC
      simp only [List.flatMap_cons,List.length_append] at hS
      simp only [List.length_cons] at hC
      have hhead := hE s saved count (by omega) (by omega)
      have htail := ih
        ((AtLeastCircuit.gatePayload (q := q) v s).reverse ++ saved)
        (List.replicate 3 true ++ count)
        (by simp only [List.length_append,List.length_reverse]; omega)
        (by simp only [List.length_append,List.length_replicate]; omega)
      simp only [AtLeastClock.gateListCost,List.length_cons]
      have e : (ss.length+1)*(E+1) = ss.length*(E+1)+(E+1) := by ring
      omega

/-! ## Source word of one at-least chain -/

def atVariableBound (n a q : Nat) : Nat :=
  n*a + n*(SourceBooleanEncoding.width a q + 1) + a + 1

def atWordBound (n a q : Nat) : Nat :=
  (3*a+2)*(6*atVariableBound n a q+6)

theorem atLeast_word_length_le {n a q : Nat} (v : Fin n) :
    (clauseFields (chain (SourceGenericPrefix.base n a q v.val)
      (SourceGenericPrefix.atLeastPayload (a := a) v))).length ≤
      atWordBound n a q := by
  let b := SourceGenericPrefix.base n a q v.val
  let M := atVariableBound n a q
  have hv := v.isLt
  have hvw : v.val*(SourceBooleanEncoding.width a q+1) +
      (SourceBooleanEncoding.width a q+1) ≤
      n*(SourceBooleanEncoding.width a q+1) := by
    have h := Nat.mul_le_mul_right (SourceBooleanEncoding.width a q+1)
      (show v.val+1 ≤ n by omega)
    rw [Nat.add_mul,Nat.one_mul] at h
    exact h
  have hbase : b + (SourceGenericPrefix.atLeastPayload (a := a) v).length
      < M := by
    rw [SourceGenericPrefix.atLeast_length]
    change n*a + v.val*(SourceBooleanEncoding.width a q+1) + a <
      n*a + n*(SourceBooleanEncoding.width a q + 1) + a + 1
    omega
  have hlit : ∀ l ∈ SourceGenericPrefix.atLeastPayload (a := a) v,
      l.variable < M := by
    intro l hl
    simp only [SourceGenericPrefix.atLeastPayload,List.mem_ofFn] at hl
    obtain ⟨s,rfl⟩ := hl
    have hb := (SourceBooleanEncoding.bitIndex v s).isLt
    change (SourceBooleanEncoding.bitIndex v s).val < M
    dsimp [M,atVariableBound]
    omega
  have hvalid := chain_valid b M
    (SourceGenericPrefix.atLeastPayload (a := a) v) hbase hlit
  have hlen := EncodedCNF.clauseFields_length_upper M _ hvalid
  have hcl : (chain b (SourceGenericPrefix.atLeastPayload (a := a) v)).length
      = 3*a+2 := SourceGenericPrefix.atLeast_chain_length (q := q) v
  rw [hcl] at hlen
  exact hlen

/-! ## One whole at-least vertex callback -/

noncomputable def atVertexEnvelope (n a q S O C : Nat) : Nat :=
  (2*atUnitCoefficient a q + a*atGateCoefficient a q) *
    (atSize n a q (S+atWordBound n a q) O (C+3*a+2))^4 + a + 3

theorem at_vertex_cost_le_poly {n a q : Nat} (v : Fin n)
    (saved output count : List Bool) :
    AtLeastClock.cost (a := a) (q := q) v saved output count ≤
      atVertexEnvelope n a q saved.length output.length count.length := by
  let w := SourceBooleanEncoding.width a q + 1
  let opening := UnitHandoff.nextSaved n a v.val w 0 false saved
  let middle := AtLeastCircuit.gateFold (q := q) v
    (List.ofFn (fun s : Fin a => s)) opening
  let S := saved.length + atWordBound n a q
  let O := output.length
  let C := count.length + 3*a + 2
  let Z := atSize n a q S O C
  let U := atUnitCoefficient a q
  let G := atGateCoefficient a q
  have hfinal := AtLeastSource.saved_eq_source (a := a) (q := q) v saved
  dsimp only at hfinal
  have hword := atLeast_word_length_le (a := a) (q := q) v
  have hmid_final : middle.length ≤ S := by
    have h1 : (UnitHandoff.nextSaved n a v.val w a true middle).length =
        (clauseFields (chain (SourceGenericPrefix.base n a q v.val)
          (SourceGenericPrefix.atLeastPayload (a := a) v))).length +
          saved.length := by
      change (UnitHandoff.nextSaved n a v.val (SourceBooleanEncoding.width a q + 1)
        a true (AtLeastCircuit.gateFold (q := q) v
          (List.ofFn (fun s : Fin a => s))
          (UnitHandoff.nextSaved n a v.val
            (SourceBooleanEncoding.width a q + 1) 0 false saved))).length = _
      rw [hfinal]
      simp only [List.length_append,List.length_reverse]
    have h2 : middle.length ≤
        (UnitHandoff.nextSaved n a v.val w a true middle).length := by
      simp only [UnitHandoff.nextSaved,List.length_append]
      omega
    dsimp only [S]
    omega
  have hmid : opening.length +
      ((List.ofFn (fun s : Fin a => s)).flatMap
        (AtLeastCircuit.gatePayload (q := q) v)).length = middle.length := by
    change _ = (AtLeastCircuit.gateFold (q := q) v
      (List.ofFn (fun s : Fin a => s)) opening).length
    rw [AtLeastSource.gateFold_eq_reverse]
    simp only [List.length_append,List.length_reverse]
    omega
  have hopen : saved.length ≤ opening.length := by
    simp only [opening,UnitHandoff.nextSaved,List.length_append]
    omega
  have hU0 := at_unit_cost_le_poly (a := a) (q := q) v 0 false saved output count
    S O C (Or.inl ⟨rfl,rfl⟩) (by dsimp only [S]; omega) le_rfl
    (by dsimp only [C]; omega)
  have hU1 := at_unit_cost_le_poly (a := a) (q := q) v a true middle output
    (List.replicate (3*a) true ++ (true :: count)) S O C
    (Or.inr ⟨rfl,rfl⟩) hmid_final le_rfl
    (by
      simp only [List.length_append,List.length_replicate,List.length_cons]
      dsimp only [C]
      omega)
  have hG : ∀ (s : Fin a) (saved' count' : List Bool),
      saved'.length ≤ S → count'.length ≤ C →
        AtLeastClock.gateCost (q := q) v s saved' output count' ≤ G*Z^4 :=
    fun s saved' count' hs hc =>
      at_gate_cost_le_poly (q := q) v s saved' output count' S O C
        hs le_rfl hc
  have hL := at_gateList_cost_le (q := q) v output S C (G*Z^4) hG
    (List.ofFn (fun s : Fin a => s)) opening (true :: count)
    (by omega)
    (by
      simp only [List.length_cons,List.length_ofFn]
      dsimp only [C]
      omega)
  simp only [List.length_ofFn] at hL
  have hU0' : UnitCycle.cost n a v.val (SourceBooleanEncoding.width a q + 1)
      0 false saved output count ≤ U*Z^4 := hU0
  have hU1' : UnitCycle.cost n a v.val (SourceBooleanEncoding.width a q + 1)
      a true middle output (List.replicate (3*a) true ++ (true :: count)) ≤
      U*Z^4 := hU1
  change UnitCycle.cost n a v.val (SourceBooleanEncoding.width a q + 1)
        0 false saved output count +
      (AtLeastClock.gateListCost (q := q) v
        (List.ofFn (fun s : Fin a => s)) opening output (true :: count) +
      UnitCycle.cost n a v.val (SourceBooleanEncoding.width a q + 1)
        a true middle output
        (List.replicate (3*a) true ++ (true :: count)) + 1) + 1 ≤
    (2*U + a*G)*Z^4 + a + 3
  have e1 : a*(G*Z^4+1) = a*G*Z^4 + a := by ring
  have e2 : (2*U + a*G)*Z^4 = 2*(U*Z^4) + a*G*Z^4 := by ring
  omega

#print axioms at_gate_pre_le_poly
#print axioms at_gate_cost_le_envelope
#print axioms at_gate_step_le
#print axioms at_unit_cost_le_poly
#print axioms at_gate_cost_le_poly
#print axioms at_gateList_cost_le
#print axioms atLeast_word_length_le
#print axioms at_vertex_cost_le_poly

end EthInapproximability.CurrentPaper.SourceGenericPrefixClock
