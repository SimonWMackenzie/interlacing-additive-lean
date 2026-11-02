import CurrentAdditive.GaussGridPreparedInput
import CurrentAdditive.GaussConcreteGridInputBytes

namespace CurrentAdditive.GaussGridInputPolynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussGridPreparedInput GaussCellPolynomialClock
open GaussConcreteGridPolynomial (invocation)
open CurrentAdditive.MinimumRatioContext

attribute [local irreducible] GaussInputDimensions.R GaussInputDimensions.C
  GaussRowCount.oneMachine GaussFetchedArithmetic.M PolynomialBound

theorem row_clock_polynomial : PolynomialBound (fun _ n => GaussRowCount.polynomialClock n) := by
  have hn:=second
  have hn1:=add hn (constant 1)
  have hitem:=add (add (add (add (add
    (mul (mul (constant 20) hn1) hn1) (constant 1))
    (mul (constant 4) hn)) (constant 1))
    (mul (constant GaussRowCount.oneMachine.stackCount)
      (add (add hn (constant GaussRowCount.oneMachine.pushBound)) (constant 1)))) (constant 9)
  have hsmall:=add (mul (constant 3) hn) (constant 1)
  have hmain:=add (add (mul hn (add (add hitem (mul (constant 4) hn)) (constant 8)))
    (mul (constant 11) hn)) (constant 17)
  simpa only [GaussRowCount.polynomialClock,GaussRowCount.itemEnvelope] using
    add (add (add hmain (mul (constant 2) hsmall)) (constant 2))
      (add (mul (constant 2) hsmall) (constant 3))

theorem column_clock_polynomial : PolynomialBound (fun _ n => GaussMatrixDimensions64.columnsClock n) := by
  simpa only [GaussMatrixDimensions64.columnsClock] using
    add (add (add (mul (constant 50) (power (add second (constant 1)) 3))
      (mul (constant 2) second)) (constant 2)) row_clock_polynomial

def dimensions (n : Nat) : Nat :=
  invocation GaussInputDimensions.R n (GaussRowCount.polynomialClock n)+
  invocation GaussInputDimensions.C n (GaussMatrixDimensions64.columnsClock n)+1

theorem dimensions_polynomial : PolynomialBound (fun _ n => dimensions n) := by
  exact add (add
    (GaussConcreteGridPolynomialBound.invocation_polynomial GaussInputDimensions.R second row_clock_polynomial)
    (GaussConcreteGridPolynomialBound.invocation_polynomial GaussInputDimensions.C second column_clock_polynomial))
    (constant 1)

theorem dimensionClock_le (matrix : List Bool) {n : Nat} (h : matrix.length≤n) :
    GaussInputDimensions.dimensionClock matrix≤dimensions n := by
  have hr:=GaussRowCount.polynomialClock_mono h
  have hc : GaussMatrixDimensions64.columnsClock matrix.length≤
      GaussMatrixDimensions64.columnsClock n := by
    unfold GaussMatrixDimensions64.columnsClock
    gcongr
  unfold GaussInputDimensions.dimensionClock dimensions MachineInvokeFull.uniformBound invocation
  gcongr

theorem extended_length {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) :
    (BitMachineBankCodec.encode (words B r pivot c)).length=
      (BitMachineBankCodec.encode (rawWords B r pivot c)).length+2*m+2*k+2 := by
  rw [BitMachineBankCodec.encode_length,BitMachineBankCodec.encode_length]
  simp [words,GaussInputDimensions.extended,rawWords,Fin.sum_univ_succ] <;> omega

theorem public_size_bounds {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) :
    let n := (BitMachineBankCodec.encode (rawWords B r pivot c)).length
    (GaussPhysical.encodeTypedMatrix B).length≤n ∧ m≤n ∧ k≤n ∧
      (BitMachineBankCodec.encode (words B r pivot c)).length≤5*(n+1) := by
  let n := (BitMachineBankCodec.encode (rawWords B r pivot c)).length
  have hmatrix : (GaussPhysical.encodeTypedMatrix B).length≤n :=
    BitMachineBankCodec.word_length_le_encode (rawWords B r pivot c) 0
  have hm:=GaussInitialByteDimensions.rows_le_initial_bytes B
  have hk:=GaussInitialByteDimensions.columns_le_initial_bytes B (by have h:=r.isLt; omega)
  have hlen:=extended_length B r pivot c
  exact ⟨hmatrix,hm.trans hmatrix,hk.trans hmatrix,by omega⟩

def totalBound (C e n : Nat) : Nat := dimensions n+150*(n+1)+C*(n+1)^e

theorem totalBound_polynomial (C e : Nat) : PolynomialBound (fun _ n => totalBound C e n) :=
  add (add dimensions_polynomial (mul (constant 150) (add second (constant 1))))
    (mul (constant C) (power (add second (constant 1)) e))

/-- A single coefficient and exponent precede all matrices, dimensions and
addresses. The input contains the matrix and three cursors, but no dimensions
or assumed prepared bank. Every invocation and transfer is charged. -/
theorem uniform_outputs : ∃ C e : Nat,
    ∀ {m k : Nat} (B : Fin m → Fin k → ℚ) (r pivot : Fin m) (c : Fin k),
      B pivot c≠0 → finiteBitMachine.OutputsWithin
        (BitMachineBankCodec.encode (rawWords B r pivot c)) (answer B r pivot c)
        (C*((BitMachineBankCodec.encode (rawWords B r pivot c)).length+1)^e) := by
  obtain ⟨C,e,hgrid⟩:=GaussConcreteGridInputBytes.uniform_grid_original_bytes
  have hpoly:=totalBound_polynomial C e
  unfold PolynomialBound at hpoly
  obtain ⟨D,f,hD⟩:=hpoly
  refine ⟨D,f,?_⟩
  intro m k B r pivot c hn
  let raw:=rawWords B r pivot c
  let w:=words B r pivot c
  let n:=(BitMachineBankCodec.encode raw).length
  obtain ⟨hmat,hm,hk,hlen⟩:=public_size_bounds B r pivot c
  have hprep : preparationClock w≤100*(n+1) := by
    have hw4 : (w 4).length=m := by simp [w,words,GaussInputDimensions.extended]
    unfold preparationClock
    rw [hw4]
    dsimp only [n,raw,w] at *
    omega
  have hdim : GaussInputDimensions.clock raw m k≤dimensions n+23*(n+1) := by
    have hd:=dimensionClock_le (GaussPhysical.encodeTypedMatrix B) hmat
    change 9*(n+1)+GaussInputDimensions.dimensionClock (raw 0)+
      2*(GaussInputDimensions.outputPacket raw m k).length+4≤dimensions n+23*(n+1)
    change 9*(n+1)+GaussInputDimensions.dimensionClock (GaussPhysical.encodeTypedMatrix B)+
      2*(BitMachineBankCodec.encode w).length+4≤dimensions n+23*(n+1)
    dsimp only [n,raw,w] at *
    omega
  obtain ⟨a,ha,hprepare⟩:=physical_prepare w
  have hprepare': ((advance program)^[a])
      (rawInit inputCell start GaussGridPreparedInput.control (BitMachineBankCodec.encode w))=
      ⟨none,GaussGridPreparedInput.control,(GaussConcreteGrid.initialData B r pivot c).contents⟩ := by
    simpa only [w,prepared_exact] using hprepare
  obtain ⟨b,hb,v,hgrun⟩:=hgrid B r pivot c hn
  have hb' : b≤C*(n+1)^e :=
    hb.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right hmat 1) e))
  obtain ⟨t,ht,he⟩:=BitMachineRawSequence.runs program GaussConcreteGrid.program
    start GaussConcreteGrid.start GaussGridPreparedInput.control GaussGridPreparedInput.control GaussConcreteGrid.control v
    (rawInit inputCell start GaussGridPreparedInput.control (BitMachineBankCodec.encode w)).stk
    (GaussConcreteGrid.initialData B r pivot c).contents
    (Function.update (GaussConcreteGrid.initialData B r pivot c).contents outputCell
      (answer B r pivot c)) a b hprepare' hgrun
  have hfull : ((advance fullProgram)^[t])
      (rawInit inputCell fullStart fullControl (BitMachineBankCodec.encode w))=
      ⟨none,(GaussGridPreparedInput.control,v),
        Function.update (GaussConcreteGrid.initialData B r pivot c).contents outputCell
          (answer B r pivot c)⟩ := he
  have hsix : sixFieldMachine.OutputsWithin (BitMachineBankCodec.encode w)
      (answer B r pivot c) (100*(n+1)+C*(n+1)^e+1) := by
    apply outputsWithin_of_raw_run inputCell outputCell fullStart fullControl fullProgram
      (BitMachineBankCodec.encode w) (answer B r pivot c) t _ (by omega)
    · rw [hfull]
    · rw [hfull]; simp
  have hdimensions:=GaussInputDimensions.outputs B (by have h:=r.isLt; omega) raw rfl
  have hout:=BitMachineComposition.composition_outputsWithin
    GaussInputDimensions.machine sixFieldMachine hdimensions hsix
  apply BitMachine.outputsWithin_mono finiteBitMachine hout
  have hbound:=hD 0 n
  simp only [Nat.zero_add] at hbound
  apply (show GaussInputDimensions.clock raw m k+
      2*(BitMachineBankCodec.encode w).length+2+
      (100*(n+1)+C*(n+1)^e+1)≤totalBound C e n from by
    unfold totalBound
    dsimp only [n,raw,w] at *
    omega).trans hbound

def coefficient : Nat := Classical.choose uniform_outputs
def exponent : Nat := Classical.choose (Classical.choose_spec uniform_outputs)
def gridPolynomialClock (n : Nat) : Nat := coefficient*(n+1)^exponent

theorem outputs_polynomial {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    finiteBitMachine.OutputsWithin (BitMachineBankCodec.encode (rawWords B r pivot c))
      (answer B r pivot c)
      (gridPolynomialClock (BitMachineBankCodec.encode (rawWords B r pivot c)).length) :=
  Classical.choose_spec (Classical.choose_spec uniform_outputs) B r pivot c hn

#print axioms uniform_outputs
#print axioms outputs_polynomial
end
end CurrentAdditive.GaussGridInputPolynomial
