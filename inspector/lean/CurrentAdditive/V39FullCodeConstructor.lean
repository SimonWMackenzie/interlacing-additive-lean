import CurrentAdditive.V39CurrentCodeConstructorBounds
import CurrentAdditive.V39FullResourceBounds
import CurrentAdditive.V39FullCutoff

/-! Literal current public-schedule specialization of the actual constructor.
The accepted all-large source cutoff supplies every width and sample bound. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V39CurrentCodeConstructor

open V38Schedule V39PublicSchedule
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open V39DeadTaggedCompiler

def fullSampleCode (n L k : Nat) : Code :=
  deadSampleCode n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
    (fullW L) (fullQ L) k (sampleSide L k)

noncomputable def fullCompilerClock (n L k : Nat) : Nat :=
  V39DeadSampleJoin.clock n (seedWidth L) (fullS L) (fullQ₁ L) (fullQ₂ L)
    (fullW L) (fullQ L) k (sampleSide L k) (sampleSide L k)

def fullConstructorExponent : Nat :=
  26*(V39DeadCodeExponent.exponentConstant+18)+77

theorem full_clock_le_pow (n : Nat) (c : ℚ) (L edgeCount k : Nat) (δv ζ : ℚ)
    (hn : n ≤ 2^L) (htest : FullTests c L edgeCount δv ζ) :
    fullCompilerClock n L k ≤ 2^(fullConstructorExponent*(k+1)*L) := by
  have hL : 16 ≤ L := htest.2.2.1
  obtain ⟨hnE,hp,hq₁,hq₂,hs,hw,hQ⟩ := full_widths_le_pow n L hL hn
  have hm := full_sampleSide_le_pow c L edgeCount k δv ζ htest
  have hs3 : 3 ≤ fullS L := by have := fullS_ge_256 L; omega
  have hc := sampleClock_le_two_pow n (seedWidth L) (fullQ₁ L) (fullQ₂ L)
    (fullS L) (fullW L) (fullQ L) (fullWidthExponent L) (fullSampleExponent L k)
    k (sampleSide L k) hs3 hnE hp hq₁ hq₂ hs hw hQ hm
  apply hc.trans
  apply pow_le_pow_right₀ (by decide)
  unfold fullWidthExponent fullSampleExponent fullConstructorExponent
  have h10 : 16*L+10 ≤ 26*L := by omega
  have hmul := Nat.mul_le_mul_left
    ((V39DeadCodeExponent.exponentConstant+18)*(k+1)) h10
  have hunit : 1 ≤ (k+1)*L := by nlinarith
  nlinarith

theorem full_promised_clock (n Δ edgeCount k : Nat) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n)
    (hnm : n ≤ 2*edgeCount) (hdeg : 2*edgeCount ≤ Δ*n)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ ≤ n) :
    fullCompilerClock n (Nat.clog 2 n) k ≤
      2^(fullConstructorExponent*(k+1)*(Nat.clog 2 n)) := by
  exact full_clock_le_pow n (fullConstant γ Δ n edgeCount) (Nat.clog 2 n)
    edgeCount k (sourceDeltaV γ Δ n edgeCount) (sourceZeta γ)
    (Nat.le_pow_clog (by decide) n)
    (V39FullCutoff.fullPublicTests_all_large γ Δ n edgeCount hγ hΔ hn hnm hdeg hlarge)

theorem full_promised_construct (n Δ edgeCount k : Nat) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n)
    (hnm : n ≤ 2*edgeCount) (hdeg : 2*edgeCount ≤ Δ*n)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ ≤ n) :
    let L := Nat.clog 2 n
    ∃ t ≤ 2^(fullConstructorExponent*(k+1)*L),
      ((EthInapproximability.CurrentPaper.BitMachineEncoding.advance
        V39DeadSampleJoin.program)^[t])
        (⟨some start,control,V39DeadSampleJoin.initial n (seedWidth L) (fullS L)
          (fullQ₁ L) (fullQ₂ L) (fullW L) (fullQ L) k (sampleSide L k) (sampleSide L k)⟩ :
          Turing.TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none,control,finalBank n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
          (fullW L) (fullQ L) k (sampleSide L k)⟩ ∧
      finalBank n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
        (fullW L) (fullQ L) k (sampleSide L k) (Paper2.CodeGeneratorSampleTransfer.sample 10) =
        encodeCode (fullSampleCode n L k) := by
  let L := Nat.clog 2 n
  have hs : 3 ≤ fullS L := by have := fullS_ge_256 L; omega
  obtain ⟨t,ht,hr⟩ := physical_construct n (seedWidth L) (fullQ₁ L) (fullQ₂ L)
    (fullS L) (fullW L) (fullQ L) k (sampleSide L k) hs
  exact ⟨t,ht.trans (full_promised_clock n Δ edgeCount k γ hγ hΔ hn hnm hdeg hlarge),
    hr,final_output n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
      (fullW L) (fullQ L) k (sampleSide L k)⟩

#print axioms full_clock_le_pow
#print axioms full_promised_clock
#print axioms full_promised_construct

end CurrentAdditive.V39CurrentCodeConstructor
