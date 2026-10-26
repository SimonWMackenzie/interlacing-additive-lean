import CurrentAdditive.V39PhysicalSampleClock

/-! Public full-schedule invocation of the same physical sample program.
The source cutoff discharges its scalar schedule tests. There is no assumed
constructor run, successful random tape, alphabet cap, or sample-size cap. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V39PhysicalSample
noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open V38Schedule V39PublicSchedule V39FullSampleResources
open V39RecursiveGenerator V38OneStep

private instance seedWidthNeZero (L : ℕ) : NeZero (seedWidth L) :=
  ⟨ne_of_gt (full_positive_widths L).1⟩
private instance fullQ₁NeZero (L : ℕ) : NeZero (fullQ₁ L) :=
  ⟨ne_of_gt (full_positive_widths L).2.1⟩
private instance fullQ₂NeZero (L : ℕ) : NeZero (fullQ₂ L) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.1⟩
private instance fullSNeZero (L : ℕ) : NeZero (fullS L) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.2.1⟩
private instance fourFullSNeZero (L : ℕ) : NeZero (4 * fullS L) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.2.2.1⟩
private instance fullSMinusThreeNeZero (L : ℕ) : NeZero (fullS L - 3) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.1⟩
private instance fullWNeZero (L : ℕ) : NeZero (fullW L) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.2.1⟩
private instance fullQNeZero (L : ℕ) : NeZero (fullQ L) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.2.2⟩

def fullReservation (L k : ℕ) : ℕ := 2^fullDrawExponent L k
def fullPrecision (n L k : ℕ) : ℕ := publicBits (fullAlphabet n L) (fullReservation L k)

theorem full_draws_le (c : ℚ) (L edgeCount k : ℕ) (δv ζ : ℚ)
    (htest : FullTests c L edgeCount δv ζ) :
    sampleDrawBudget (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
      (fullW L) (fullQ L) k (sampleSide L k) ≤ fullReservation L k :=
  fullDrawCap_le c L edgeCount k δv ζ htest

theorem full_reserved_bits_le (n : ℕ) (c : ℚ) (L edgeCount k : ℕ) (δv ζ : ℚ)
    (hn : n ≤ 2^L) (htest : FullTests c L edgeCount δv ζ) :
    fullPrecision n L k * fullReservation L k ≤ 2^(240*((k+1)*L)) := by
  exact (randomBits_le_expSum (fullAlphabet n L) (fullReservation L k)
    (fullWidthExponent L) (fullDrawExponent L k)
    (fullAlphabet_le n L htest.2.2.1 hn) le_rfl).trans
    (Nat.pow_le_pow_right (by decide)
      (by simpa only [Nat.mul_assoc] using (budget_exponents_linear L k htest.2.2.1).2.2))

theorem full_physical_sample (n : ℕ) [NeZero n] (c : ℚ)
    (L edgeCount k : ℕ) (δv ζ : ℚ) (hn : n ≤ 2^L)
    (htest : FullTests c L edgeCount δv ζ)
    (bits : RoundedDraw.BitBlocks (fullPrecision n L k) (fullReservation L k))
    (suffix : List Bool) :
    ∃ t ≤ 2^(fullPhysicalExponent*((k+1)*L)),
      ((advance program)^[t])
        (⟨some start,control,initial n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
          (fullW L) (fullQ L) k (sampleSide L k)
          (RoundedCodeLoop.tapeWord (fullPrecision n L k) (fullReservation L k) bits ++ suffix)
          (fullPrecision n L k)⟩ : TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none,control,finalAtBudget n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
          (fullW L) (fullQ L) (by have h := fullS_ge_256 L; omega) rfl k (sampleSide L k)
          (fullReservation L k) (full_draws_le c L edgeCount k δv ζ htest) bits suffix⟩ := by
  obtain ⟨t,ht,hr⟩ := physical_sample_at_budget n (seedWidth L) (fullQ₁ L) (fullQ₂ L)
    (fullS L) (fullW L) (fullQ L) (by have h := fullS_ge_256 L; omega) rfl
    k (sampleSide L k) (fullReservation L k) (full_draws_le c L edgeCount k δv ζ htest)
    bits suffix
  exact ⟨t,ht.trans (full_physical_clock_le n c L edgeCount k δv ζ hn htest),hr⟩

theorem full_promised_physical_sample (n Δ edgeCount k : ℕ) [NeZero n] (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hnm : n ≤ 2*edgeCount) (hdeg : 2*edgeCount ≤ Δ*n)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ ≤ n)
    (bits : RoundedDraw.BitBlocks (fullPrecision n (Nat.clog 2 n) k)
      (fullReservation (Nat.clog 2 n) k)) (suffix : List Bool) :
    let L := Nat.clog 2 n
    let htest := V39FullCutoff.fullPublicTests_all_large γ Δ n edgeCount hγ hΔ
      (NeZero.pos n) hnm hdeg hlarge
    ∃ t ≤ 2^(fullPhysicalExponent*((k+1)*L)),
      ((advance program)^[t])
        (⟨some start,control,initial n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
          (fullW L) (fullQ L) k (sampleSide L k)
          (RoundedCodeLoop.tapeWord (fullPrecision n L k) (fullReservation L k) bits ++ suffix)
          (fullPrecision n L k)⟩ : TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none,control,finalAtBudget n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
          (fullW L) (fullQ L) (by have h := fullS_ge_256 L; omega) rfl k (sampleSide L k)
          (fullReservation L k)
          (full_draws_le (fullConstant γ Δ n edgeCount) L edgeCount k
            (sourceDeltaV γ Δ n edgeCount) (sourceZeta γ) htest) bits suffix⟩ := by
  intro L htest
  exact full_physical_sample n (fullConstant γ Δ n edgeCount) L edgeCount k
    (sourceDeltaV γ Δ n edgeCount) (sourceZeta γ) (Nat.le_pow_clog (by decide) n) htest bits suffix

#print axioms full_reserved_bits_le
#print axioms full_physical_sample
#print axioms full_promised_physical_sample

end
end CurrentAdditive.V39PhysicalSample
