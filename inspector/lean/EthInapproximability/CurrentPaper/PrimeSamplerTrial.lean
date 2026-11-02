import EthInapproximability.CurrentPaper.PrimeSampler

/-!
# Finite trial-division search for the prime-polynomial sampler

Source: frozen v8 `B-effectivity-details.tex`,
`lem:paper-explicit-balanced-family`. This executable finite search tests
each candidate against divisors `2,...,n-1`, then scans candidates in
increasing order in `[X,2X)`. The result is exactly the existing sampler's
least prime. This module proves pure algorithmic correctness only; actual
Boolean-stack runtime is a separate obligation.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerTrial

def trialPrime (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range (n - 2)).all (fun i => decide (n % (i + 2) ≠ 0))

theorem trialPrime_eq_true (n : Nat) : trialPrime n = true ↔ Nat.Prime n := by
  simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  rw [Nat.prime_def_lt']
  constructor
  · rintro ⟨hn, hdiv⟩
    refine ⟨hn, ?_⟩
    intro d hd hdlt hdn
    have ht := hdiv (d - 2) (by omega)
    have he : d - 2 + 2 = d := by omega
    rw [he] at ht
    exact ht (Nat.mod_eq_zero_of_dvd hdn)
  · rintro ⟨hn, hdiv⟩
    refine ⟨hn, ?_⟩
    intro i hi
    exact fun h => hdiv (i + 2) (by omega) (by omega) (Nat.dvd_of_mod_eq_zero h)

theorem trialPrime_eq (n : Nat) : trialPrime n = decide (Nat.Prime n) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using trialPrime_eq_true n

/-- `fuel` is a literal candidate count. No unbounded least-number search is
used by this executable function. -/
def scan : Nat → Nat → Option Nat
  | _, 0 => none
  | start, fuel + 1 => if trialPrime start then some start else scan (start + 1) fuel

theorem scan_eq_some_iff (start fuel p : Nat) :
    scan start fuel = some p ↔
      Nat.Prime p ∧ start ≤ p ∧ p < start + fuel ∧
        ∀ r, start ≤ r → r < p → ¬Nat.Prime r := by
  induction fuel generalizing start with
  | zero =>
      simp only [scan, reduceCtorEq, false_iff]
      intro h
      omega
  | succ fuel ih =>
      by_cases hs : trialPrime start = true
      · have hpstart := (trialPrime_eq_true start).mp hs
        simp only [scan, hs, ↓reduceIte, Option.some.injEq]
        constructor
        · intro hp
          subst p
          refine ⟨hpstart, le_rfl, by omega, ?_⟩
          intro r hr hlt
          omega
        · rintro ⟨hp, hlo, hhi, hleast⟩
          by_contra hne
          exact hleast start le_rfl (by omega) hpstart
      · have hnot : ¬Nat.Prime start := (trialPrime_eq_true start).not.mp hs
        rw [scan, if_neg hs, ih]
        constructor
        · rintro ⟨hp, hlo, hhi, hleast⟩
          refine ⟨hp, by omega, by omega, ?_⟩
          intro r hr hlt
          by_cases he : r = start
          · simpa only [he] using hnot
          · exact hleast r (by omega) hlt
        · rintro ⟨hp, hlo, hhi, hleast⟩
          have hne : p ≠ start := fun h => hnot (h ▸ hp)
          exact ⟨hp, by omega, by omega, fun r hr hlt => hleast r (by omega) hlt⟩

theorem scan_success (start fuel p : Nat) (hp : Nat.Prime p)
    (hlo : start ≤ p) (hhi : p < start + fuel)
    (hleast : ∀ r, start ≤ r → r < p → ¬Nat.Prime r) :
    scan start fuel = some p :=
  (scan_eq_some_iff start fuel p).mpr ⟨hp, hlo, hhi, hleast⟩

theorem scan_primeSampler (q t m : Nat) :
    scan (PrimeSampler.threshold q t m) (PrimeSampler.threshold q t m) =
      some (PrimeSampler.prime q t m) := by
  obtain ⟨hlo, hhi⟩ := PrimeSampler.prime_window q t m
  apply scan_success _ _ _ (PrimeSampler.prime_isPrime q t m) hlo
  · omega
  · intro r hr hlt hp
    have hleast := PrimeSampler.prime_least q t m r hp hr
    omega

/-- The fallback is observable only for arbitrary thresholds below two;
the sampler's threshold always gives a successful scan. -/
def firstPrime (X : Nat) : Nat := (scan X X).getD 0

theorem firstPrime_eq_sampler (q t m : Nat) :
    firstPrime (PrimeSampler.threshold q t m) = PrimeSampler.prime q t m := by
  simp [firstPrime, scan_primeSampler]

theorem firstPrime_sampler_window (q t m : Nat) :
    let X := PrimeSampler.threshold q t m
    X ≤ firstPrime X ∧ firstPrime X < 2 * X := by
  simpa only [firstPrime_eq_sampler] using PrimeSampler.prime_window q t m

theorem firstPrime_sampler_prime (q t m : Nat) :
    Nat.Prime (firstPrime (PrimeSampler.threshold q t m)) := by
  rw [firstPrime_eq_sampler]
  exact PrimeSampler.prime_isPrime q t m

theorem threshold_of_two_le (X : Nat) (hX : 2 ≤ X) :
    PrimeSampler.threshold X 0 0 = X := by
  simp [PrimeSampler.threshold, max_eq_left hX]

theorem firstPrime_prime (X : Nat) (hX : 2 ≤ X) : Nat.Prime (firstPrime X) := by
  simpa only [threshold_of_two_le X hX] using firstPrime_sampler_prime X 0 0

theorem firstPrime_window (X : Nat) (hX : 2 ≤ X) :
    X ≤ firstPrime X ∧ firstPrime X < 2 * X := by
  simpa only [threshold_of_two_le X hX] using firstPrime_sampler_window X 0 0

theorem scan_firstPrime (X : Nat) (hX : 2 ≤ X) : scan X X = some (firstPrime X) := by
  have he := scan_primeSampler X 0 0
  have hp := firstPrime_eq_sampler X 0 0
  rw [threshold_of_two_le X hX] at he hp
  rw [he, hp]

theorem firstPrime_least (X p : Nat) (hX : 2 ≤ X) (hp : Nat.Prime p)
    (hlo : X ≤ p) : firstPrime X ≤ p := by
  have he := firstPrime_eq_sampler X 0 0
  rw [threshold_of_two_le X hX] at he
  rw [he]
  exact PrimeSampler.prime_least X 0 0 p hp (by simpa [threshold_of_two_le X hX] using hlo)

theorem trial_regressions :
    trialPrime 0 = false ∧ trialPrime 1 = false ∧ trialPrime 2 = true ∧
      trialPrime 3 = true ∧ trialPrime 4 = false ∧ trialPrime 9 = false ∧
      scan 2 2 = some 2 ∧ scan 8 8 = some 11 ∧ firstPrime 2 = 2 := by decide

end EthInapproximability.CurrentPaper.PrimeSamplerTrial
