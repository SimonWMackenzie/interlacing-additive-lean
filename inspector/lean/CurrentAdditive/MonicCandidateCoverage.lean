import CurrentAdditive.CandidateCoverage

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial

abbrev MonicDegree (e : ℕ) :=
  {p : Polynomial (ZMod 2) // p.Monic ∧ p.natDegree = e}

noncomputable def monicEncoding (e : ℕ) (tail : Fin (2 ^ e)) : MonicDegree e :=
  ⟨polynomial (e + 1) (TrialSearch.monicBits e tail),
    monicBits_monic e tail tail.isLt, monicBits_degree e tail tail.isLt⟩

theorem monicEncoding_injective (e : ℕ) : Function.Injective (monicEncoding e) := by
  intro a b hab
  have hpoly : polynomial (e + 1) (TrialSearch.monicBits e a) =
      polynomial (e + 1) (TrialSearch.monicBits e b) := congrArg Subtype.val hab
  let aCode : Fin (2 ^ (e + 1)) :=
    ⟨TrialSearch.monicBits e a, monicBits_lt e a a.isLt⟩
  let bCode : Fin (2 ^ (e + 1)) :=
    ⟨TrialSearch.monicBits e b, monicBits_lt e b b.isLt⟩
  have hlow : lowEncoding (e + 1) aCode = lowEncoding (e + 1) bCode :=
    Subtype.ext hpoly
  have hcodes := congrArg Fin.val (lowEncoding_injective (e + 1) hlow)
  change TrialSearch.monicBits e a = TrialSearch.monicBits e b at hcodes
  apply Fin.ext
  change 2 ^ e + a.val = 2 ^ e + b.val at hcodes
  omega

theorem monicEncoding_surjective (e : ℕ) : Function.Surjective (monicEncoding e) := by
  letI : Fintype (Polynomial.degreeLT (ZMod 2) e) :=
    Fintype.ofEquiv (Fin e → ZMod 2) (Polynomial.degreeLTEquiv (ZMod 2) e).toEquiv.symm
  letI : Fintype (MonicDegree e) :=
    Fintype.ofEquiv (Polynomial.degreeLT (ZMod 2) e)
      (Polynomial.monicEquivDegreeLT e).symm
  have hcard : Fintype.card (Fin (2 ^ e)) = Fintype.card (MonicDegree e) := by
    rw [Fintype.card_fin, Fintype.card_congr (Polynomial.monicEquivDegreeLT e),
      Fintype.card_congr (Polynomial.degreeLTEquiv (ZMod 2) e).toEquiv]
    simp [ZMod.card]
  let equiv : Fin (2 ^ e) ≃ MonicDegree e := Fintype.equivOfCardEq hcard
  exact (Finite.injective_iff_surjective_of_equiv equiv).mp (monicEncoding_injective e)

theorem exists_monicBits (e : ℕ) (p : Polynomial (ZMod 2))
    (hp : p.Monic) (hdeg : p.natDegree = e) :
    ∃ tail < 2 ^ e, polynomial (e + 1) (TrialSearch.monicBits e tail) = p := by
  obtain ⟨tail, htail⟩ := monicEncoding_surjective e ⟨p, hp, hdeg⟩
  exact ⟨tail.val, tail.isLt, congrArg Subtype.val htail⟩

#print axioms monicEncoding_surjective
#print axioms exists_monicBits

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
