import EthInapproximability.CurrentPaper.Construction
import EthInapproximability.ParameterizedNP.BalancedFamilyBuilder

/-!
# The current paper's explicit prime-polynomial column family

Source: v8 `B-effectivity-details.tex`, `lem:paper-explicit-balanced-family`
and `eq:paper-balanced-family-size`; `02-foundations.tex`,
`def:paper-relaxed-interlace`; `03-parameterized-construction.tex`,
`eq:paper-M2-M3-definition`.

The independent prime search, base-p digit bijection, Vandermonde counting,
and residue estimates are reused from `ParameterizedNP.BalancedFamilyBuilder`.
Their actual definitions and proofs were checked against these source anchors;
their theorem closures use only `propext`, `Classical.choice`, `Quot.sound`.
In particular, the AGHP balanced-family existence axiom is not consumed.

All indices and alphabet values here are zero-based. Thus adding one to an
entry, coordinate, and label gives precisely the paper's displayed accessor.
Labels remain `Fin (p^t)`, even when two polynomial indices give equal tuples.
The explicit alphabet equivalence below connects this family to the actual
current matrix constructor, not to an older Stage-4 matrix.

This module proves finite construction correctness, not a bit-model runtime
bound or the legality of a particular parameter schedule. The same family is
available at both row-restriction depths; obtaining either communication
lower bound is a separate obligation and is not an input to this construction.
-/

namespace EthInapproximability.CurrentPaper.PrimeSampler

open scoped BigOperators
open EthInapproximability.ParameterizedNP.BalancedFamilyBuilder

/-- The search threshold appearing literally in the current paper. -/
def threshold (q t m : ℕ) : ℕ := max (max q (1000 * m * t ^ 2)) 2

/-- The least prime at least `threshold`, computed by the audited search. -/
abbrev prime (q t m : ℕ) : ℕ := balPrime q t m

/-- Labels are coefficient vectors in their base-p enumeration, with repeats
of represented tuples kept as distinct labels. -/
abbrev size (q t m : ℕ) : ℕ := balN q t m

abbrev digit (p l r : ℕ) : ℕ := balDigit p l r

abbrev entry (p t m l j : ℕ) : ℕ := balEntryVal p t m l j

abbrev family (q t m : ℕ) (hm : 0 < m) : Fin (size q t m) → Fin q → Fin m :=
  balFamily q t m hm

theorem prime_isPrime (q t m : ℕ) : Nat.Prime (prime q t m) :=
  balPrime_prime q t m

theorem prime_window (q t m : ℕ) :
    threshold q t m ≤ prime q t m ∧ prime q t m < 2 * threshold q t m :=
  ⟨xBal_le_balPrime q t m, balPrime_lt_two_mul_xBal q t m⟩

theorem prime_least (q t m p : ℕ) (hp : Nat.Prime p)
    (hlo : threshold q t m ≤ p) : prime q t m ≤ p :=
  balPrime_least hlo hp

theorem size_exact (q t m : ℕ) : size q t m = prime q t m ^ t := rfl

theorem size_pos (q t m : ℕ) : 0 < size q t m := balN_pos q t m

theorem size_lt (q t m : ℕ) (ht : 1 ≤ t) :
    size q t m < (2 * threshold q t m) ^ t :=
  balN_lt_bBal q t m ht

theorem digit_eq (p l r : ℕ) : digit p l r = l / p ^ r % p := rfl

theorem entry_eq (p t m l j : ℕ) :
    entry p t m l j = (∑ r ∈ Finset.range t, (l / p ^ r % p) * j ^ r) % p % m := rfl

theorem family_entry (q t m : ℕ) (hm : 0 < m)
    (l : Fin (size q t m)) (j : Fin q) :
    (family q t m hm l j).val =
      (∑ r ∈ Finset.range t, (l.val / prime q t m ^ r % prime q t m) * j.val ^ r)
        % prime q t m % m := rfl

/-- The digit map is a bijection onto all degree-less-than-t coefficient
vectors, not a selected set or a presumed source of independence. -/
abbrev coefficientsEquiv (q t m : ℕ) :
    Fin (size q t m) ≃ (Fin t → ZMod (prime q t m)) := balCoeffEquiv q t m

theorem coefficientsEquiv_apply (q t m : ℕ)
    (l : Fin (size q t m)) (r : Fin t) :
    coefficientsEquiv q t m l r =
      (digit (prime q t m) l.val r.val : ZMod (prime q t m)) := rfl

/-- Exact finite-field fibre count, including zero selected coordinates.
This derives the explicit power from the audited uniform-count identity. -/
theorem polynomial_fibre_card {p t r : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    (ht : 1 ≤ t) (hrt : r ≤ t) (x : Fin r → ZMod p)
    (hx : Function.Injective x) (y : Fin r → ZMod p) :
    (Finset.univ.filter (fun a : Fin t → ZMod p => vandEval x a = y)).card =
      p ^ (t - r) := by
  classical
  have h := card_vandEval_preimage_mul (p := p) ht hrt x hx (fun j => {y j})
  have hcount :
      (Finset.univ.filter (fun a : Fin t → ZMod p => vandEval x a = y)).card * p ^ r
        = p ^ t := by
    simpa only [Finset.mem_singleton, ← funext_iff, Finset.card_singleton,
      Finset.prod_const_one, one_mul] using h
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (NeZero.pos p) r)
  rw [hcount, ← pow_add, Nat.sub_add_cancel hrt]

/-- The same exact fibre count over the actual indexed polynomial labels. -/
theorem indexed_polynomial_fibre_card (q t m r : ℕ) (ht : 1 ≤ t) (hrt : r ≤ t)
    (x : Fin r → ZMod (prime q t m)) (hx : Function.Injective x)
    (y : Fin r → ZMod (prime q t m)) :
    (Finset.univ.filter (fun l : Fin (size q t m) =>
      vandEval x (coefficientsEquiv q t m l) = y)).card = prime q t m ^ (t - r) := by
  classical
  rw [← polynomial_fibre_card ht hrt x hx y]
  apply Finset.card_equiv (coefficientsEquiv q t m)
  intro l
  simp

/-- The actual deterministic family satisfies the two-sided indexed balance
condition of the current paper. No balancedness premise is assumed. -/
theorem family_balanced (q t m : ℕ) (hm : 0 < m) (ht : 1 ≤ t) (htq : t ≤ q) :
    NPCC.IsBalancedFamily t (family q t m hm) (1 / (100 * (t : ℝ))) :=
  balFamily_isBalanced q t m hm ht htq

/-- The paper's interval statement, rather than its equivalent absolute-value
encoding. Probability is over labels, so multiplicity is retained. -/
theorem pattern_frequency_bounds (q t m : ℕ) (hm : 0 < m) (ht : 1 ≤ t)
    (htq : t ≤ q) (J : Finset (Fin q)) (hJ : J.card ≤ t) (a : Fin q → Fin m) :
    let probability := ((Finset.univ.filter (fun l : Fin (size q t m) =>
      ∀ j ∈ J, family q t m hm l j = a j)).card : ℝ) / size q t m
    (1 - 1 / (100 * (t : ℝ))) / (m : ℝ) ^ J.card ≤ probability ∧
      probability ≤ (1 + 1 / (100 * (t : ℝ))) / (m : ℝ) ^ J.card := by
  dsimp only
  have h := (family_balanced q t m hm ht htq).2 J hJ a
  simp only [Fintype.card_fin, abs_le] at h
  constructor <;> (simp only [sub_div, add_div]; linarith [h.1, h.2])

theorem size_lower (q t m : ℕ) (hm : 0 < m) (ht : 1 ≤ t) (htq : t ≤ q) :
    m ^ t ≤ size q t m := balN_pow_le q t m hm ht htq

/-- A successful explicit descriptor and its random-access semantics. This is
algorithmic correctness only; no running-time assertion is packaged here. -/
theorem descriptor_correct (q t m : ℕ) (hm : 0 < m) (ht : 1 ≤ t) (htq : t ≤ q) :
    balBuild q t m = some (size q t m, balDescriptor q t m) ∧
    ∀ (l : Fin (size q t m)) (j : Fin q),
      balEntry q t m (size q t m) (balDescriptor q t m) l.val j.val =
        some (family q t m hm l j).val := by
  refine ⟨balBuild_eq_some hm ht htq, ?_⟩
  intro l j
  exact balEntry_at_builder_output hm l.isLt j.isLt

section ActualSecondMatrix

universe u
variable {X Y : Type u} [Fintype X] [DecidableEq X]

/-- The finite public enumeration is supplied explicitly, so the constructor
does not silently change the order of the row alphabet. -/
def secondFamily (a q t m : ℕ) (hm : 0 < m)
    (e : Fin m ≃ Construction.FirstRows a X) :
    Construction.SecondFamily a q (size q t m) X :=
  fun l j => e (family q t m hm l j)

theorem secondFamily_balanced (a q t m : ℕ) (hm : 0 < m) (ht : 1 ≤ t)
    (htq : t ≤ q) (e : Fin m ≃ Construction.FirstRows a X) :
    NPCC.IsBalancedFamily t (secondFamily a q t m hm e) (1 / (100 * (t : ℝ))) :=
  isBalancedFamily_congr_equiv e (family_balanced q t m hm ht htq)

/-- No resampling is needed when a later argument uses fewer coordinates. -/
theorem secondFamily_balanced_lower_order (a q t m r : ℕ) (hm : 0 < m)
    (ht : 1 ≤ t) (htq : t ≤ q) (hrt : r ≤ t)
    (e : Fin m ≃ Construction.FirstRows a X) :
    NPCC.IsBalancedFamily r (secondFamily a q t m hm e) (1 / (100 * (t : ℝ))) := by
  have h := secondFamily_balanced a q t m hm ht htq e
  exact ⟨h.1, fun J hJ pattern => h.2 J (hJ.trans hrt) pattern⟩

omit [Fintype X] [DecidableEq X] in
/-- The balanced accessor is connected to the actual current-paper matrix,
with the transpose in its correct position and the original family labels. -/
theorem secondMatrix_eq_relaxedInterlace (R : X → Y → Bool) (a s q t m : ℕ)
    (hm : 0 < m) (e : Fin m ≃ Construction.FirstRows a X) :
    Construction.secondMatrix R a s q (size q t m) (secondFamily a q t m hm e) =
      NPCC.relaxedInterlace (fun γ r => Construction.firstMatrix R a s r γ)
        (secondFamily a q t m hm e) := rfl

end ActualSecondMatrix

/-- For numeric row labels the alphabet relabelling is the standard
lexicographic product enumeration, without a choice of ordering. -/
def canonicalFirstRowsEquiv (a n : ℕ) :
    Fin (Construction.qOne a * n) ≃ Construction.FirstRows a (Fin n) :=
  finProdFinEquiv.symm

theorem canonicalFirstRowsEquiv_symm_val (a n : ℕ)
    (r : Construction.FirstRows a (Fin n)) :
    ((canonicalFirstRowsEquiv a n).symm r).val = r.1.val * n + r.2.val := by
  simp [canonicalFirstRowsEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

theorem canonicalSecondFamily_balanced (a q t n : ℕ)
    (hm : 0 < Construction.qOne a * n) (ht : 1 ≤ t) (htq : t ≤ q) :
    NPCC.IsBalancedFamily t
      (secondFamily a q t (Construction.qOne a * n) hm (canonicalFirstRowsEquiv a n))
      (1 / (100 * (t : ℝ))) :=
  secondFamily_balanced a q t (Construction.qOne a * n) hm ht htq
    (canonicalFirstRowsEquiv a n)

end EthInapproximability.CurrentPaper.PrimeSampler
