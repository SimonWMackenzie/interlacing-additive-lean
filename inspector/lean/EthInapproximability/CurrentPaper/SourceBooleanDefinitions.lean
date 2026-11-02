import EthInapproximability.CurrentPaper.EncodedCNF

/-!
# Finite-alphabet constraints and their exact-one Boolean clauses

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`, the
exact-one Boolean encoding between the cited PCP and colouring reductions.
Every constraint, including repeated constraints, has a separate index.
The enumeration uses explicit arithmetic equivalences of finite types.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanEncoding

open EncodedCNF

structure CSP (n m a q : ℕ) where
  query : Fin m → Fin q → Fin n
  accept : Fin m → (Fin q → Fin a) → Bool

def evalConstraint {n m a q : ℕ} (P : CSP n m a q)
    (σ : Fin n → Fin a) (j : Fin m) : Bool :=
  P.accept j (fun t => σ (P.query j t))

def Satisfiable {n m a q : ℕ} (P : CSP n m a q) : Prop :=
  ∃ σ : Fin n → Fin a, ∀ j, evalConstraint P σ j = true

def falseConstraints {n m a q : ℕ} (P : CSP n m a q)
    (σ : Fin n → Fin a) : Finset (Fin m) :=
  Finset.univ.filter fun j => evalConstraint P σ j = false

def Gap {n m a q : ℕ} (P : CSP n m a q) (ε : ℚ) : Prop :=
  ∀ σ : Fin n → Fin a, ε * m ≤ ((falseConstraints P σ).card : ℚ)

def incident {n m a q : ℕ} (P : CSP n m a q) (v : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun j => ∃ t, P.query j t = v

/-- A repeated query in one constraint counts once for this degree bound.
The literal-occurrence estimate below separately pays the query width. -/
def BoundedOccurrence {n m a q : ℕ} (P : CSP n m a q) (D : ℕ) : Prop :=
  ∀ v, (incident P v).card ≤ D

def bitIndex {n a : ℕ} (v : Fin n) (s : Fin a) : Fin (n * a) :=
  finProdFinEquiv (v, s)

abbrev ClauseLabel (n m a q : ℕ) :=
  Fin n ⊕ ((Fin n × (Fin a × Fin a)) ⊕ (Fin m × (Fin q → Fin a)))

def clauseCount (n m a q : ℕ) : ℕ := n + (n * (a * a) + m * a ^ q)

def labelEquiv (n m a q : ℕ) : ClauseLabel n m a q ≃ Fin (clauseCount n m a q) :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr
    ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv)
    ((Equiv.prodCongr (Equiv.refl _) finFunctionFinEquiv).trans finProdFinEquiv)).trans
      finSumFinEquiv)).trans finSumFinEquiv

def positive (v : ℕ) : Literal := ⟨v, true⟩
def negative (v : ℕ) : Literal := ⟨v, false⟩

/-- The diagonal pair clauses and accepted-pattern clauses are tautologies.
Keeping their labelled slots makes the enumeration and size completely fixed;
it changes only the constant in the resulting gap. -/
def clause {n m a q : ℕ} (P : CSP n m a q) (hq : 0 < q) :
    ClauseLabel n m a q → List Literal
  | .inl v => List.ofFn fun s : Fin a => positive (bitIndex v s)
  | .inr (.inl (v, s, t)) =>
      if s = t then [positive (bitIndex v s), negative (bitIndex v s)]
      else [negative (bitIndex v s), negative (bitIndex v t)]
  | .inr (.inr (j, τ)) =>
      let negatives := List.ofFn fun t : Fin q => negative (bitIndex (P.query j t) (τ t))
      if P.accept j τ then positive (bitIndex (P.query j ⟨0, hq⟩) (τ ⟨0, hq⟩)) :: negatives
      else negatives

def encodedBits {n a : ℕ} (σ : Fin n → Fin a) : List Bool :=
  List.ofFn fun i : Fin (n * a) =>
    decide ((finProdFinEquiv.symm i).2 = σ (finProdFinEquiv.symm i).1)

def readBit {n a : ℕ} (A : List Bool) (v : Fin n) (s : Fin a) : Bool :=
  A.getD (bitIndex v s).val false

def GoodBlock {n a : ℕ} (A : List Bool) (v : Fin n) : Prop :=
  ∃! s : Fin a, readBit A v s = true

instance {n a : ℕ} (A : List Bool) (v : Fin n) : Decidable (GoodBlock (a := a) A v) :=
  inferInstanceAs (Decidable (∃ s : Fin a, readBit A v s = true ∧
    ∀ t : Fin a, readBit A v t = true → t = s))

def badBlocks {n a : ℕ} (A : List Bool) : Finset (Fin n) :=
  Finset.univ.filter fun v => ¬ GoodBlock (a := a) A v

def failedLabels {n m a q : ℕ} (P : CSP n m a q) (hq : 0 < q)
    (A : List Bool) : Finset (ClauseLabel n m a q) :=
  Finset.univ.filter fun z => (clause P hq z).any (fun l => l.eval A) = false

end EthInapproximability.CurrentPaper.SourceBooleanEncoding
