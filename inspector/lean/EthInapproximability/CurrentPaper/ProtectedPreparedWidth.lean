import EthInapproximability.CurrentPaper.ProtectedPreparedRouting

/-!
# Width transport for the literal protected routing theorem

Source: frozen v8 `A-stage4-details.tex`,
`lem:paper-protected-routed-closure`. This is only an equality transport
interface: the actual protected matrix keeps its original coordinate type.
-/

noncomputable section
open scoped Classical BigOperators
open NPCC Workspace.Types.Protocol Workspace.Types.CommComplexity Workspace.Types.Interlace

namespace EthInapproximability.CurrentPaper.ProtectedPreparedWidth
open Construction JointTransfer ProtectedGraphItems ProtectedDefects ProtectedLocalCopies
open ProtectedRoutedBound ProtectedPreparedRouting

universe u
variable {X Y : Type u} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- Apply the canonical-width theorem without changing the physical inputs,
vectors, retained sets, or protocol in its caller. -/
theorem physical_prepared_lower (base : X → Y → Bool)
    (a s q m R L nv nb H b w : ℕ) (heq : q = 2 ^ R * 2 ^ m)
    (hs : 0 < s) (hL : 0 < L) (hqOne : 0 < qOne a)
    (family : SecondFamily a q L X)
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    {x h ε xcap : ℝ}
    (inputs : OrdinaryInputs (H := H) (Function.swap (firstMatrix base a s))
      (fun l α => family l (Fin.cast heq.symm α)) x h ε)
    (hgraph : H + 1 ≤ Dfamily (interlaceFun base (qOne a + 3))
      (bracketGE X Y (qOne a + 3) xcap (1 / 2)))
    (B : Finset (ProtectedRows s L nv nb X))
    (A : Finset (ProtectedColumns a s q Y))
    (branch : ProtectedRows s L nv nb X → Fin s) (p bin : Fin s)
    (K : Finset (Fin L)) (hKdensity : h * (L : ℝ) ≤ K.card)
    (hKphysical : ∀ ℓ ∈ K, ∃ copy : TemplateLabels s L nv nb X,
      templateEmbedding s L nv nb bin (ℓ, copy) ∈ B ∧
      branch (templateEmbedding s L nv nb bin (ℓ, copy)) = p)
    (ordinary witnesses : Finset (Fin q)) (hsub : witnesses ⊆ ordinary)
    (hordinary : q ≤ ordinary.card + b)
    (hwitnesses : w ≤ witnesses.card + b) (hexcess : 4 * b < w)
    (hgood : ∀ α ∈ ordinary,
      α ∉ ParameterizedNP.DenseSourceOwners.templateBadSet ⌈(Fintype.card X : ℝ) * xcap⌉₊
        (coordinateSupport family K) ∧ α ∉ diagonalDefects a s q A)
    (hWit : ∀ α ∈ witnesses, ∃ i j k : Fin (nv + nb), i ≠ j ∧
      vectors i α = true ∧ vectors j α = true ∧ vectors k α = false ∧
      ItemRepresentatives (t := ⌈(Fintype.card X : ℝ) * xcap⌉₊) order B branch p i ∧
      ItemRepresentatives (t := ⌈(Fintype.card X : ℝ) * xcap⌉₊) order B branch p j ∧
      ItemRepresentatives (t := ⌈(Fintype.card X : ℝ) * xcap⌉₊) order B branch p k)
    (hscale : (2 : ℝ) ^ (R + m + 1) * x ≤ 1 / 4)
    (P : Protocol (ProtectedColumns a s q Y) (ProtectedRows s L nv nb X) Bool)
    (hcomp : ∀ r ∈ B, branch r = p → ∀ c ∈ A,
      P.eval c r = protectedMatrix base a s q L nv nb hs family order vectors cap c r) :
    H + (R + m) + 1 ≤ P.cost := by
  subst q
  simpa only [Fin.cast_refl] using
    ProtectedPreparedRouting.physical_prepared_lower base a s m R L nv nb H b w
      hs hL hqOne family order vectors cap inputs hgraph B A branch p bin K hKdensity
      hKphysical ordinary witnesses hsub hordinary hwitnesses hexcess hgood hWit hscale P hcomp

end EthInapproximability.CurrentPaper.ProtectedPreparedWidth
