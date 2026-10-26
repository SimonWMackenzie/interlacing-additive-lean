import CurrentAdditive.V39WTable

/-! The entry evaluator's retained public bank has ten nonblank source
positions. This exact layout lemma is independent of the physical supplier
of the raw graph and unary scalar words. -/

namespace CurrentAdditive.V39WMasterLayout
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
open Paper2 EthInapproximability.CurrentPaper
open V39RLoop

def scan (j : ScanJoin.JJ) : SrcX.JX := .inl (.inr (.inl j))
def graph : SrcX.JX := scan (.inr (.inl (.inl (.inl (.inl (.inl 0))))))

def dst : Fin 10 → SrcX.JX :=
  ![.inl (.inl (.inl FetchIndexed.myC)), .inl (.inl OTBody.sC),
    scan (.inl 1), scan (.inl 2), graph,
    .inr (.inl 0), .inr (.inl 1), .inr (.inl 2),
    .inr (.inr (.inl (.inl 2))), .inr (.inr (.inl (.inr 1)))]

theorem dst_injective : Function.Injective dst := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | simp [dst,scan,graph,FetchIndexed.myC,OTBody.sC] at h

def values (g : EncodedGraph.Graph) (p s q₁ w Q r : Nat) : Fin 10 → List Bool :=
  ![List.replicate (s+1) true, List.replicate s true,
    List.replicate r true, List.replicate g.edges.length true, EncodedGraph.encode g,
    List.replicate q₁ true, List.replicate s true, List.replicate Q true,
    List.replicate p true, List.replicate w true]

variable {p s q₁ q₂ w Q : Nat} [NeZero q₁] [NeZero q₂]
  [NeZero w] [NeZero Q] [NeZero s]

theorem master_at (g : EncodedGraph.Graph) (r : Nat) (i : Fin 10) :
    V39RLoop.master (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r (dst i) =
      values g p s q₁ w Q r i := by
  fin_cases i <;> rfl

theorem master_off (g : EncodedGraph.Graph) (r : Nat) (z : SrcX.JX)
    (hz : ∀ i, dst i ≠ z) :
    V39RLoop.master (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r z = [] := by
  fin_cases z <;> first
    | rfl
    | exact False.elim (hz 0 rfl)
    | exact False.elim (hz 1 rfl)
    | exact False.elim (hz 2 rfl)
    | exact False.elim (hz 3 rfl)
    | exact False.elim (hz 4 rfl)
    | exact False.elim (hz 5 rfl)
    | exact False.elim (hz 6 rfl)
    | exact False.elim (hz 7 rfl)
    | exact False.elim (hz 8 rfl)
    | exact False.elim (hz 9 rfl)

#print axioms master_at
#print axioms master_off
end
end CurrentAdditive.V39WMasterLayout
