import CurrentAdditive.V42GeneratedConstruction
import CurrentAdditive.V39RecursiveTable
import Paper2.SourceRank

/-! Literal current two-tag full-product decoding of every generated input.
No promise, profile, rank conclusion or distinctness of decoded labels is an
input. The original generated indices are retained in the source matrix. -/
namespace CurrentAdditive.V42GeneratedEmbedding

open Paper2 Paper2.SourceMatrix Paper2.RankLeaves Workspace.Types.CommComplexity
open V39GeneratedConstruction

variable {q₁ q₂ s w Q nx ny ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  {μI : PositiveRationalLaw (Fin ni)}
  (src : SourceData (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

def fullColumn : src.Column → V38Matrix.TaggedColumn q₁ q₂ s (Fin ny)
  | .inl (j,γ) => .inl (tail (src.gamma.decode γ),
      fun p => let a:=src.outer.decode j p; (a.1,src.gamma.decode a.2))
  | .inr (a,γ) => .inr (a,src.gamma.decode γ)

theorem erase_fullColumn (Z : src.Column) :
    V39RecursiveTable.eraseTag (fullColumn src Z)=src.decodeColumn Z := by
  cases Z <;> rfl

def fullSuccessor (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) :
    (Fin Q → Fin w × V38Matrix.TaggedColumn q₁ q₂ s (Fin ny)) →
    (Fin Q × (Fin w → RawRow q₁ q₂ s (Fin nx) (Fin ni))) → Bool :=
  fun z a =>
    let p:=z a.1
    raw R activity (a.2 p.1) (V39RecursiveTable.eraseTag p.2)

def fullRowDecode
    (out : ExactList 8192 Q (Fin w × src.Column) (product (uniform w) src.columnLaw))
    (j : Fin out.size) : Fin Q → Fin w × V38Matrix.TaggedColumn q₁ q₂ s (Fin ny) :=
  fun p => ((out.decode j p).1,fullColumn src (out.decode j p).2)

def fullColumnDecode (st : src.Streams (w := w) (μI := μI))
    (a : Fin Q × st.Label) : Fin Q × (Fin w → RawRow q₁ q₂ s (Fin nx) (Fin ni)) :=
  (a.1,fun p => src.decodeRow (SourceData.Streams.decode src st a.2 p))

theorem successor_decoded_entry
    (st : src.Streams (w := w) (μI := μI))
    (out : ExactList 8192 Q (Fin w × src.Column) (product (uniform w) src.columnLaw))
    (R : Fin nx → Fin ny → Bool) (activity : Fin ni → Fin q₂ → Option (Fin s))
    (j : Fin out.size) (a : Fin Q × st.Label) :
    src.successor st out R activity j a =
      fullSuccessor (q₁ := q₁) (w := w) (Q := Q) R activity (fullRowDecode src out j)
        (fullColumnDecode src st a) := by
  simp only [SourceData.successor,SourceData.B,fullSuccessor,fullRowDecode,fullColumnDecode,
    erase_fullColumn]

theorem numbered_decoded_entry
    (st : src.Streams (w := w) (μI := μI))
    (out : ExactList 8192 Q (Fin w × src.Column) (product (uniform w) src.columnLaw))
    (R : Fin nx → Fin ny → Bool) (activity : Fin ni → Fin q₂ → Option (Fin s))
    (j : Fin out.size) (a : Fin (Q*(st.metadata.size*(st.base.size*st.selector.size)))) :
    (src.numbered st out R activity).entry j a =
      fullSuccessor (q₁ := q₁) (w := w) (Q := Q) R activity (fullRowDecode src out j)
        (fullColumnDecode src st ((SourceData.successorColumnOrder src st).symm a)) :=
  successor_decoded_entry src st out R activity j _

theorem full_rank_le (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) :
    (realMatrix (fullSuccessor (q₁ := q₁) (w := w) (Q := Q) R activity)).rank ≤
      Q*w*(s*q₁*q₂+ni)*(realMatrix R).rank := by
  classical
  let N := fun (Z : V38Matrix.TaggedColumn q₁ q₂ s (Fin ny))
    (a : RawRow q₁ q₂ s (Fin nx) (Fin ni)) => raw R activity a (V39RecursiveTable.eraseTag Z)
  let W := fun (z : Fin w → RawRow q₁ q₂ s (Fin nx) (Fin ni))
    (a : Fin w × V38Matrix.TaggedColumn q₁ q₂ s (Fin ny)) => N a.2 (z a.1)
  have hN : (realMatrix N).rank≤(s*q₁*q₂+ni)*(realMatrix R).rank := by
    change (realMatrix (fun Z a => raw (q₁ := q₁) R activity a (V39RecursiveTable.eraseTag Z))).rank≤_
    rw [transpose_rank]
    exact (pullback_rank_le (raw (q₁ := q₁) R activity) id V39RecursiveTable.eraseTag).trans
      (by simpa only [Fintype.card_fin] using raw_rank_le R activity)
  have hW : (realMatrix W).rank≤w*(realMatrix N).rank := by
    change (realMatrix (fun z a => fullInterlace N w a z)).rank≤_
    rw [transpose_rank]
    exact fullInterlace_rank_le N w
  have hS : (realMatrix (fullSuccessor (q₁ := q₁) (w := w) (Q := Q) R activity)).rank≤Q*(realMatrix W).rank := by
    change (realMatrix (fun z a => fullInterlace W Q a z)).rank≤_
    rw [transpose_rank]
    exact fullInterlace_rank_le W Q
  exact (hS.trans (Nat.mul_le_mul_left Q (hW.trans (Nat.mul_le_mul_left w hN)))).trans_eq (by ring)

theorem successor_rank_le
    (st : src.Streams (w := w) (μI := μI))
    (out : ExactList 8192 Q (Fin w × src.Column) (product (uniform w) src.columnLaw))
    (R : Fin nx → Fin ny → Bool) (activity : Fin ni → Fin q₂ → Option (Fin s))
    (hI : ni≤2*s*q₂) (hq₁ : q₁+2=s)
    (a b c d : ℕ) (hs : s=2^a) (hq : q₂=2^b) (hw : w=2^c) (hQ : Q=2^d) :
    (realMatrix (src.successor st out R activity)).rank≤2^(a+a+b+c+d)*(realMatrix R).rank := by
  have he : src.successor st out R activity =
      fun j u => fullSuccessor (q₁ := q₁) (w := w) (Q := Q) R activity
        (fullRowDecode src out j) (fullColumnDecode src st u) := by
    funext j u
    exact successor_decoded_entry src st out R activity j u
  rw [he]
  apply (pullback_rank_le _ _ _).trans ((full_rank_le (q₁ := q₁) (w := w) (Q := Q) R activity).trans ?_)
  have hfactor : s*q₁*q₂+ni ≤ s*q₂*(q₁+2) := by nlinarith only [hI]
  calc
    _ ≤ Q*w*(s*q₂*(q₁+2))*(realMatrix R).rank := by gcongr
    _ = _ := by rw [hq₁,hs,hq,hw,hQ]; simp only [pow_add]; ring

theorem numbered_rank_le
    (st : src.Streams (w := w) (μI := μI))
    (out : ExactList 8192 Q (Fin w × src.Column) (product (uniform w) src.columnLaw))
    (R : Fin nx → Fin ny → Bool) (activity : Fin ni → Fin q₂ → Option (Fin s))
    (hI : ni≤2*s*q₂) (hq₁ : q₁+2=s)
    (a b c d : ℕ) (hs : s=2^a) (hq : q₂=2^b) (hw : w=2^c) (hQ : Q=2^d) :
    (realMatrix (src.numbered st out R activity).entry).rank≤2^(a+a+b+c+d)*(realMatrix R).rank := by
  have he : (src.numbered st out R activity).entry=
      fun j u => src.successor st out R activity j ((SourceData.successorColumnOrder src st).symm u) := rfl
  rw [he]
  exact (pullback_rank_le _ id (SourceData.successorColumnOrder src st).symm).trans
    (successor_rank_le src st out R activity hI hq₁ a b c d hs hq hw hQ)

#print axioms successor_decoded_entry
#print axioms numbered_decoded_entry
#print axioms numbered_rank_le

end CurrentAdditive.V42GeneratedEmbedding

