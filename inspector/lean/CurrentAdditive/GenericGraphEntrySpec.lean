import CurrentAdditive.GenericBitvectorRecursiveJoin

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

/-! A short name for the exact, clocked physical graph-entry conclusion.
The proposition is literally the type of `recursive_entry`, so its full
fixed-program, input-bank, output-bank, and clock statement remain visible
to a reviewer by unfolding this abbreviation. -/

namespace Paper2.GenericGraphEntrySpec

open Paper2.GeneratorSource Paper2.RecursiveEntries
open Paper2.SourceProfileParameters
open EthInapproximability.CurrentPaper

abbrev EntrySpec (L w Q r : ℕ)
    (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] (hn : 0 < g.vertices) (hw : 0 < w) (hQ : 0 < Q)
    [NeZero (width L)] [NeZero (width L - 2)]
    [NeZero (outerWidth L)] [NeZero w] [NeZero Q]
    (hq : outerWidth L = SourceItems.sourceQ0
      (Fin (4 * width L)) (Fin g.edges.length) * r)
    (F : (Fin (LookupSeed.width L) → Bool) →
      Fin (LookupSeed.width L) → Bool)
    (K : ℕ)
    (x : Row (Fin (LookupSeed.width L) → Bool)
      (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices))
      (width L) (width L - 2) (outerWidth L) w Q K)
    (y : Column (Fin (LookupSeed.width L) → Bool)
      (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices))
      (width L) (width L - 2) (outerWidth L) w Q K) : Prop :=
  type_of% (GenericBitvectorRecursiveJoin.recursive_entry
    L w Q r g hg hn hw hQ hq F K x y)

theorem checked (L w Q r : ℕ)
    (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] (hn : 0 < g.vertices) (hw : 0 < w) (hQ : 0 < Q)
    [NeZero (width L)] [NeZero (width L - 2)]
    [NeZero (outerWidth L)] [NeZero w] [NeZero Q]
    (hq : outerWidth L = SourceItems.sourceQ0
      (Fin (4 * width L)) (Fin g.edges.length) * r)
    (F : (Fin (LookupSeed.width L) → Bool) →
      Fin (LookupSeed.width L) → Bool)
    (K : ℕ)
    (x : Row (Fin (LookupSeed.width L) → Bool)
      (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices))
      (width L) (width L - 2) (outerWidth L) w Q K)
    (y : Column (Fin (LookupSeed.width L) → Bool)
      (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices))
      (width L) (width L - 2) (outerWidth L) w Q K) :
    EntrySpec L w Q r g hg hn hw hQ hq F K x y :=
  GenericBitvectorRecursiveJoin.recursive_entry
    L w Q r g hg hn hw hQ hq F K x y

#print axioms checked

end Paper2.GenericGraphEntrySpec
