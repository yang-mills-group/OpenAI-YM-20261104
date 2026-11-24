import YM.UVExt.TieValue
import YM.UVExt.BaseStep
/-!
# Same-family interim endpoint with tie interpolation at retained periods

This theorem does not label a subsequence as the full UV sequence. Its W interpolant at order
zero is literal; higher-order and full-tail goals require additional arguments. The facts in
`BaseStep` about the unmasked quadratic kernel, bare integrals and normalized vacuum density
can also be attached by further extraction (not needed to define the cylinders).
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt
open Set Filter Function Extraction Bid Dash Lattice Metric MeasureTheory Spec
open YM.Next.Extract
open scoped Topology Classical BigOperators

variable {G : Gauge} {C : Family G} {f g : Extraction.Order} {A T : Table C.book} {M : ℕ→Table C.book}
variable {R : Bin A} {E : DiffPlan T} (H : Base C f A M R T E)
include H
lemma first_base : FiniteFirstDifference C f := first_difference H.family H.center H.arrives.born
     H.arrives.census.integral R (fun d=> Bin.exactC R H.arrives.census.integral (H.pinned.p d) (H.pinned.q d)) H.carries

structure InterimTie (C : Family G) (f : Extraction.Order) (T : Table C.book) : Prop where
  step : FiniteFirstDifference C f
  tied : ∀ n (K : Set (Points n)), IsCompact K → K ⊆ conf n → ∀ q : Fin n→C.book.Token,
    ∀ᶠ p : ℕ in atTop, ContinuousOn (Grid.picture C f (f.per p) n q) K ∧
       TendstoUniformlyOn (fun i=>Grid.film C q (f.mesh i) (f.per p) ([]:List (Grid.Index n)))
         (Grid.picture C f (f.per p) n q) atTop K
  tiles : ∀ n (q : Fin n→C.book.Token), Extraction.Meets (conf n) (fun p=>Grid.picture C f (f.per p) n q)
        (fun x : Points n=>T.read x q)

lemma interim : InterimTie C f T := ⟨first_base H,fun n K hk hq q =>
    Grid.tie_picture n q K hk hq H.clean.mesh.mesh (first_base H),fun n q=>Grid.volume_fill n q
     (T.smooth_read H.clean.smooth q).continuousOn H.clean.mesh (first_base H)⟩

omit H
/-- Interim production on an actual family and a further extraction from any given order. -/
theorem initial_tie (G : Gauge) (h : G.Simple) (f : Extraction.Order) :
    ∃ (C : Family G), C.Makes ∧ Spec.Calibrated C ∧ Extraction.Wcmain C ∧
      ∃ (g : Extraction.Order) (T : Table C.book), Nonempty (Spec.Final C (f.refine g) T) ∧ InterimTie C (f.refine g) T := by
  obtain ⟨C,-,hC,hM,hW,H,hQ,hF⟩:= YM.PhysicalNext.Repeat.Legato.noel h one_pos
  obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:= hF f
  obtain ⟨hs,hG⟩:= hQ (f.refine g) s.copies
  obtain ⟨M,I,hI,p⟩:= MergeProof.Acme.emanate (W:=E) H h hs hG s hA.clean.ready hA.clean.tilt
  exact ⟨C,hM,hC,hW,g,T,MergeProof.Acme.glistens hC hA.clean.ready hA.clean.tilt p,interim hA⟩
end YM.UVExt
