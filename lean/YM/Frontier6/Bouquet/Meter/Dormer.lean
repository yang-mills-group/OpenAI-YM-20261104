import YM.Frontier6.Bouquet.Meter.MergeCover

/-! Join point rule, including the support condition on the WHOLE root normals
 and the smaller (per-spin) boundary tests within finite cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q R:Ensemble} (g:Q≤R)
variable {Y:Type}[NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
    {x:Seats R} {B:Balcony R}{H:Patron S R Y}{f:Full (fiber R)}(he:Gentle H B)(hf:Fair f B x)
namespace Courses
abbrev refineD (g:Q≤R): Down Q ↪ Down R:= ⟨fun p=> ⟨p.val,p.property.trans g⟩, fun _ _ he=>Subtype.ext (congr_arg (fun x: Down R=> x.val) he)⟩
lemma splitIndex (g:Q≤R) {u:Down R}: u.val ≤ Q ↔ u∈ Finset.univ.map (refineD g):=by
   simp only [Finset.mem_map,Finset.mem_univ,true_and]; refine ⟨fun hh=> ⟨⟨_,hh⟩,rfl⟩,fun ⟨x,hx⟩=>?_⟩; rw [← hx]; exact x.property
end Courses

def Glued (x:Seats R)(H:Patron S R Y)(f:Full (fiber R))(z:Margin R Q): Y:= regulator K A T (transit g x z) (convey g H) (slit T g z f)
lemma GlueComplies (he':∀ z∈tsupport f, Separate g z)(hf:Fair f B x)(he:Gentle H B): regulator K A T x H f=∫ z, Glued K A T g x H f z:=by
   unfold regulator; unfold Glued regulator
   let w(y:Down R):= branch K A T y.property x H f; let S:= Finset.univ.map (Courses.refineD g); change ∑ i,w i=_; rw [← sum_subset (f:=w) (Finset.subset_univ S)] -- orientation name
   · unfold S; rw [Finset.sum_map,integral_finsetSum]; exacts [sum_congr rfl (fun i _=> crust K A T i.property g he hf), fun i _=> branch_folding K A T i.property g he hf]
   intro i _ hi; unfold w branch; exact Finset.sum_eq_zero fun p _=>gone K A T i.property H p g he' (fun hv=>hi (Courses.splitIndex g|>.mp hv))
lemma glued_apt (hf:Fair f B x)(he:Gentle H B): Integrable (Glued K A T g x H f):= integrable_finsetSum _ (fun i _=>branch_folding K A T (show i.val ≤ Q from i.property) g he hf)
lemma absent_choice {p:Pod}{f:Full (fiber R)}(h:p∈ R.choose)(hp:p∉ Q.choose)(he':∀ z∈tsupport f, Separate g z) {J: Ensemble}(hj:J ≤ R)(hv:p∈ J.choose)(x:Seats R): branch K A T hj x H f=0:=by
   have ht :¬ J ≤ Q:=by
       intro ht; obtain ⟨i,hi,he⟩:= ht.2 p hv; obtain ⟨q,hq,hH⟩:= g.2 i hi; have h':= same h hq (p.here_mem) (hH (he p.here_mem)); exact hp ((le_antisymm he (h' ▸ hH)) ▸ hi)
   unfold branch; exact Finset.sum_eq_zero (fun p _=> gone K A T hj H p g he' ht)
end YM.Frontier6.Bouquet
