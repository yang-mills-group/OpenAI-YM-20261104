import YM.FVA2.O.Hue.Shine
/-!
# Real Taylor slices in a fixed rank/weight budget

For the MS OPE projection at large distance. Obtain shift data
from the free Ward-closed local space including exact directions (`Ker` etc.).
`camera`: transfer polynomial bounds from pointwise pricing to coefficients
in any such finite-dimensional basis. No claim that the quantities `Profit`
estimates are themselves polynomials.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Hue
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Flux Book High Detect MS.Color MS.Local.Physical MS.Land Domain Convolve
open Lives O.Ward MS.City MS.Rake Outlook Tune O.Pad Submodule
open scoped Topology ContDiff
variable {I J :Type} {G:Gauge}{B:Deck G}{K: Booked B}{M:MS_Data G K}{P:IntervalFamily I}{η:I→ℝ}{n j d k h:ℕ}{b t:ℤ}{X Y:T ( Glade G I )}{a:I→ℝ}{f:I→ Law G}{F:Law G}
lemma camera (H:Submodule ℝ (J→ℂ)) [FiniteDimensional ℝ H](F:I→ H)(hp:∀ i:J, Profit P.dawn (fun j=> (F j).val i))(p: Module.Dual ℝ H): Profit P.dawn (p∘F):= by
    let Y (i:J): H→ₗ[ℝ] ℂ:= (LinearMap.proj i).comp H.subtype; let Q (x:J× (ℂ→L[ℝ]ℝ)):= x.2.toLinearMap.comp (Y x.1); let V:= span ℝ (Set.range Q); have hV: V.dualCoannihilator=⊥:= by
       refine le_antisymm (fun x hx=>?_) bot_le; apply (mem_bot _).mpr; apply Subtype.ext; funext i; have hp(A:ℂ→L[ℝ]ℝ):= (Submodule.mem_dualCoannihilator _).mp hx (Q (i,A)) ( Submodule.subset_span ( Set.mem_range_self _ ) ); exact Complex.ext (hp Complex.reCLM) (hp Complex.imCLM)
    have he : V= ⊤:= by apply Submodule.eq_top_of_finrank_eq; rw [Subspace.dual_finrank_eq]; have hx:= Subspace.finrank_add_finrank_dualCoannihilator_eq V; rw [hV] at hx; simpa using hx
    have hw : p∈V:= he ▸ Submodule.mem_top; refine Submodule.span_induction (p:=fun (p:Module.Dual ℝ H) _=> Profit P.dawn (p ∘ F)) ?_ Profit.z (fun _ _ _ _ hz hx=> hz.plus hx) (fun i p _ hx=>hx.scalar i) hw; rintro Z ⟨⟨i,a⟩,rfl⟩; exact (hp i).L a
private def Ker (h k: ℕ)(G:Gauge): Submodule ℝ (Law G):= Local.Physical.Lease G h k 0 ⊓ LinearMap.ker ( kills G )
private instance (h k:ℕ)(G:Gauge): FiniteDimensional ℝ (Ker h k G):= Module.Finite.of_injective (Submodule.inclusion (show Ker h k G ≤ Local.Physical.Lease G h k 0 from inf_le_left )) (Submodule.inclusion_injective _)
lemma shine_family (hd:d ≤ h)(hf:∀ i, f i∈Local.Physical.Lease G d k 0)(hx:∀ i,natQ ( f i )=0)(hs:∀ l, Profit P.dawn (fun i=> f i l))(he:allowance P η): Shine M η P h n k f:= by
    let L:= Ker d k G; let B:= Module.finBasis ℝ L; let F(i:I):L:=⟨ f i,hf i,hx i⟩; let a j i:= B.repr ( F i ) j; let Φ j i:= a j i • (B j).val; have H j: Shine M η P h n k ( Φ j ):= shine_cash ( shine_seed ( F:=(B j).val ) (show _∧ _ from (B j).property).1 ( show _∧ _ from ( B j ).property ).2 hd he ) ( camera L F hs ( B.coord j ) )
    rw [ show f=∑ i, Φ i from ?_ ]; exact shine_pile Finset.univ H; funext i; rw [ Finset.sum_apply ]; change ( L.subtype ( F i ) ) = _; rw [← B.sum_repr (F i),map_sum]; simp only [map_smul]; rfl
lemma shine_price (hv:P.beg=0)(hT:Every P)(hd:d≤h)(hs:allowance P η)(hP:Certified X M η 0)(hp:prime P ( X n ))(hx:width P ( X n ) h (k+2))(he:∀ m<n,paidC P (X m) h)(hA:∀ i,Absent (col (X n) i) false k d): Shine M η P h n k ( flash ( X n ) k d ):= by
    have v:=hP.1; let F:= X n; have hF:= (v.life n).cross; have hB: Warm ( helm M η X n ) false:= ( plenary M|>.lives v.life n ).cross; obtain hC:= h_cost hF hs decay_p hx he; have H i:= broadW hF hB hT (v.vital n) hC i; have hd:(d:ℤ)≤h:= by omega
    exact shine_family (by omega) (fun i=> lease_one.mpr ⟨ slice_solid (H i) hd (fun t=> (v.life n).tone i t.2), slice_form (H i) hd,rank_slice ⟩) ( X_closed hP hd hs hT hx he hA ) ( paid_φ hv hT hF hB ( v.vital n ) hC hp hd ) hs
end YM.FVA2.O.Hue
