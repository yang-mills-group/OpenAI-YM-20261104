import YM.FVA2.O.Read.Study
/-!
# Parameter-dependent smearing

Continuous representatives and cost through integrating against a fixed test.
No smoothness assertions on kernels outside test support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Read
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix NNReal ENNReal
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
variable { I J K: Type }{ n m d k:ℕ }{b:ℝ}
variable {A:I→ Points n→ ℂ}{ p:Test n }[MetricSpace I] { s:Set I }
lemma single_c (h: ContinuousOn ( Function.uncurry A ) ( s ×ˢ CoverP p )) {i:I}(he:i∈s): ContinuousOn ( A i ) ( CoverP p ):= h.comp (f:=fun i'=> (i,i')) ( Continuous.prodMk continuous_const ( continuous_id ( X:=Points n ) ) ).continuousOn ( fun _ hp=>⟨ he,hp ⟩ ) -- signature domain
lemma stays_c (h: IsCompact s)(he:ContinuousOn ( Function.uncurry A ) ( s ×ˢ CoverP p )): ContinuousOn ( fun i=> p.applyTo ( A i )) s:= by
    have hh:= IsCompact.uniformContinuousOn_of_continuous ( h.prod p.hasCompactSupport ) he; have hp:= value_0 p;
    intro x hx; refine Metric.continuousWithinAt_iff.mpr (fun ε hε=>?_ ); let B:=2*Value p+1; have h0 : 0<B:=by unfold B; linarith
    obtain ⟨δ,hδ,h⟩:= Metric.uniformContinuousOn_iff.mp hh (ε/B) (by positivity); refine ⟨δ,hδ,fun i hi ht=>?_ ⟩; rw [dist_eq_norm, ← smear_sub p ( single_c he hi ) ( single_c he hx ) ]; apply lt_of_le_of_lt (value_le p ( b:=ε/B ) ( ( single_c he hi ).sub ( single_c he hx ) ) (fun j hj=>show _ from ?_ )) _ -- may leave goals order
    · calc Value p*(ε/B) ≤ ( B-1 )*(ε/B) := (by gcongr; unfold B; linarith)
           _ < B*(ε/B) := (by gcongr; linarith)
           _ = ε := (by field_simp)
    specialize h _ ⟨hi,hj⟩ _ ⟨hx,hj⟩ ( show dist (i,j) (x,j)<δ from (by simpa only [Prod.dist_eq, dist_self,max_lt_iff] using And.intro ht hδ ) ); exact le_of_lt ( (dist_eq_norm ( A i j ) (A x j)).symm ▸ h ) -- orientation & implicit params
abbrev draw_s (A: I→ Points n→ Cn)(t:Test n)(s:Set I) : Prop:= ∀ i,ContinuousOn (fun j:I× Points n=> coeff i ( A j.1 j.2 ) ) ( s ×ˢ CoverP t )
variable {F:I→ Points n→ Cn}
lemma stays_fee (h:IsCompact s)(he:draw_s F p s)(i:ℕ): ContinuousOn (fun x=> coeff i ( smearing p (F x) ) ) s:= by simp_rw [smearing,coeff_mk]; exact stays_c ( A:=fun x k=> coeff i ( F x k ) ) h ( he i ) -- type_sorts
lemma draw_once (he:draw_s F p s){i:I}(ht:i∈s): draw p ( F i ):= fun j=> single_c ( A:=fun x k=> coeff j ( F x k ) ) ( he j ) ht
omit [MetricSpace I]
-- Cost-shape variant for standalone ℝ→integrals, avoid Unit reversal for inner s. Transfer through smear shape
lemma paid_u {f:Points n→ℝ→ Cn}(h:ChargeP d b (fun i:↥( CoverP p )=> f i.val))(he: ∀ᶠ t:ℝ in atTop, draw p ( fun x=> f x t )): ChargeP d b ( fun (_:I) t=> smearing p ( fun x=> f x t ) ):= fee_W p ( F:=fun _ t x=> f x t ) ( h.pull Prod.snd ) ( fun i _=>he.mono ( fun _ h _=> h i ) )
end YM.FVA2.O.Read
