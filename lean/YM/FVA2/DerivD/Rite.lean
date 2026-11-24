import YM.FVA2.DerivD.Inside
import YM.FVA2.O.Canon.Docket
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.DerivD
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
/-!
# Uniform limits give the gradient identity for FAR coefficient functions

Apply the first derivative insertion identity to the defining FAR estimates.
Gain the verdict on the limiting unit coefficients in the inner shapes
(all orders). No joint limit with any UV regulator removal. Need the rank
criteria for the OPE Gram to use this, supplied in the `O` modules.
-/
open O.Read O.Canon Dframe Equator Facets
open scoped NNReal ENNReal
variable {G:Gauge}{ I:Type }{n m k d:ℕ}{Q':Staff G}{A:Album G}{V:Arenas G}{H:ℝ→ Frames G}{r:ℝ→ Cn}{P: Geology G d}{s:Set (Points n)}{u:Scan G n}{t:ℝ}
variable {x:Points n}
lemma occurs (y:Points m)(h:Influence Q' A)(ht: forest x ( squeeze (-t) y )∈ conf (n+m))(v:Scan G m): Shard Q' ( fun x i=> ShowT H A t x i y v ) x:= by
    apply Shard.along (F:=fun x u=>concert (Astro H (-t)) v ( fun v=> party A x ( squeeze (-t) y ) u v )) (d:=Acres (-t) (totalG v)); unfold concert; apply Shard.league; intro i hi; apply Shard.along ( F:=fun x u=> party A x ( squeeze (-t) y ) u ( decode v i ) ); exact interior_phase h ht _
lemma increases (h:Influence Q' A)(hh:IsCompact s)(he:Observed A)(hP:O.Read.Part t s P)(ht:x∈ interior s)(b:Toon G d): Shard Q' (fun x u=> Perch H A P u t x b) x:= by
    unfold Perch; apply Shard.league; intro i hi; exact Shard.profiles (F:=fun x y u=> ShowT H A t x u y (LetterQ i)) ( fun u=> indoors he ( hP b i ) _ ) hh ht ( fun x hx y hy=> occurs _ h ( hP b i x (interior_subset hx) y hy ) _ )
lemma color_f (h: Influence Q' A)(hh:IsCompact s)( he: Observed A)(hP:O.Read.Part t s P)(ht:x∈ interior s)(b:Toon G d): Shard Q' (fun x u=> QuoteShape H A P u t x b) x := by
    unfold QuoteShape Matrix.mulVec dotProduct; apply Shard.league; intro i hi; exact Shard.along ( increases h hh he hP ht i ) _ -- H defeq
private lemma uf_sum {E I J:Type}[NormedAddCommGroup E](s:Finset I){f:I→ℝ→J→E}{g:I→J→ E}{l:Filter J}(h:∀ i∈s, TendstoUniformlyOnFilter ( f i ) ( g i ) atTop l): TendstoUniformlyOnFilter (fun i p=>∑ j∈s,f j i p ) (fun p=> ∑ j∈s,g j p ) atTop l:= by
    induction s using Finset.induction_on with| empty=> simpa only [Finset.sum_empty] using! Filter.Tendsto.tendstoUniformlyOnFilter_const (g:= fun _ : ℝ=>(0:E)) tendsto_const_nhds l| insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact TendstoUniformlyOnFilter.add ( h i (by simp) ) (ih (fun j hj=> h j (by simp [hj])))
local notation "V'"=> install V
variable (hp:Physical V r H)(he:Detected V P)(hx:x∈conf n)
include hp hx he
lemma far_proper (hQ: Influence Q' (install V))(b:Toon G d): Shard Q' ( fun ( x:Points n )(u:Scan G n)=> FarCoefficients V u x ( flash b ) ) x:= by
    let D(q:Points n)(v:Scan G n):= FarCoefficients V v q ( flash b ); intro u i;
    let f(t:ℝ)(q:Points n)(v:Scan G n):= QuoteShape H V' P v t q b; obtain ⟨ s,hs,hx',ht ⟩:= exists_compact_subset ( conf_open n ) ( show x∈ conf n from hx ); have hh:= isOpen_interior.mem_nhds hx';
    have hft (k:ℕ)(v: Scan G n)(x:Points n)(hx:x∈ s): Tendsto (fun t=> coeff k ( f t x v )) atTop (𝓝 ( coeff k ( D x v ) )):= TendstoUniformlyOn.tendsto_at (α:=Points n) (x:=x) (honest hp.scope hp.dimensions hp.awake hs ht ( hp.far v ) he b k ) hx
    have hW(k:ℕ)(v: Scan G n) : TendstoUniformlyOnFilter (fun t y=> coeff k ( f t y v ) ) (fun y=> coeff k ( D y v )) atTop (𝓝 x):= ( honest hp.scope hp.dimensions hp.awake hs ht ( hp.far v ) he b k ).tendstoUniformlyOnFilter.mono_right ( le_principal_iff.mpr ( mem_interior_iff_mem_nhds.mp hx' ) );
    have hC(t:ℝ)(y:Points n)(hT:O.Read.Part t s P)(hv:y∈ interior s):= color_f (H:=H) hQ hs hp.awake hT hv b;
    let ℓ (g:Scan G n→ Cn):=DerivD.Γ Q' g u i;
    refine hasFDerivAt_of_tendstoUniformlyOnFilter ( f:=fun t x=> coeff i ( f t x u ) ) ( f':=fun t y=> ℓ ( f t y ) ) ( g':=fun y=> ℓ ( D y ) ) ?_ (( ( O.Read.life P hs ht ).prod_mk ( Filter.eventually_of_mem hh (fun _ h=> (show _∈ interior s from h) ) ) ).mono (fun i hi=> hC i.1 i.2 hi.1 hi.2 _ _) ) ( eventually_of_mem hh ( fun v hv=> hft i u v ( interior_subset hv ) ) ); -- hh as mem / filter lemma check
    unfold ℓ DerivD.Γ; apply uf_sum; intro a _; apply uf_sum; intro b _; apply ( italy a b ).uniformContinuous.comp_tendstoUniformlyOnFilter ( f:=fun x=> coeff i ( Raise Q' a b u (D x) ) ) ( F:=fun t x=> coeff i ( Raise Q' a b u ( f t x ) )); unfold Raise; simp_rw [LinearMap.coe_mk, AddHom.coe_mk,map_sum, coeffF ]; apply uf_sum; intro v _; apply uf_sum; intro k _; exact ( ContinuousLinearMap.mul ℝ ℂ ( coeff k ( Q' _ b v ) ) ).uniformContinuous.comp_tendstoUniformlyOnFilter ( hW _ _ ) -- maybe F binder uppercase
omit he
lemma establish (hQ:Influence Q' V')(b:Q G): Shard Q' ( fun ( x: Points n ) (u:Scan G n)=> FarCoefficients V u x b ) x:= by
    obtain ⟨P,hP,ht⟩:= Physical.light hp ( heft b ); exact far_proper hp ht hx hQ ( grab b )
end YM.FVA2.DerivD
