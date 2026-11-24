import YM.FVA2.O.Read.Fire
/-!
# Observation geometry supports

For moving $T=exp(t)$ and profile $K$ interior at length one, exterior tests running
length-T fields in coordinates before expansion of their measure. Need only separated
configurations for ALL of these identities. Any estimator/smear against collisions
for small $t$ carries no meaning here.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Read
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
variable { G:Gauge }{ I:Type}{n m k d i:ℕ}{ H:ℝ→Frames G }{r:ℝ→Cn}{ V:Arenas G }{A:Album G}
variable { x:Points n }{y:Points m}{f:Fable G n}{ K:Set (Points n)}{P: Exterior m}{t v a:ℝ }
variable {u:Scan G n}{w: Scan G m}
lemma for_far {S:Set ( Points m )} (hp:IsCompact K)(hr:K⊆conf n)(h:IsCompact S)(he:S⊆Outside m): ∀ᶠ t:ℝ in atTop,∀ x∈K,∀ i∈S, forest x ( squeeze (-t) i )∈conf (n+m):= by -- fix S binding
    filter_upwards [ district hp hr h he ] with t h x hx i hi; rw [← squeeze_iff t,← crossN]; exact h i hi x hx
abbrev Church (t:ℝ)(K:Set (Points n))(P:Exterior m): Prop:= ∀ x∈K,∀ i ∈ CoverP P.val, forest x (squeeze (-t) i)∈ conf (n+m)
lemma spring (hp:IsCompact K)(he:K⊆conf n)(P: Exterior m): ∀ᶠ t:ℝ in atTop,Church t K P:= for_far hp he P.val.hasCompactSupport P.property
lemma known (h:Observed A)(he:Church t K P)(v:Scan G m): draw_s ( fun x (y: Points m)=>party A x ( squeeze (-t) y ) u v ) P.val K:= by
    intro i; let F: Points n× Points m→ Points (n+m):= fun x=>forest x.1 ( squeeze (-t) x.2 ); have ht: Continuous F:= Enh.continual ( f:=Prod.fst ) continuous_fst ( ( continuous_const_smul (exp (- -t)) ).comp continuous_snd : Continuous ( fun x:Points n× Points m => squeeze (-t) x.2 ) ) ; -- fill
    exact ( h _ _ i ).comp ( f:=F ) ht.continuousOn ( fun x hx=> he _ hx.1 _ hx.2 )
lemma indoors (h:Observed A)(he:Church t K P)(w:Scan G m): draw_s ( fun x y=> ShowT H A t x u y w ) P.val K:= by
    intro i; unfold ShowT LensT; apply stableV ( A₁:=fun _=> Acres (-t) (totalG w) ) ( fun _=>continuousOn_const ); unfold concert; exact sum_on _ _ ( fun i _ k=> stableV ( A₁:=fun _=> play (Astro H (-t)) w ( decode w i ) ) ( fun _=> continuousOn_const ) ( known h ( u:=u ) he ( decode w i ) ) k )
-- Lens linearity, before convolution sizes or states
abbrev looseT (H:ℝ→ Frames G)(A:Album G)(t:ℝ)(u:Scan G n)(v:Scan G m)(f:Fable G n)(k:ℕ)(x:Points n)(y:Points m): Cn:= ShowT H A t x u y v-∑ p:Toon G k, f x (flash p) * LongT H A t (flash p) y v
lemma Fare (p:Q G→Cn) (A:Album G): ∑ i:Toon G k, p ( flash i )* lonelyG A y ( flash i ) w= Lamp A k y w p:= LampT ..
lemma Lens_sub (ξ ϕ:Points m→ Scan G m→ Cn): LensT H t ξ y w-LensT H t ϕ y w= LensT H t ( fun i v=> ξ i v-ϕ i v ) y w:= by unfold LensT; rw [← mul_sub, concert_sub]
lemma Lens_payment (w:Scan G m)(H:ℝ→ Frames G)(p:Cn)(ξ:Points m→ Scan G m→ Cn): p*LensT H t ξ y w= LensT H t (fun i v=> p*ξ i v) y w:= by unfold LensT; rw [ mul_left_comm, concert_sum_r ]
lemma Lens_sum (w:Scan G m)(s:Finset I)(F:I→ Points m→ Scan G m→ Cn): ∑ i∈s,LensT H t (F i) y w= LensT H t ( fun p v=>∑ i∈s,F i p v ) y w:= by unfold LensT; rw [ ← Finset.mul_sum, concert_sum ]
lemma loose (t:ℝ)(y:Points m)(w:Scan G m) : looseT H A t u w f k x y= LensT H t ( fun y v=> Basket A u v ( f x ) k x y ) y w:= by
    unfold looseT LongT ShowT; simp_rw [ Lens_payment,Lens_sum,Fare,Basket,Lens_sub ]; -- Lens_sub maybe rew after Lamp
local notation "A0"=> install V
lemma price_yard (hp:Law V r H)(K':Set (Points m))(h:IsCompact K')(he:K' ⊆ Outside m)(hv:Fiasco A0 K k a i u f)(w:Scan G m): ChargeP i ( ( k:ℝ )+a ) (fun (p:K×K') t=> looseT H A0 t u w f k p.1.val p.2.val ):= by
    simp_rw [ loose,LensT ]; refine ChargeP.grow ( ChargeP.joint ( a:=-(totalG w:ℝ) ) ( b:=(k:ℝ)+a+(totalG w:ℝ) ) reflectV ?_ ) ( by linarith ); exact cost_tag ( T:=fun t=> Astro H (-t) ) ( Uniform.flips ( rhythm_v hp ) ) _ _ ( fun j=> hv _ K' ( decode w j ) h he ) -- inference
lemma quiet (hp: Law V r H)(ht:Regular V)(he:Observed A0)(hq:x∈K)(hi:Church t K P): draw P.val ( fun y=> looseT H A0 t u w f k x y ):= by
    intro i; unfold looseT; simp_rw [map_sub]; apply ContinuousOn.sub ( draw_once ( indoors he ( H:=H ) ( u:=u ) hi w ) hq i ) ( draw_sum _ _ (fun j _=> region _ ( forever hp he ht _ _ _ ) _ ) i ) -- binder free
-- smearing estimate
end YM.FVA2.O.Read
