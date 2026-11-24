import YM.FVA2.O.Read.Zone
/-!
# Large-time cost of point-wise FAR quote

`post_quote`: try reading off the unit OPE coefficient by the far-profile operation. Both
the exterior smear and the projection by Sheet inverse have their appropriate T powers;
net cost of the error decays with at least the gap a when positive (up to log factors).
Uniform over a fixed compact of unscaled input shapes. `honest` specializes to convergence
(an `AllC` candidate at hand). Only need the rank criterion `Detected` on the chosen
far-test profile (not positivity itself), with the law, regularity and continuity as explicit.
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
variable { G:Gauge }{ I:Type }{n m d k i:ℕ}{t a:ℝ}{V: Arenas G}{P:Geology G d}{ H:ℝ→Frames G }{ r:ℝ→ Cn }
variable { x:Points n }{ y:Points m }{ s:Set (Points n) }{Q':Exterior m}{ A:Album G }{u: Scan G n}{v:Scan G m}{ f:Fable G n }
local notation "V'"=> install V
local notation "S"=> Sheet H V' P
abbrev Perch (H:ℝ→ Frames G)(A:Album G)(P:Geology G d)(u:Scan G n)(t:ℝ)(x:Points n): Toon G d→ Cn := fun i=> ∑ j:Toon G d, smearing ( P i j ).val ( fun y:Points 1=> ShowT H A t x u y ( LetterQ j ) )
abbrev QuoteShape (H:ℝ→ Frames G)(A:Album G)(P:Geology G d)(u:Scan G n)(t:ℝ)(x:Points n): Toon G d→ Cn := ( ( Sheet H A P t )⁻¹ ) *ᵥ Perch H A P u t x
abbrev FarReader (H:ℝ→ Frames G)(A:Album G)(P:Geology G d)(f:Fable G n)(u:Scan G n)(t:ℝ)(x: Points n): Toon G d→ Cn:= fun i=> ∑ j:Toon G d, smearing ( P i j ).val ( fun y:Points 1=> looseT H A t u ( LetterQ j ) f d x y )
abbrev ROI (f:Fable G n)(x:Points n)(i:Toon G d):= f x ( flash i )
abbrev Part (t:ℝ)(s:Set (Points n))(P:Geology G d): Prop:= ∀ i j,Church t s ( P i j )
lemma life (P:Geology G d)(h:IsCompact s)(ht:s⊆conf n): ∀ᶠ t:ℝ in atTop, Part t s P:= eventually_all.mpr fun i=> eventually_all.mpr fun j=> spring h ht ( P i j )
lemma look (hp:IsCompact s)(he: Part t s P)(h:Observed A) (i:ℕ)(b:Toon G d): ContinuousOn ( fun x=> coeff i ( Perch H A P u t x b )) s:= sum_on _ _ ( fun j _ i=> stays_fee hp ( indoors h ( u:=u ) (he b j) ( LetterQ j ) ) i ) i
variable (h:Law V r H)(hp:Regular V)(he: Observed ( install V ))
include h hp he
lemma account (F0:Exterior m)(ht:x∈s)(hT: Church t s F0)(v:Scan G m): smearing F0.val ( fun y=> looseT H V' t u v f d x y )= smearing F0.val (fun y=> ShowT H V' t x u y v) - ∑ p:Toon G d, f x ( flash p )*smearing F0.val ( fun y=>LongT H V' t ( flash p ) y v ):= by -- variable V conflict
    unfold looseT; rw [ smearing_sub, smearing_sum ]; · simp_rw [ smearing_mul F0.val ( forever h he hp _ _ F0 ) _ ]
    · intro i hi; exact region _ ( forever h he hp _ _ _ ) _
    · exact draw_once ( indoors he ( u:=u ) hT v ) ht
    exact draw_sum _ _ ( fun j _=> region _ ( forever h he hp _ _ _ ) _ )
lemma table_0 (hr:Part t s P)(ht:x∈s) : FarReader H V' P f u t x= Perch H V' P u t x - S t *ᵥ ROI f x := by
    funext i; unfold FarReader; simp_rw [ account h hp he _ ht ( hr i _ ), Finset.sum_sub_distrib, Pi.sub_apply, Matrix.mulVec,dotProduct, Sheet, Finset.sum_mul ]; refine congr_arg ( _-· ) ?_; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun j _=> Finset.sum_congr rfl fun k _=> mul_comm .. )
lemma quote_shape_b (hr: Part t s P)(hQ:Detected V P)(ht:x∈s): QuoteShape H V' P u t x - ROI f x = ( S t )⁻¹ *ᵥ FarReader H V' P f u t x := by
    rw [table_0 h hp he hr ht, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (( Matrix.isUnit_iff_isUnit_det _ ).mp ( sealed_t h he hp hQ )), Matrix.one_mulVec ]
lemma err_value (hK:IsCompact s)(hr:s⊆ conf n)(ht:Fiasco V' s d a k u f)(b:Toon G d): ChargeP k ((d:ℝ)+a) ( fun (x:↥s) t=> FarReader H V' P f u t x.val b ):= by
    unfold FarReader; apply ChargeP.sum; intro j hj; let F:= P b j; let s':= CoverP F.val; let v:= LetterQ j; obtain hv:= price_yard h s' F.val.hasCompactSupport F.property ht v;
    exact fee_W F.val ( F:=fun (i:↥s) t y=> looseT H V' t u v f d i.val y ) hv ( fun i _=> ( spring hK hr F ).mono ( fun t hh x=> quiet h hp he x.property hh i ) )
lemma post_quote (hk:IsCompact s)(hr:s⊆conf n)(ht:Detected V P)(hh:Fiasco V' s d a k u f)(b:Toon G d): ChargeP k ((d:ℝ)+a-( heft ( flash b ):ℝ) ) ( fun (x:↥s) t=> QuoteShape H V' P u t x.val b- f x.val (flash b) ):= by
    obtain hA : ChargeP k ((d:ℝ)+a- ( heft ( flash b ):ℝ)) ( fun (x:↥s) t=> ((S t)⁻¹ *ᵥ FarReader H V' P f u t x.val) b ) := by unfold Matrix.mulVec dotProduct; refine ChargeP.sum _ ( fun j _=>ChargeP.grow ( ChargeP.joint ( b:=(d:ℝ)+a ) ( budget_Gram h he hp ht b j ) ?_ ) (by linarith)); exact err_value h hp he hk hr hh j
    intro i hi; refine Rain.raise (hA i hi) ( ( life P hk hr ).mono ( fun t hm j=> Eq.le ?_ ) ); exact congr_arg (fun U':Cn=> ‖coeff i U'‖) (congr_fun ( quote_shape_b h hp he ( P:=P ) ( u:=u ) ( f:=f ) hm ht ( x:=j.val ) j.property ) b ) -- eq
lemma honest (hk:IsCompact s)(hr:s⊆conf n)(hF:AllC V' u f)(ht:Detected V P)(b: Toon G d)(i:ℕ): TendstoUniformlyOn ( fun t x=> coeff i ( QuoteShape H V' P u t x b )) ( fun x=> coeff i ( f x ( flash b ) ) ) atTop s:= by
    obtain H0:= post_quote h hp he hk hr ht ( hF.2.2 s hk hr d ( i+1 ) ) b i ( Nat.lt_succ_self i ); simp_rw [ map_sub ] at H0; have he: ( heft ( flash b ):ℝ ) ≤ (d:ℝ):= (by exact_mod_cast size_le b); obtain H':= Rain.lapse H0 ( by linarith ); rw [ Metric.tendstoUniformly_iff ] at H'; refine Metric.tendstoUniformlyOn_iff.mpr (fun ε hε=> ( H' ε hε ).mono ( fun t h x hx=>?_ ) ); specialize h (⟨ x,hx ⟩: ↥s); rw [ Pi.zero_apply,dist_zero_left ] at h; rw [dist_comm,dist_eq_norm ]; exact h
end YM.FVA2.O.Read
