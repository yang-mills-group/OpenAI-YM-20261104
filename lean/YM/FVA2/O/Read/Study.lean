import YM.FVA2.O.Project.Shine
/-!
# Smearing isolated test contributions

Enough to have continuity on actual supports of tests. Includes moving-time
power-log bounds for a fixed `Test`.
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
variable {G:Gauge}{ I J: Type }{m n d k:ℕ}{a b t:ℝ}{ x:Points n }{F:Points n→ Cn}
variable (p:Test n) {f g: Points n→ℂ}
abbrev CoverP (p: Test n): Set ( Points n ):= tsupport p
abbrev smearing (p:Test n)(F:Points n→Cn) : Cn:= PowerSeries.mk (fun i=> Test.applyTo p (fun x=> PowerSeries.coeff i ( F x )) )
lemma outside (h:x ∉ CoverP p): p x=0:= image_eq_zero_of_notMem_tsupport h
lemma treasury (f:Points n→ ℂ): (CoverP p).indicator (fun x=> p x*f x)=(fun x=>p x*f x):= by
    funext x; by_cases hp:x∈CoverP p; · exact indicator_of_mem hp _
    rw [indicator_of_notMem hp, outside p hp,zero_mul]
lemma smear_F (h:ContinuousOn f ( CoverP p )) : Integrable ( fun x=> p x*f x ):= by
    rw [ ← treasury p ]; exact (integrable_indicator_iff (isClosed_tsupport _).measurableSet).mpr ( (p.continuous.continuousOn.mul h).integrableOn_compact p.hasCompactSupport )
abbrev draw (p:Test n)(F:Points n→Cn): Prop := ∀ i:ℕ, ContinuousOn (fun x=> coeff i ( F x )) ( CoverP p )
lemma smear_price (h:EqOn f g ( CoverP p )): p.applyTo f=p.applyTo g:= by
    unfold Test.applyTo; apply integral_congr_ae; filter_upwards with x; by_cases hp:x∈CoverP p; · rw [h hp];
    rw [outside p hp,zero_mul,zero_mul]
lemma smear_one (b:ℂ) : p.applyTo (fun x=> b*f x)=b*p.applyTo f:= by unfold Test.applyTo; simp_rw [mul_left_comm ( p _ ) b ]; rw [ integral_const_mul ] -- no integrability
lemma smear_sub (h:ContinuousOn f ( CoverP p ))(he:ContinuousOn g ( CoverP p )): p.applyTo (fun x=> f x-g x)=p.applyTo f-p.applyTo g:= by unfold Test.applyTo; simp only [mul_sub]; rw [ integral_sub ( smear_F p h ) ( smear_F p he ) ]
lemma smear_sum {f:I→ Points n→ ℂ}(s:Finset I)(h:∀ i∈s,ContinuousOn ( f i ) ( CoverP p )): p.applyTo (fun x=>∑ i∈s,f i x)=∑ i∈s,p.applyTo (f i):= by unfold Test.applyTo; simp only [Finset.mul_sum]; exact integral_finsetSum _ ( fun i hi=> smear_F p ( h i hi ) )
lemma draw_sum {A:I→Points n→ Cn}(s:Finset I)(h:∀ i∈s, draw p ( A i )): draw p ( fun x=> ∑ i∈s,A i x ):= sum_on A s h
lemma region (h:draw p F)(q:Cn): draw p ( fun x=> q* F x ):= stableV ( A₁:=fun (_:Points n)=> q ) ( fun _=>continuousOn_const ) h
lemma smearing_mul (h:draw p F)(q:Cn): smearing p (fun i=> q* F i)= q* smearing p F:= by
    ext i; rw [smearing,coeff_mk]; simp_rw [ coeffF,smearing,coeff_mk ]; rw [smear_sum]; · simp_rw [smear_one]
    exact fun j _=> ( h (i-j) ).const_mul _
lemma smearing_sum {f:I→ Points n→ Cn}(s:Finset I)(h:∀ i∈s,draw p ( f i )): smearing p ( fun x=>∑ i∈s, f i x )=∑ i∈s,smearing p (f i):= by
    ext i; simp_rw [ smearing,map_sum,coeff_mk ]; exact smear_sum p _ ( fun j hj=> h j hj i )
lemma smearing_sub {F F':Points n→ Cn}(h: draw p F)(he:draw p F'): smearing p ( fun x=> F x - F' x )= smearing p F - smearing p F':= by ext i; simp_rw [ smearing,map_sub,coeff_mk ]; exact smear_sub p ( h i ) ( he i )
-- $norm cost. Use fullness of volume on Points.L.Body
abbrev Value (t:Test n):ℝ:= ∫ x:Points n, ‖t x‖
lemma value_0 : 0≤ Value p:= integral_nonneg (fun _=> norm_nonneg _)
lemma value_le (h: ContinuousOn f (CoverP p))( he:∀ i∈CoverP p, ‖f i‖≤ b ): ‖p.applyTo f‖ ≤ Value p*b := by
    apply le_trans (norm_integral_le_integral_norm _); unfold Value; rw [← integral_mul_const]; -- types μ inference
    apply integral_mono ( ( smear_F p h ).norm ) (( p.continuous.integrable_of_hasCompactSupport p.hasCompactSupport ).norm.mul_const _ ); intro i; dsimp only; rw [ norm_mul ]; by_cases hx:i∈CoverP p; · exact mul_le_mul_of_nonneg_left ( he i hx ) ( norm_nonneg _ )
    rw [ outside p hx,norm_zero,zero_mul,zero_mul ]
variable {F:I→ℝ→ Points n→ Cn } -- name shadow
lemma cost_V {F:I→ℝ→ Points n→ℂ}(he:Rain a (fun (i:I× ↥( CoverP p )) t=> F i.1 t i.2.val))(h:∀ᶠ t:ℝ in atTop,∀ i:I,ContinuousOn ( F i t ) ( CoverP p )): Rain a ( fun i t=> p.applyTo ( F i t ) ):= by
    obtain ⟨C,hC,k,H⟩:= he; refine ⟨ Value p * C+1,(by nlinarith [value_0 p]),k,?_⟩; filter_upwards [ H,h,eventually_ge_atTop (0:ℝ) ] with t he h ht i; have hp:= post_at ( k:=k ) ( a:=a ) ht; exact ( value_le p ( h i ) ( fun j hj=> he ( i,⟨ j,hj ⟩ ) ) ).trans ( by rw [ add_mul, mul_assoc ]; nlinarith [value_0 p] )
lemma fee_W (h: ChargeP d a ( fun (i:I× ↥( CoverP p )) t=> F i.1 t i.2.val ))( hv:∀ i<d,∀ᶠ t:ℝ in atTop,∀ j:I, ContinuousOn ( fun x=> coeff i (F j t x) ) (CoverP p) ): ChargeP d a ( fun i t=> smearing p ( F i t ) ):= by
    intro i hi; unfold smearing; simp only [coeff_mk]; exact cost_V ( F:= fun j t x=> coeff i ( F j t x ) ) p ( h i hi ) ( hv i hi )
end YM.FVA2.O.Read
