import YM.QuadraticLocal.Rebirth.Trend
import YM.QuadraticLocal.Union.Commit
/-!
# Coupling sold on exactly the comparison epoch

 Tilt ∆ is an error *after* solving the field-independent kinetic location. Require
 that solution along the actual step carrying all the marks as in `WheelP` and `Oak`. This
 file proves it's possible to register the clearance for the enhanced birth of the marks from
 just that very Schedule. All authority for chart estimates post L but before Run.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Rebirth
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open PositionX.Jet Extra.Iteration
open AllOrder AllOrder.Catch AllOrder.Catch.Clock AllOrder.Wheel AllOrder.Transit
open AllOrder.Rosary.Repair PostP AllOrder.Wheel.Ride
open Coat Next.Scheduling Next.Scheduling.Clock AllOrder.Floe
open Step Step.PlanV
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G: Gauge} {X: Metals G}
variable (D:RG.Supply.Rolls X.p)(R: Roots (G:=G) X.p.profile X.K X.p.kernel)
variable (x y:ℕ)(hx:4≤ x) {k:ℕ}
set_option quotPrecheck false
local notation "ρ"=> (Burn.horizon k)
local notation "L"=> D.L x
local notation "H"=> (fun t=> betaF G t (D.L x))
local notation "B"=> X.p.profile y
local notation "F'" => ( fun ξ:ℝ=> Pair.Note D R x y hx (q:=k) ξ )
local notation "N" => ρ+2
local notation "E"=> Aux.fare G (D.L x)
local notation "Z₁"=> (E).stage F'
variable (F: Income D R x y hx (Burn.horizon k))
local notation "T"=> Pair.Note

structure Predicted (s:ℝ) where
    news : Pair.Note D R x y hx (q:=k) s
    post : ℝ
    band: post ∈ Set.Icc (s/2) (2*s)
    pace : Pressure.temp s ^ 2 * |post-Wheel.now (F.issue news.token) (Burn.horizon k+2) news.beta| ≤ PostP.θ2 G B s k

namespace Predicted
local notation "Ξ"=> (Predicted D R x y hx F)
local notation "K"=> (Σ s, Predicted D R x y hx F s)
local notation "Z"=> (Aux.fare G (D.L x)).stage (Ξ)
local notation "u"=> (fun i:K=> Predicted.post i.2)
local notation "Y"=> (fun i:K=> i.1)
local notation "Φ"=> (fun i:K=> F.issue i.2.news.token)
local notation "v"=> (fun i:K=> i.2.news.beta)
local notation "q"=> (fun i:K=> i.2.news)
lemma grade0 (i:K): (Φ i) 0=0:= (F.sustenance.due _).1
-- regulator proof doesn't need exists query. clocks may empty.
lemma rotates : AllOrder.Wheel.Hall (Z) (Burn.horizon k+2) (v) (Φ):=by
    let g:( Σ s, Predicted D R x y hx F s )→ Σ s, F' s:= fun i=> ⟨i.1,(i.2.news)⟩; have hx': (Z₁).Fare (U:=Z) g:= ⟨tendsto_comap_iff.mpr ((E).liftF (Y)).tends, Eventually.of_forall fun _=> rfl⟩; have ht:= Pair.lesson D R x y hx F; exact ⟨ht.tune.orbit g Z hx',fun j hj=>(ht.fee j hj).pays g hx', hx'.tends.eventually ht.mild⟩
local notation "r"=> (Z).rail
lemma begins : ∀ᶠ i in r,0< u i:= ((E).liftF Y).tends.eventually (eventually_gt_atTop (0:ℝ))|>.mono fun i hi=> (half_pos hi).trans_le (i.2.band).1

/-- `βerror ≤ x θ₂`, x **coarse reference**. This real cost uses the exact thermal threshold. -/
lemma currents (i:K)(he:0 < i.1): |u i-now (Φ i) (N) (v i)| ≤ PostP.θ2 G (X.p.profile y) i.1 k * i.1:= by
   let x':= i.1; let A:= Pressure.temp x'
   let b:= Coat.gStep x'; have hm:= i.2.pace; let c:= PostP.θ2 G (X.p.profile y) i.1 k; let u₁:= |u i-now (Φ i) (Burn.horizon k+2) (v i)|; have hr:0≤u₁:= abs_nonneg _; change A^2*u₁ ≤ c at hm; have hz:= Fare.gS x' he; change u₁≤ c*x'; have hw:b≤ A:= le_mul_of_one_le_right hz.1.le (Real.one_le_exp (sq_nonneg _))
   rw (occs:=.pos [1]) [ ← one_mul u₁, ← hz.2 ]; calc
     _ = b^2*u₁*x':= by change b^2*x'*u₁=_; ring
     _ ≤ _:= mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz.1.le hw _) hr).trans hm) he.le
-- maybe `one_div` etc.
lemma strength : (Z).Meter (fun i:( Σ s, Predicted D R x y hx F s )=> Predicted.post i.2 - now (F.issue i.2.news.token) (Burn.horizon k+2) i.2.news.beta) ( graded ((Burn.horizon k+1)+1)+1 ):=by
   let c:= Time.credit G (X.p.profile y); have hc:0≤c:= (Time.credit_pos G (X.p.profile y)).le; let p:= Burn.credit k+1; have hz:p< 0:=by unfold p; linarith only [PostP.earns k]
   let A:= G.slopeConstant*Real.log ((D.L x).val:ℝ); let D' := (Z);
   have hf: p ≤ graded ((Burn.horizon k + 1)+1) + 1:= by unfold p graded; rw [Burn.sale_eq]; push_cast; linarith
   let v' := (2:ℝ)⁻¹ ^ p;
   refine ((Catch.Clock.Meter.weak (S:=D') (( Catch.Clock.Meter.pale (Z) p ).lscale (2*c*v')) hf).smaller ?_);
   filter_upwards [ (Z).positive, ((E).liftF Y).tends.eventually (eventually_gt_atTop (0:ℝ)), ((E).liftF (Y)).tends.eventually (eventually_ge_atTop A)] with i hi ht hv
   let g':= (Z).cost i; have hx' : g'=i.1+A:= rfl; let b₁:= g'^p;
   change 0<g' at hi; change 0 < i.1 at ht; change A ≤ i.1 at hv
   refine (currents D R x y hx F i ht).trans (le_trans ?_ (le_abs_self _)); change _ ≤ 2*c*v'* g'^p; rw [show PostP.θ2 G (X.p.profile y) i.1 k*i.1=2*c*(i.1)^p by unfold PostP.θ2 PostP.θ1 Burn.young p c; rw [Real.rpow_add ht,Real.rpow_one]; ring]; rw [mul_assoc (2*c)]; apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2*c); unfold v'; rw [←Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2⁻¹) hi.le]; exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hz.le

lemma census (s:ℤ)(n e₀:ℕ)(hn:n≤Burn.horizon k+1)(he:e₀ ≤ n): (Z).Meter (fun i:K=> gStep (v i) ^ e₀ *Balance.balance (Φ i) (grade0 D R x y hx F i) (Burn.horizon k+2) s ( gStep (v i)) (gStep (u i)) (n-e₀)) (graded (n+1)):=by
   let H':= Predicted.rotates D R x y hx F; let V:=Trend.delivery (Q:=Φ) (Z) s (grade0 D R x y hx F) (k:= Burn.horizon k+1) (by omega) H' (begins D R x y hx F) (Predicted.strength D R x y hx F) (n-e₀) (by omega); apply ((H'.tune.stepI.pow e₀).mul V).weak; unfold graded; push_cast; rw [Nat.cast_sub he]; linarith
end Predicted
end YM.QuadraticLocal.Rebirth
