import YM.FVA2.Smooth.Travel
/-!
# Smoothness of the scalar IR readings on the chart

Transfer the derivative recursion to this limit (pointwise at separated
positions). Only dealing with formal coefficients. No estimates on the
actual cutoff Wilson prediction in this file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Smooth.Cruise
open Set Function Filter Finset Metric MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake
open MS.Breeze MS.Book MS.Book.Convolve MS.Plane.Flux MS.High MS.Rake.Geo MS.Vane MS.Vista MS.Motif MS.Plane.Wire
open MS.Tone.Frame MS.City MS.Osc MS.Osc.Snap Belt
open MS.Land MS.Local.Physical MS.Dial MS.Port
open Lifetime Slots
open Complex (I)
open scoped Topology ContDiff BigOperators Interval
variable {W I : Type}{G:Gauge}{P Q:Geo I}{b:Deck G}{M:Booked b}
variable {k:ℝ}
variable [LinearOrder W][Fintype W]
open MS.Tide
open MS.Momentum
variable (S:MS_Data G M) (u:W→Rake.Label b)
-- compute on Board specialized Draw W.
local notation "Π"=> Draw W
local notation "μ₀"=> (fun (_:Draw W)=>planeF)
local notation "Δ"=> Rake.Geo.constantP G (Draw W) (PlanetD G)
local notation "Ψ"=> (field (p:=Landau.parity ( A:=Axis ) (C:=G.ColorIndex) ) (P:=QP))
variable {v r t:ℝ} {s: Steps W}
local notation "R"=> frameF (Draw W) v
local notation "Ω"=> approach R S
variable {x: Position W (Draw W)} {T T' U:Finset W} {ρ:Steps W} {J: Set (Draw W)} {q: Draw W}
variable {V:Steps W→Dance G (Draw W) W} {w:Legs (Lane4 G)} {A:Type}
open MeasureTheory
variable {E β α : Type*}{l:Filter α}{m:ℕ}
omit [LinearOrder W][Fintype W] in
lemma uniform_cycle [NormedAddCommGroup E] (k:Finset I){f:I→α→β→E}{g:I→β→E}(h:∀ i∈k,TendstoUniformly (f i) (g i) l): TendstoUniformly (fun i p=>∑ j∈k,f j i p ) (fun p=> ∑ j∈k,g j p ) l:= by
    classical
    induction k using Finset.induction_on with| empty=> simpa only [Finset.sum_empty] using! (tendsto_const_nhds ( x:= (0:E) )).tendstoUniformly_const ( p:=l ) ( α:=β ) | @insert i k he hi=> simp_rw [Finset.sum_insert he]; exact TendstoUniformly.add ( h i (by simp) ) (hi (fun j hj=> h j (by simp [hj]))) -- filters arg names
-- uniform exponential blade on any frame constant scale, also marks derivative lists.P. proof from Dial.ultimate.
variable {F:Glade G I}{η:ℝ}
omit [LinearOrder W][Fintype W] in
lemma speeding (hp:Verdict (frameF I η) m 0 F) : ∃ M:ℝ,0<M∧∀ x t,0≤t→ ‖F x t []-blade F x‖≤ M*exp ( -( High.eps_gain /2 )*t ):= by
    let P:= frameF I η; obtain ⟨ C,hC,k,hk⟩:= hp.2.1; obtain ⟨B,hB,hA⟩:= capped High.p_gain k; let r':ℝ := C*(1+|η|)^k; have hr : 0< r':= by unfold r'; positivity
    refine ⟨r'*B,by positivity,fun x t hp=>?_⟩; let T:Vane.Vista P:= ⟨ x,t, hp ⟩; obtain h:= hk T; rw [ norm_sub_rev ]; apply h.trans; change C*((1+|η|)*(1+|t|))^k*( exp (((-(m:ℝ))-0)*0)* exp (-High.eps_gain*(t-0)))≤_; rw [abs_of_nonneg hp, mul_zero,exp_zero,one_mul,sub_zero,mul_pow]; exact le_trans ( b:= r'*( (1+t)^k*exp (-High.eps_gain*t))) ( le_of_eq (by unfold r'; ring) ) ((mul_le_mul_of_nonneg_left (hA t hp) hr.le).trans_eq (by ring))
omit [LinearOrder W][Fintype W] in
lemma zoom (hp:Verdict (frameF I η) m 0 F) : TendstoUniformly (fun u i=> F i u [] ) ( blade F ) atTop:= by
    obtain ⟨C,hC,h⟩:= speeding hp; let M (t:ℝ):= C*exp ( -(High.eps_gain/2)*t );
    have ht:Tendsto M atTop (𝓝 0):= by simpa only [mul_zero] using! (tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (show -(High.eps_gain/2)<0 from by unfold High.eps_gain; norm_num)).mpr tendsto_id)).const_mul C -- conflict C(t:
    rw [ Metric.tendstoUniformly_iff ]; intro ε hε; filter_upwards [ ( ht.eventually ( Iio_mem_nhds hε ) ), eventually_ge_atTop 0 ] with t ht he x; exact lt_of_le_of_lt ( show dist (blade F x) (F x t [])≤_ from by rw [dist_comm, dist_eq_norm]; exact h _ _ he ) ht
lemma freight (ho:IsOpen J){U:Steps W→Draw W→ℂ}(hp:∀ (s:Steps W)(q:Draw W),q∈ J→ Rides r T s U q)(p:Steps W): ContDiffOn ℝ ∞ ( U p ) J := by
    have hd (s:Steps W): DifferentiableOn ℝ ( U s ) J:= fun q h=> (hp s q h).differentiableAt.differentiableWithinAt
    refine contDiffOn_infty.mpr ?_; intro n; induction n generalizing p with
    | zero=> exact contDiffOn_zero.mpr (hd p|>.continuousOn)
    | succ n ih=>
       rw [ Nat.cast_add_one, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (ho.uniqueDiffOn) ]; refine ⟨ by simp, (fun x=> Abroad.jet r T p ( fun u=> U u x ) ), ?_,fun x hx=> (hp p x hx).hasFDerivWithinAt ⟩; unfold Abroad.jet; refine ContDiffOn.sum ( fun i hi=>?_ ); exact ( Abroad.spout r i ).contDiff.comp_contDiffOn ( ih ( hop p i ) )
variable (ho:IsOpen J)(hu:∀ i, EqOn ( x i ) (fun q=> r • q i) J)(hx:Mesh (frameF (Draw W) v) x)
variable (ht:∀ s':Steps W,charted (frameF (Draw W) v) S u s' x ( V s' ))
include hx ht
-- all t over same support window, uniform exponential convergence. easy
omit [Fintype W] in
lemma uniform (s:Steps W)(T:Finset W)(n:ℕ): TendstoUniformly (fun t x'=> aboard x ( V s ) T n x' t []) (blade ( V s T n )) atTop:= by
    simp_rw [ aboard,perch,cove, show net ([]:Legs (Lane4 G))=0 from rfl, right0,one_mul ]; obtain h|h:=T.eq_empty_or_nonempty; simp_rw [ h,( ht s ).1,Pi.zero_apply, show blade (0:Glade G (Draw W))=0 from funext (fun i=> (Fleet.allow_zero i).2 ) ]; exact tendsto_const_nhds.tendstoUniformly_const; exact zoom ( verdict S u s x hx (ht s) _ h n )
include ho hu
lemma stars (T:Finset W) (n:ℕ) (p:Steps W)(hq:q∈J): Rides r T p (fun p=> blade ( V p T n )) q:= by
    let f(s:Steps W)(t:ℝ)(x':Draw W):= aboard x ( V s ) T n x' t []; let g(s:Steps W):= blade ( V s T n );
    have hU(s:Steps W): TendstoUniformly ( f s ) ( g s ) atTop:= Cruise.uniform S u hx ht s T n;
    let Z (t:ℝ)(q:Draw W):= Abroad.jet r T p (fun v=> f v t q); have he : TendstoUniformly Z (fun q=> Abroad.jet r T p (fun v=>g v q)) atTop:= uniform_cycle ( I:=W×Axis ) (patch T) (fun i hi=> ( Abroad.spout r i ).uniformContinuous.comp_tendstoUniformly (hU ( hop p i ))) -- mismatch implicit f under fun
    exact hasFDerivAt_of_tendstoUniformlyOn ho he.tendstoUniformlyOn ( hf:=fun t y hy=> visa S u ho hu hx ht t T n p ( w:=[] ) hy ) ( hfg:=fun x _ => (hU p|>.tendsto_at x) ) hq
lemma smoothness (T:Finset W)(n:ℕ)(s:Steps W): ContDiffOn ℝ ∞ (blade (V s T n)) J:= freight (U:=fun u=> blade ( V u T n ) ) ho (fun i _=> stars S u ho hu hx ht T n i ) s
lemma smooth_finite (T:Finset W)(n:ℕ)(w:Legs (Lane4 G))(t:ℝ)(s:Steps W): ContDiffOn ℝ ∞ (fun p=> aboard x ( V s ) T n p t w) J:= freight (U:=fun i p=> aboard x (V i) T n p t w ) ho (fun i _=> visa S u ho hu hx ht t T n i ) s
end YM.FVA2.Smooth.Cruise
