import YM.MS.Dial.Wake
/-!
# Negative time domination in continuum frame.Purpose: separated continuity; also grants actual PT regulator statements on sequences of profile samples converging to fixed physical positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Vane -- alias
open scoped Topology ContDiff
variable {I W E:Type} {G:Gauge} {v t:ℝ}{a b:ℤ}{l:Filter I} {r:ℕ}
set_option quotPrecheck false
local notation "Υ" => east ( frameF I v ) false
local notation "Ω"=> ( Υ ).price
open Wire Belt
variable {F H:Glade G I}{m:I→QP}
variable {p:I}
local notation "R"=> frameF I v
local notation "D"=> constantP G I (PlanetD G)
variable [LinearOrder W] {B:Deck G}{M:Booked B}{b:MS_Data G M}(X:W→Label B){x:Position W I}{K:Rake.Dance G I W}
local notation "m0"=> (fun (_:I)=>planeF)
local notation "Sκ"=> approach (frameF I v) b
variable (h: Mesh (frameF I v) x)(ht:DOrd M (frameF I v) b X x K) {s:Finset W}{n:ℕ}
variable [l.IsCountablyGenerated] (hv:∀ i:W,tend l p ( x i ))
include h ht hv
lemma pale_P (s:Finset W)(n:ℕ)(t:ℝ)(w: Legs (Lane4 G)): tend l p (fun i=> K s n i t w):= by
   let Y(w:W)(i:I):= exp (-t) • x w i; let v':= v+t; let Q:=frameF I v'; have hx : Mesh Q Y:= by
       intro i j hi; have hζ(k:I): ( Y i - Y j ) k= exp (-t) • (x i-x j) k:= by simp only [Y,Pi.sub_apply,smul_sub]
       obtain ⟨⟨ C,hC,hK⟩,A,hA,hE⟩:= h i j hi; have he(k:I): Q.roots k= (R).roots k:= rfl; refine ⟨ ⟨ exp (-t)*C,by positivity,fun k=>?_⟩, ⟨ exp (-t)*A,by positivity,fun k=>?_⟩⟩; all_goals rw [hζ,norm_smul_of_nonneg (exp_pos _|>.le),he,mul_assoc]; gcongr; first|exact hK k|exact hE k
   obtain ⟨ V,hL⟩:= formal ( builder b hx X ); let J: I→ℝ:=fun _=>t; have hm := shifter b ( σ:=J ) ( P:=R ) ( fun i=> show Q.η i= _ from rfl ) hL; have hr : Port.moved J Y=x:= funext fun i=> funext fun j=> by unfold Port.moved Y J; rw [Real.exp_neg, smul_inv_smul₀ (exp_pos _|>.ne')];
   rw [hr] at hm; rw [perfect ht hm]; change tend _ _ (fun i=>Port.τ _ t * V s n i ( t-t ) ( Alps.sr t w )); rw [sub_self]; exact ( Wake X hx hL ( fun w=> ( hv w ).const_smul ( exp (-t) ) ) s n (0:ℝ) le_rfl ( Alps.sr t w ) ).const_mul _ -- type p order const_smul
-- moving ∞ uniform implies local cinch. 
omit hv h ht
lemma ultimate (η:ℝ)(hp: Verdict (frameF I η) r 0 F) (h: ∀ t:ℝ,tend l p (fun i=> F i t [] )) : tend l p (Vane.blade F):= by
    let P:= frameF I η; obtain ⟨ C,hC,k,hk⟩:= hp.2.1; have hb:= norm_of_nonneg (hC.le); obtain ⟨A,hA,hB⟩:= capped High.p_gain k; let r':ℝ := C*(1+|η|)^k; have hr : 0≤ r':= by unfold r'; positivity
    let B(t:ℝ):= r'*A*exp ( -(High.eps_gain/2)*t ); have ht (t:ℝ)(hp:0≤t)(x:I): dist (F x t []) (Vane.blade F x ) ≤ B t:= by
        rw [ dist_comm, dist_eq_norm ]; let T:Vane.Vista P:= ⟨ x,t, hp ⟩; obtain h:= hk T; apply h.trans; change C*((1+|η|)*(1+|t|))^k*( exp (((-(r:ℝ))-0)*0)* exp (-High.eps_gain*(t-0)))≤_; rw [abs_of_nonneg hp, mul_zero,exp_zero,one_mul,sub_zero, mul_pow ]; exact le_trans ( b:= r'*( (1+t)^k*exp (-High.eps_gain*t))) ( le_of_eq (by unfold r'; ring) ) ((mul_le_mul_of_nonneg_left (hB t hp) hr).trans_eq (by unfold B; ring))
    have hV:Tendsto B atTop (𝓝 0):= by simpa only [mul_zero] using! (tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (show -(High.eps_gain/2)<0 from by unfold High.eps_gain; norm_num)).mpr tendsto_id)).const_mul ( r'*A )
    apply Metric.tendsto_nhds.mpr; intro ε hε; obtain ⟨t,hT,ht'⟩ := (( hV.eventually ( Iio_mem_nhds ( show 0<ε/4 from by linarith ) ) ).and ( eventually_ge_atTop 0 ) ).exists; replace hT:B t<ε/4:=hT; filter_upwards [Metric.tendsto_nhds.mp (h t) (ε/2) (by positivity)] with i hi; apply lt_of_le_of_lt ( dist_triangle4 _ ( F i t [] ) ( F p t [] ) _ ); replace hi : dist ( F i t [] ) ( F p t [] )<ε/2:= hi; rw [ dist_comm (blade F i) ]; linarith [ ht t ht' i, ht t ht' p ]
include h ht hv
lemma owed {g:ℕ}(hs:Verdict R g 0 ( K s n )): tend l p ( Vane.blade ( K s n ) ):= ultimate v hs (fun t=> pale_P X h ht hv s n t [] )
end YM.MS.Dial
