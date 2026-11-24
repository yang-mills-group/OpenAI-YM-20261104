import YM.FVA2.Lambda.Glow
/-!
# Center a moment formula

 The useful reusable computation of both τ jets. Define mixed polynomial and prove both symmetric; no derivative of widths. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Lathe
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open Canvas (quad high line4 triple upperquad trigger)
open MS.City MS.Plane.Flux
open Area Shells Pages
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}
local notation "g"=>triple G
local notation "Z"=>Momentum.sq (A:=Axis)
variable (q:QP)(x a h y z:ℝ)(i:G.ColorIndex)
def prism (a q r s:ℝ):ℝ:= 10*r^2*s^2 * (2*a^2*q^2 -a) +20*q*r^2*s*(-2*a*q)+ (4*q^2*r^2-8*q^2*s+6*r^2*s+8*s^2)
def jewel (q:QP)(a:ℝ):= prism a (q 0) (q 1) (Z q)
def bud (q:QP)(x:ℝ):= x*((Z q-(q 0)^2)*( 2*Z q+2*x*(q 0)+x^2 ))
def pulse (q:QP):= ( Z q-(q 0)^2 )*(2* Z q)
abbrev Absorb (f:QP→ℝ→ℝ)(q:QP): ℝ := ∫ a, γ a q*a/2*f q a ∂unitμ
def simplex (a b c d e:ℝ)(x:ℝ):= a+b*x+c*x^2+d*x^3+e*x^4
lemma cards (a b c d e:ℝ): Lathe.read 1 (simplex a b c d e)=b ∧ Lathe.read 2 (simplex a b c d e)=c:= by
    let v(t:ℝ):= b+c*(2*t)+d*(3*t^2)+e*(4*t^3)
    have hd (x:ℝ): HasDerivAt (simplex a b c d e) (v x) x:= by
        let h:= (hasDerivAt_id' x); convert! ( ( ( ( h.const_mul b ).const_add a ).fun_add (( h.pow 2 ).const_mul c)|>.fun_add ((h.pow 3).const_mul d) )|>.fun_add ((h.pow 4).const_mul e)) using 1; unfold v; push_cast; ring
    have he (x:ℝ): HasDerivAt v (2*c+6*d*x+12*e*x^2) x:= by let h:= hasDerivAt_id' x; convert! (((( h.const_mul (2:ℝ) |>.const_mul c ).const_add b ).fun_add (( ( h.pow 2).const_mul (3:ℝ)).const_mul d ) )|>.fun_add ((( h.pow 3).const_mul (4:ℝ)).const_mul e)) using 1; push_cast; ring
    refine ⟨ ?_,?_⟩; rw [Lathe.read,iteratedDeriv_one, (hd 0).deriv ]; simp [v]
    rw [Lathe.read,iteratedDeriv_succ, iteratedDeriv_one,show deriv (simplex a b c d e)=v from funext fun x=>(hd x).deriv,(he 0).deriv ]; norm_num; ring
lemma part_cont : ContDiff ℝ ∞ (partQ q):= by unfold partQ marble; fun_prop
lemma bud_cont : ContDiff ℝ ∞ (bud q):= by unfold bud; fun_prop
lemma read_P : Lathe.read 2 (existW ( partQ q ) q)=Absorb jewel q := by
    let v:=(4*(q 0)^2*(q 1)^2-8*(q 0)^2*Z q+6*(q 1)^2*Z q+8*(Z q)^2)
    have h₁: Lathe.read 1 ( partQ q )=20*(q 0)*(q 1)^2*Z q:= ( cards _ _ _ _ _ ).1; have h₂: Lathe.read 2 ( partQ q )=v:= ( cards _ _ _ _ _ ).2
    rw [ redjet q _ _ (part_cont q) ]; unfold Absorb; apply integral_congr_ae; filter_upwards with a; rw [Lathe.read_mul 2 _ _ ( gem_Ω .. ) (part_cont q) ]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num only; rw [ h₁,h₂, read₀, read₀, gem_1,gem_2,gem_l ]; simp only [jewel,prism,partQ,marble,mul_zero,add_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,v]; ring
lemma read_Q : Lathe.read 1 (existW ( bud q ) q)=Absorb (fun q _=> pulse q) q:= by
    have ht: Lathe.read 1 (bud q)=pulse q:= by rw [ (show bud q=simplex 0 ( Lathe.pulse q ) (( Z q-(q 0)^2 )*(2*q 0)) ( Z q-(q 0)^2 ) 0 from funext (fun i=> by unfold bud Lathe.pulse simplex; ring)), (cards ..).1 ];
    rw [ redjet q _ _ (bud_cont q) ]; unfold Absorb; apply integral_congr_ae; filter_upwards with a; rw [Lathe.read_mul 1 _ _ ( gem_Ω .. ) (bud_cont q) ]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num only; rw [ ht, read₀,read₀, gem_l, show bud q 0=0 from ( by simp [bud] ) ]; ring
lemma gem_neg : Absorb jewel (-q)=Absorb jewel q:= by unfold Absorb; apply integral_congr_ae; filter_upwards with a; simp only [γ,sq_neg,jewel,Pi.neg_apply]; unfold prism; ring
lemma pulse_neg : Absorb (fun q _=> Lathe.pulse q) (-q)=Absorb (fun q _=> Lathe.pulse q) q:= by unfold Absorb; apply integral_congr_ae; filter_upwards with a; simp [ Lathe.pulse ] -- γ
end YM.FVA2.Lambda.Lathe
