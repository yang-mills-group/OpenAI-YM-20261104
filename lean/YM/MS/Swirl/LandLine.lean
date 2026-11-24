import YM.MS.Swirl.UnSeat
import YM.MS.SpaceOut.Saga
/-!
# Finite dimensional terminal supplies. Line in core Landau chart, for Vista terminal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl.Near
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice City Latch Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program
open Complex (I)
open scoped Topology ContDiff Interval
variable {G:Gauge}{A E:Type}[Fintype A][DecidableEq A]{p:Momentum A}(x y:Atom A)
-- no low cost. including projected inversion ghosts
/-- Terminal covariance, both orientations; λ^{-1} harmless at λ=0 by modulus convention.
Harmonics set to zero. -/
def Tail : YMflow A
 | (some i,false),(some j,false),p=> ((precision i j p/p.sq^2 :ℝ):ℂ)
 | (some i,true),(none,false),p=> I*((p i/p.sq:ℝ):ℂ)
 | (none,false),(some i,true),p=> I*((p i/p.sq:ℝ):ℂ)
 | _,_,_=>0
omit [DecidableEq A] in
lemma lown (p:Momentum A)(t:ℝ): low t p = (1+t^2*p.sq)*exp (-(t^2*p.sq)):= by simp only [low,coat,pow_zero, one_mul,scaling]
omit [DecidableEq A] in
lemma ohLow (p:Momentum A): low 0 p=1:= by rw [lown]; norm_num
omit [DecidableEq A] in
lemma lowers (hp:0<p.sq): Tendsto (fun t=> low t p) atTop (𝓝 0):= by
    let z(t:ℝ):= t^2*p.sq; have he : Tendsto z atTop atTop:= ?_; swap; · exact Filter.Tendsto.atTop_mul_const hp (tendsto_pow_atTop ( show 2≠0 from (by omega) )) -- signatures
    obtain hv:= tendsto_exp_neg_atTop_nhds_zero.comp he; obtain ht:= (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp he; simp_rw [pow_one] at ht; simp_rw [ lown, add_mul, one_mul ]; exact Eq.mp (by rw [add_zero]; rfl : ((Tendsto _ atTop (𝓝 (0+0:ℝ))))=_ ) ( hv.add ht ) -- metavars
abbrev Fuel (t:ℝ): YMflow A:= fun i j p=> (1-(low t p:ℂ))*Tail i j p/2
lemma zeroShift (hp:p.sq=0): Tail x y p=0:= by rcases x with ⟨_|x,_|_⟩ <;> rcases y with ⟨_|y,_|_⟩ <;> simp [ Tail,hp ]
omit [DecidableEq A] in
lemma NoWave (p:Momentum A)(h:p.sq=0): p=0:= by apply norm_eq_zero.mp; nlinarith [sup_square p,norm_nonneg p]
lemma bruC (hp:p.sq=0)(t:ℝ): L0 t x y p=0:= by rw [NoWave p hp]; rcases x with ⟨_|x,_|_⟩ <;> rcases y with ⟨_|y,_|_⟩ <;> simp [L0,precision,delta,Momentum.sq, ite_self]
lemma swing {t:ℝ}: HasDerivAt (fun t=>Fuel t x y p) (L0 t x y p) t:= by
    unfold Fuel; by_cases h:p.sq=0; · rw [zeroShift x y h,bruC x y h]; simp; exact hasDerivAt_const ..
    have hC:(p.sq:ℂ)≠0:= by exact_mod_cast h
    let P(t:ℝ):=(low t p:ℂ); obtain hp : HasDerivAt (fun u=>P u) ((-2*( City.brush t p )*p.sq^2:ℝ):ℂ) t:= by obtain hj:= Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt _ ( xH t p ); exact hj
    have he:= ((hp.const_sub 1).mul_const ( Tail x y p )).div_const 2; convert! he using 1; rcases x with ⟨_|x,_|_⟩ <;> rcases y with ⟨_|y,_|_⟩ <;> simp only [ L0,Tail,mul_zero,zero_div ] <;> push_cast <;> field_simp [hC] <;> ring -- Lean casts.
lemma swingL (p:Momentum A): Tendsto (fun t=>Fuel t x y p) atTop (𝓝 ( Tail x y p/2 )):= by
    unfold Fuel; by_cases hp:p.sq=0; · rw [zeroShift x y hp]; simp
    obtain hx : Tendsto (fun t=> (low t p:ℂ)) atTop (𝓝 0):= by convert Complex.ofRealCLM.continuous.continuousAt.tendsto.comp (lowers (p:=p) ( lt_of_le_of_ne (le_trans (sq_nonneg _) (sup_square p)) (Ne.symm hp) )) using 1; rfl; rw [map_zero] -- likely simp
    convert! ( ( (tendsto_const_nhds.sub hx).mul_const ( Tail x y p ) ).div_const (2:ℂ) ) using 1; simp -- no goals
-- shape terminal proportional to r→t Cpu. since brush 1 never zero. leave pref.
abbrev bank (p: Momentum A): ℂ:= (( Real.exp p.sq/(2*p.sq^2):ℝ):ℂ)
lemma uni (p:Momentum A): Tail x y p/2 = bank p * L0 1 x y p:= by
    by_cases h:p.sq=0; rw [zeroShift x y h,bruC x y h,mul_zero,zero_div]; have hc : (p.sq:ℂ)≠0:= by exact_mod_cast h
    have he := Real.exp_ne_zero p.sq
    unfold bank; rcases x with ⟨_|x,_|_⟩ <;> rcases y with ⟨_|y,_|_⟩ <;> simp only [ L0,Tail, City.brush, one_pow,one_mul, Real.exp_neg,mul_zero, zero_div] <;> first| rfl| (push_cast; field_simp [hc]) -- name
-- coloring. plan. d positions
abbrev Bass (G:Gauge): Latch.Edge G:= fun i j p=> flag i p*flag j (-p)*Landau.choir Tail wave i j p
abbrev Forest (G:Gauge)(t:ℝ): Latch.Edge G:= dope (Landau.choir ( Fuel t ) wave)
/-- based mode half terminal -/
abbrev FinalK (G:Gauge): Latch.Edge G:= fun i j p=> Bass G i j p/2
variable (a d:BH G) (p':QP)
lemma clave (t:ℝ): HasDerivAt (fun t=>Forest G t a d p') (LaceL G t a d p') t:= by
    unfold Forest dope LaceL Cpu LegsK; simp only [dope,Landau.choir]; split; exact ( swing a.1 d.1 ).const_mul _; simp; exact hasDerivAt_const ..
lemma essence : Tendsto (fun t=>Forest G t a d p') atTop (𝓝 ( FinalK G a d p' )):= by unfold Forest FinalK Bass dope; simp_rw [Landau.choir]; split; rw [ mul_div_assoc ]; exact ( swingL a.1 d.1 ( wave p' ) ).const_mul _; simp
lemma and_here : FinalK G a d p' = bank ( wave p' )* LaceL G 1 a d p':= by unfold FinalK Bass LaceL Cpu LegsK; simp_rw [ dope_p, Landau.choir, mul_div_assoc ]; split; rw [ uni a.1 d.1 ]; ring; simp
-- future $W respect
end YM.MS.Swirl.Near
