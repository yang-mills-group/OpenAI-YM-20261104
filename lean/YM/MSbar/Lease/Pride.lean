import YM.MSbar.Lease.Rents
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Cottage
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup Bulk
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {c f:Side} {S:StepData c f} {U:Config G f}{R: Rep G f}{R':Rep G c}{σ C T K B a b v r δ w β u:ℝ}{M k m:ℕ}
open ConnectedActivityE6 Finset RG.PathData Tree Push.Uniform Pressure SectorNext.Vacuum AnalyticBridge.VerifiedReset Next.Scheduling Precision Stock Metric Posture
variable (P:Patch)(D:KernelChoices)(p:Palisade)(J:Voice G) (L L' : Stage) (h : Clear G J)
set_option quotPrecheck false
local notation "Ξ"=> tip G P.L
variable (G) (f:ℝ→ℕ)(hF: Beam G P.L (fun x=>(f x:ℝ)))
def boldPrice (L:Stage)(x t:ℝ)(p:ℕ):=
    let R:=radiusB x; let z:=L.supportExponent; let T:=temp x
    craft L.paths L.width t p (voyageB x)+(p*8:ℝ)*( lbt x*T^2*(2*Real.exp (L.width*8)*(81*meter L.width))+ability x*(2*Real.exp (z*10))*((2*(4*R+2)+1:ℝ)^4*meter z))
include hF
lemma cloth : Beam G P.L (fun x=> boldPrice L (Ξ x) (2*Ξ x) (f x)):=by
   have hv:= (lux G P L f hF) (-1); let c:= -(1:ℝ); let g:=tip G P.L; have ht:Rate G P.L 0 (lbt ∘ g):=Rate.monitor.mul_left _
   have he:Rate G P.L (-(11/10)) (ability ∘ g):= ability_rate G P.L
   have hr: Rate G P.L (-(1/2)) (temp∘g):= Rate.flame
   let d(x:ℝ):= (radiusB (g x):ℝ)
   have hx :Beam G P.L (fun x=>(2*(4*d x+2)+1)^(4:ℕ)*meter L.supportExponent):= ((((Beam.coin 2).mul (((Beam.coin 4).mul (Beam.shore P.L G)).add (Beam.coin 2))).add (Beam.coin 1)).power 4).mul (Beam.coin _)
   unfold boldPrice
   exact (Beam.lax hv (by norm_num)).add ((hF.mul (Beam.coin (8:ℝ))).mul ((Beam.lax ((ht.mul (hr.pow 2)).mul_right _) (by norm_num)).add (Beam.lax ((he.mul_right (2*Real.exp (L.supportExponent*10))).mul hx.tick) (by norm_num))))
omit hF in
lemma squareB :Beam G P.L (fun x=> Ξ x*skies (Ξ x)*skies (Ξ x)) :=by
    let k:= tip G P.L; apply ((Beam.logfine G P.L).power 4).lower (by
       filter_upwards [Delay.shift_pos G P.L] with x hx; unfold skies distance; apply le_of_eq; apply congr_arg abs; rw [Real.rpow_neg (show 0≤Ξ x from hx.le),←Real.sqrt_eq_rpow]; simp only [Function.comp_apply]; have ht:0<Real.sqrt (Ξ x):= Real.sqrt_pos.mpr hx; field_simp; rw [Real.sq_sqrt (show 0≤Ξ x from hx.le)])
omit hF in
def heat (L:Stage)(G:Gauge)(x:ℝ)(y:ℕ)(p:Palisade):=
    boldPrice L x (2*x) y + 2*x* vapor p (rot p x) (skies x) (wLevel G y (skies x))
lemma heat_glow : Beam G P.L (fun x=> heat L G (Ξ x) (f x) p):=by
   let d:=tip G P.L; let s:= skies ∘ d; let K:= 2+ceilingP p; let j:=p.coords* countCost p.a; let c:=p.density*j
   -- vapor=w*((2*s*c+I)+(K*s*c+I)); w=y*(8*card)*s; I=K²s²cj
   let b:=8*(Fintype.card G.ColorIndex:ℝ); let h x:= vapor p (rot p (d x)) (s x) (wLevel G (f x) (s x))
   let u(x:ℝ):= d x * s x*s x; have hu:Beam G P.L u:= squareB G P  -- args
   let a(x:ℝ):=(2*(f x:ℝ)*b)*u x
   let v(x:ℝ):=((2+K)*c+(2*K^2*c*j)*s x)
   have ha:Beam G P.L a:= (((Beam.coin 2).mul hF).mul (Beam.coin _)).mul hu
   have hv: Beam G P.L v:=(Beam.coin _).add ((Beam.coin _).mul (Beam.lax (flog P (G:=G)) (by norm_num)))
   apply (cloth G P L f hF).add (_ : Beam G P.L (fun x=>2*d x * h x))
   apply (ha.mul hv).lower; refine Eventually.of_forall fun x=> ?_; apply le_of_eq; apply congr_arg abs; unfold h a b v u vapor K rot wLevel c j s; simp only [Function.comp_apply]; ring
-- moss denominator price EPS.No ≤card trick. exact measure.Cost B.Bytes
omit hF in
def leaseScore (x:ℝ)(j:ℕ)(G:Gauge):= ( (Real.log x + Real.log 4)* Module.finrank ℝ G.Mat)* j
lemma leaseGlow : Beam G P.L (fun x=> leaseScore (Ξ x) (f x) G) := (((Beam.logfine G P.L|>.add (Beam.coin _)).mul (Beam.coin _)).mul hF)
omit hF in
lemma pine (G:Gauge)(x:ℝ)(hx:0<x)(p:ℕ): moss G (x^(-(1:ℝ))) p=Real.exp (-leaseScore x p G) :=by
    rw [Real.rpow_neg_one]; unfold moss leaseScore; rw [← Real.exp_log (show 0 < x⁻¹/4 from by positivity),Real.exp_log (show 0< x⁻¹/4 from by positivity)] -- nuisance
    have he:(x⁻¹/4)=Real.exp (-(Real.log x+Real.log 4)):=by rw [Real.exp_neg,Real.exp_add,Real.exp_log hx,Real.exp_log (show (0:ℝ)<4 by norm_num)]; field_simp
    rw [he,← Real.exp_nat_mul,← Real.exp_nat_mul]; congr 1; ring
omit hF in
lemma heatZero (g: ℝ→ℝ)(h:Beam G P.L g) : Pole G P.L (fun x=> courage G P.L x * Real.exp (g x)):=by
   refine (snowbank P G).lower ?_
   filter_upwards [h.lesser (show (0:ℝ)<1/2 by norm_num), (monitorG P G).eventually_ge_atTop 100] with x hx h
   rw [abs_of_pos (show 0<courage G P.L x*Real.exp (g x) from mul_pos (Real.exp_pos _) (Real.exp_pos _)), abs_of_pos (show 0< snow G P x from Real.exp_pos _)]; unfold snow courage; rw [← Real.exp_add]; apply Real.exp_monotone; let d:= Delay.fineMonitor G P.L x; change -d +_ ≤ _; have hp: g x ≤ Real.sqrt d:= (le_abs_self _).trans (by rw [← Real.sqrt_eq_rpow] at hx; exact hx)
   have he:0≤d:=le_trans (by norm_num) h; change _ ≤ -(1/2:ℝ)*d; nlinarith [Real.sqrt_nonneg d, Real.sq_sqrt he]
end YM.MSbar.Heath.Cottage
