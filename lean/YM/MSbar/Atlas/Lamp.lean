import YM.MSbar.Atlas.Drive
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Stock
open Lattice Wilson RG Function Filter MeasureTheory Metric
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f n':Side}{S:StepData c f}
open Precision Tree Pressure Push Push.AbsoluteSums ConnectedActivityE6 Push.Uniform
open Heath Bulk Finset
variable (P:Patch)(K:KernelChoices)(J:Voice G) (A B:Stage)(p:Palisade)
set_option quotPrecheck false
local notation "L"=> P.L
local notation "Ξ"=> tip G L
def snow (G:Gauge)(P:Patch)(x:ℝ):=Real.exp (-(1/2:ℝ)*Delay.fineMonitor G P.L x)
lemma snowbank (G:Gauge):Pole G P.L (snow G P):= fun a=> by unfold snow; simpa only [Real.rpow_one] using Rate.monitor_cutoff (G:=G) (a:=a) (δ:=1/2) (by norm_num) (γ:=1) one_pos («L»:=P.L)
lemma shadeG (G:Gauge):Beam G P.L (fun x=> (vestal P (radiusB (tip G P.L x)):ℝ)):= by simp_rw [vestal,Nat.cast_mul]; exact (char P G).mul (Beam.coin _)
lemma monitorG (G:Gauge): Filter.Tendsto (Delay.fineMonitor G P.L) Filter.atTop Filter.atTop:=Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (n:=2) (by norm_num)).comp (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G P.L))))
local notation "U0"=> sizingW K
local notation "n0"=> P.L
lemma interim (g:Clear G J) : ∀ᶠ x:ℝ in atTop,
      ∀ {f:Side}(R:Rep G f), FaceValue B (Ξ x) R →
        let y:= Ξ x; let b:=radiusB y; let w:= courage G n0 x
        (1+Real.exp (y*U0*(J.C*steps G p y)*(4*(skirt b:ℕ)) + R.beta*(stockMove G p y*p.noise)))*((belt b:ℝ)*(w+4*((Lattice.box (macroR P)).card*w+w)))+ w*xBill R.p (vestal P b) 1≤ snow G P x :=by
   let y:=Ξ; let M:= Delay.fineMonitor G n0; let f x:=(skirt (radiusB (y x)):ℝ); let t(x):=steps G p (y x)
   have ht: Rate G n0 (-(6/5)) t:=Rate.power.mul_left _; let u(x):=stockMove G p (y x); let K':= sizingW K; let v x:= (vestal P (radiusB (y x)):ℝ)
   have hf:= chargesA (G:=G) P _ (Beam.shore n0 G)|>.tick; let k':ℝ:= (Lattice.box (macroR P)).card; let b x:=(belt (radiusB (y x)):ℝ)
   let g' x:= y x*K'*(J.C*t x)*(4*f x)+2*y x*(u x*p.noise)
   let J' x:= (1+Real.exp 1) * (b x*(1+4*(k'+1)))
   let L' x:= B.supportExponent*v x + v x
   have hp : Rate G n0 (1+-(6/5)) g' := by
       have he := ((((Rate.hat (G:=G) («L»:=L)).mul_right K').mul (ht.mul_left J.C)).mul (hf.mul_left (4:ℝ))); rw [add_zero] at he; exact he.add (((Rate.hat (G:=G) («L»:=L)).mul_left 2).mul ((ht.mul_left 2).mul_right _))
   have hF : Beam G n0 J':=(Beam.coin _).mul ((char P G).mul (Beam.coin _)); have hL : Beam G n0 L':=((Beam.coin _).mul (shadeG P G)).add (shadeG P G)
   filter_upwards [hp.below (by norm_num) _ zero_lt_one, hF.lesser (show (0:ℝ)<1 by norm_num), hL.lesser (show (0:ℝ)<1/2 by norm_num),
        (monitorG P G).eventually_ge_atTop 400,Delay.shift_pos G n0] with x hg hj hv hw hh ss R hx
   let l:= y x; let s:= M x; let r:= vestal P (radiusB l); have hM : s ≥400:=hw; have hz :0<2*t x:=by have hp:= wi G p; unfold t steps increments y; positivity
   have hC:R.beta≤2*l:=hx.upper; have hT:= mul_le_mul_of_nonneg_right hC (show 0≤u x*p.noise from mul_nonneg hz.le p.costs.le)
   have ho : y x* K'*(J.C*t x)*(4*(skirt (radiusB l):ℕ)) + R.beta*(u x*p.noise) ≤1 := by
       apply le_trans (b:=g' x) ?_ ((le_abs_self _).trans hg); unfold g' y at *; linarith only [hT]
   let w:=courage G n0 x; let p':=(B.supportExponent * r + r:ℝ); have he : J' x ≤ s := (le_abs_self _).trans ((by rw [Real.rpow_one] at hj; exact hj))
   have hN:p' ≤ Real.sqrt s := (le_abs_self (L' x)).trans ((by rw [← Real.sqrt_eq_rpow] at hv; exact hv))
   have ha:0≤w:= (Real.exp_pos _).le
   intro yy Lb w₀
   have h' : J' x*w+xBill R.p r 1*w = (1+Real.exp 1)*((belt Lb:ℝ)*(w+4*((Lattice.box (macroR P)).card*w+w)))+w*xBill R.p r 1 :=by
       unfold J' b k'; change _= (1+Real.exp 1)*(((belt Lb:ℝ)*(w+_)))+ _; unfold Lb yy; ring
   have hz : Real.exp (s/2)=(Real.exp (s/4))^2:=by rw [show s/2=↑(2:ℕ)*(s/4) by push_cast; ring,Real.exp_nat_mul]; -- 2 nat
   let X:=Real.exp (s/4); have hX : s/4 ≤ X:= (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _); have hp: p'≤ s/4:=by nlinarith [Real.sq_sqrt (show 0≤ s by linarith),Real.sqrt_nonneg s]
   have hF: xBill R.p r 1=2*Real.exp p':=by unfold p' xBill; rw [hx.support,mul_one,Real.exp_add]; ring
   refine le_trans (add_le_add_left (mul_le_mul_of_nonneg_right (add_le_add_right (Real.exp_monotone ho) _) (show 0≤↑(belt Lb)*(w+4*(k'*w+w)) from ?_)) _) ?_
   · unfold k'; positivity
   rw [← h',hF]; change _ ≤ Real.exp _; rw [show -(1/2:ℝ)* _ = s/2+ -s by change -(1/2:ℝ)*s=_; ring, Real.exp_add (s/2) (-s), hz]; have h₀:= Real.exp_monotone hp
   have hh : J' x + 2*Real.exp p' ≤ X^2:=by nlinarith only [hX,hM,(show Real.exp p'≤X from h₀),he]
   rw [← add_mul]; exact mul_le_mul_of_nonneg_right hh ha
-- not Claim.H.Flags dissipate.But thresholds n
end YM.MSbar.Heath.Stock
