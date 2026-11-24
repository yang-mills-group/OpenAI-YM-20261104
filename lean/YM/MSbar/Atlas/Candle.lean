import YM.MSbar.Atlas.Flock
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Stock
open Lattice Wilson RG Function Filter MeasureTheory Metric
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f n':Side}{S:StepData c f}
open Precision Tree Pressure Push Push.AbsoluteSums ConnectedActivityE6 Push.Uniform
open Heath Bulk Finset
variable (P:Patch)(K:KernelChoices)(J:Voice G) (A B:Stage)(s:Palisade)
set_option quotPrecheck false
local notation "L"=> P.L
local notation "Ξ"=> tip G L
open SectorNext.Vacuum
lemma tale (g:Clear G J): ∀ᶠ x in atTop, base J (Ξ x) ≤ temp x:=by
   let u := (8*J.C*shade G)*8; have hu:0<u:= by have h:=shade_pos G; have hp:0<J.C:=zero_lt_one.trans_le g.cost; unfold u; positivity
   let L': Side:=⟨1,one_pos⟩; let Q i:=u*↑(radiusB i)
   have hv : Beam G L' Q:= (Beam.coin u).mul (Beam.rare G L')
   filter_upwards [shiftedLog G L,hv.lesser (a:=1) zero_lt_one] with x hx₀ h
   obtain ⟨hb,hx,hi,hk,hv,hh⟩:= hx₀; let y:=Ξ x; have hz:0 < x:=zero_lt_one.trans hx; have hz':0<y:=zero_lt_one.trans hi; have ht : (Real.log x)^2≤ radiusB x:=Nat.le_ceil _; have hp: (Real.log y)^2 ≤ 4* (radiusB x:ℝ):= by
       calc _ ≤ (2*Real.log x)^2:= pow_le_pow_left₀ (Real.log_pos hi).le hh _
            _ ≤ _:=by linarith only [ht]
   have ha: y ^ (-(1/2:ℝ)) ≤ 2*(Real.sqrt x)⁻¹:=by
       rw [Real.rpow_neg hz'.le,← Real.sqrt_eq_rpow,← div_eq_mul_inv]; have hg := Real.sqrt_pos.mpr hz'; have hc:= Real.sqrt_pos.mpr hz
       rw [le_div_iff₀ hc,mul_comm,← div_eq_mul_inv,div_le_iff₀ hg]; nlinarith only [Real.sq_sqrt hz.le,Real.sq_sqrt hz'.le,hk,hg,hc]
   have hs:u*(radiusB x:ℝ)≤ bbP x:= (le_abs_self (Q x)).trans (show _≤ bbP x from by simpa [L',bbP,Delay.fineMonitor,betaF] using h)
   let k:=8*J.C*shade G; have hh:0≤k:=by change 0<k*8 at hu; linarith
   calc
       _ = k*(y^(-(1/2:ℝ))* (Real.log y)^2):=by unfold base skies distance k y; ring
       _ ≤ k*(2*(Real.sqrt x)⁻¹*(4*(radiusB x:ℝ))):=mul_le_mul_of_nonneg_left (mul_le_mul ha hp (sq_nonneg _) (by positivity)) hh
       _ ≤ _:= by apply le_trans ?_ (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Real.sqrt_nonneg x))); unfold u k; apply le_of_eq; ring
lemma shellA (G : Gauge) : Beam G L (fun x=> Real.log (4*(1+2*tip G P.L x))) := by
    let f:=tip G P.L; have hp:= (Work.E09.betaF_growth G P.L).eventually_ge_atTop 1
    refine ((Beam.coin (Real.log 12)).add (Beam.logfine G L)).lower (hp.mono fun x he=>?_)
    have hs :0 < f x:=zero_lt_one.trans_le he
    change |Real.log (4*(1+2*f x))| ≤ |Real.log 12+Real.log (f x)|
    rw [abs_of_nonneg (Real.log_nonneg (by linarith only [hs]))]; apply le_trans _ (le_abs_self _); rw [← Real.log_mul (by norm_num) hs.ne']; apply Real.log_le_log (by positivity); linarith only [show 1≤ f x from he]
-- exponent costs relative exp(-monitor). give cancer.Both. force rare.K.Tag
variable {f' : StepData c f}
def treeTax (G:Gauge)(P:Patch)(K: KernelChoices)(x:ℝ) := K.penalty/2 + Module.finrank ℝ G.Mat*Real.log (4*(1+2*tip G P.L x))
lemma turtle : ∀ᶠ x in atTop, ∀ {c f d d':Side} {S:StepData c f}(R: Rep G d')(Y:Rep G d), S.patch=P → S.kernel=K → FaceValue A x Y → FaceValue B (tip G P.L x) R →
      Real.exp (ankle Y.p Y.clip A.width A.paths (ability x) (lbt x) (base J (Ξ x)) 1 Y.beta)*Real.exp (SectorNext.Vacuum.shellBill G S R.beta-R.beta*S.kernel.penalty*R.p.threshold^2/2)≤ courage G P.L x:=by
   -- later cross S1.c any.f tape R fine can be different sizes. generalize f'.
   let M x:= bbP (Ξ x)
   let v x := yCover P J A x + treeTax G P K x
   have hV:Beam G L v:=(deco P J A).add ((Beam.coin _).add ((Beam.coin _).mul (shellA P G)))
   have hp:Tendsto M atTop atTop := Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (n:=2) (by norm_num)).comp (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G L))))
   have hK:=K.penalty_pos
   filter_upwards [hV.lesser zero_lt_one,hp.eventually_ge_atTop (8/K.penalty),shiftedLog G L] with x hv hh hz
   intro c f d d' S R Y he ht hq hl
   have hu:Y.beta≤8*Ξ x:=by linarith only [hq.upper,hz.2.2.2.1,hz.2.1]
   have hA : ankle Y.p Y.clip A.width A.paths (ability x) (lbt x) (base J (Ξ x)) 1 Y.beta ≤ yCover P J A x:= by rw [firing A x hq]; exact heating A _ hq.enough _ _ _ hu
   let q:=Ξ x; have hq':0<q:= zero_lt_one.trans hl.enough; have hB:0<R.beta:= lt_of_lt_of_le (half_pos hq') hl.beta
   have hs : shellBill G S R.beta ≤ treeTax G P K x:=by unfold shellBill treeTax; rw [ht,abs_of_pos hB]; gcongr; exact hl.upper
   have hF : v x ≤ M x:= (le_abs_self _).trans (by simpa [M, Delay.fineMonitor,bbP,tip] using hv)
   have hT: q* R.p.threshold^2=(M x)^2:=by rw [hl.threshold, temp_shape]; change q*(cue q*M x)^2=_; unfold cue; rw [mul_pow,← mul_assoc,inv_pow,Real.sq_sqrt hq'.le,mul_inv_cancel₀ hq'.ne',one_mul]
   have hy := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl.beta hK.le) (sq_nonneg R.p.threshold); have hw : 8≤M x*K.penalty:=(div_le_iff₀ hK).mp hh
   rw [← Real.exp_add, ht]; unfold courage; apply Real.exp_monotone; change _ ≤ -(M x); unfold v at hF; linarith only [hA,hF,hs,mul_le_mul_of_nonneg_left hw (show 0≤ M x from (Real.exp_pos _).le),hy,congr_arg (K.penalty*·) hT] -- normalize
end YM.MSbar.Heath.Stock
