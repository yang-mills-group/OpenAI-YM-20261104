import YM.OPE.Compatible.Yolk.Peak
/-!
 # Final giga payouts. pol(log β) width used both for rarity and expansion. q=P monitor as set. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C s : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
section
variable (Q:YM.ConnectedActivityE6.Target G P)(L:Side) (m n:ℕ)
lemma vault (h : 0<μ): ∃ j:ℕ,∀ᶠ x:ℝ in atTop,glen Q L μ x (Real.exp (-(echoL G L x)^j))≤ Real.exp (-(echoL G L x)^n):=by
   let A:ℝ:= P.top.supportExponent-Q.ε
   let y:ℝ:= 8*L.val+2; let I:=incomingK G L;let H:= Delay.bill G L
   let B(x:ℝ):=betaF G x L
   obtain ⟨hf,hT⟩:=riseD Q L h
   have he' : Rate G L 0 (fun x=>6*y*Real.exp A *freight Q L μ x) := hf.mul_left _
   let j:=n+2
   have hy:0≤y:=by unfold y; positivity
   refine ⟨j,?_⟩
   filter_upwards [(hf.mul_left (3*Real.exp A)) _ zero_lt_one,(hT.mul_left (3*Real.exp A)) _ zero_lt_one,he' 1 zero_lt_one,echo_growth G L|>.eventually_ge_atTop 2,Delay.bill_pays G L h (show (0:ℝ)<1/2 by norm_num) zero_le_one j,
    Delay.monitor_pays G L j zero_le_one (show (0:ℝ)<1/5 by norm_num), ((incomingK_rate G L (-1)).mul_left y).below (by norm_num) _ (by norm_num:(0:ℝ)<1/2),Delay.shift_pos G L] with x hF hT hY hb hv hf hx ht
   let w:=Real.exp (-H x^j);let u:=Real.exp (-H x^n); let e:= H x; have hb : 2 ≤ e := hb
   have hG : B x*w ≤ u:=by
      rw [show B x= _ from (Real.exp_log ht).symm]; unfold w u; rw [← Real.exp_add]; apply Real.exp_monotone; have h:Real.log (B x) ≤ e:=by unfold e H Delay.bill; have ht:=Nat.cast_nonneg (α:=ℝ) (radiusB x); unfold B; nlinarith [sq_nonneg (Real.log (betaF G x L) -1/2)]
      -- adjust log expression
      change Real.log _ + -(e^j) ≤ - (e^n); have hv: 1 ≤ e^n:= one_le_pow₀ (by linarith); unfold j; rw [pow_add]; unfold B at h; nlinarith only [hb,hv,h,mul_le_mul_of_nonneg_right hb (show 0≤ e^n by positivity),sq_nonneg (e-2), mul_nonneg (sub_nonneg.mpr hv) (sq_nonneg e)]
   have hl(i:ℝ)(hi:|3*i| ≤ B x^(1:ℝ)) (d:ℝ)(hd:0≤d)(he:d≤w):3*(i*d) ≤ u:=by
      rw [Real.rpow_one] at hi; rw [← mul_assoc]; exact (mul_le_mul ((le_abs_self _).trans hi) he hd ht.le).trans hG
   have hv':Real.exp (-Q.mark L μ x)≤w:=Real.exp_monotone (neg_le_neg (by
       rw [one_mul] at hv
       rw [show Q.mark L μ x=Delay.hatWin G L μ (1/2) x / 2 from (by change Delay.hatWin G L (μ/2) (1/2) x=_; unfold Delay.hatWin; ring)]
       have hp:= Delay.win_pos G L x h (show (0:ℝ)<1/2 by norm_num); linarith))
   let f:= freight Q L μ x; let t:= tolls Q L μ x; let v:=I x; let g:=Real.exp A
   have hf' : 3*(g*(w*t))≤u:= by rw [mul_left_comm g w, mul_comm w]; exact hl _ (by rw [←mul_assoc]; exact hT) _ (Real.exp_pos _).le le_rfl
   have he₂:3*(g*(f*Real.exp (-Q.mark L μ x)))≤u:= by rw [←mul_assoc g]; exact hl _ (by rw [←mul_assoc]; exact hF) _ (Real.exp_pos _).le hv'
   have hd : v≤ w:= by
     apply Real.exp_monotone; apply neg_le_neg; simpa only [one_mul] using hf
   have hv : 0<v:=Real.exp_pos _
   have hc : |g*((Real.exp (y*v)-1)*f)|≤2*y*g*|f| *v:=by
     rw [abs_mul,abs_mul,abs_of_nonneg (Real.exp_nonneg _)]
     have he : |Real.exp (y*v)-1|≤2*|y*v|:= Real.abs_exp_sub_one_le (hx.trans (by norm_num))
     rw [abs_of_nonneg (mul_nonneg hy hv.le)] at he; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (abs_nonneg f)) (Real.exp_pos _).le).trans_eq (by ring)
   have ht : 3*(g*((Real.exp (y*v)-1)*f))≤u:=by
      apply (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hc) (by norm_num:(0:ℝ)≤3)).trans; refine hl _ ?_ v hv.le hd; rw [abs_mul (6*y* _),abs_of_nonneg (by positivity : 0 ≤ 6*y*Real.exp A)] at hY; rw [abs_of_nonneg (by unfold g; positivity : 0 ≤ (3:ℝ)*(2*y*g*|f|)),show (3:ℝ)*(2*y*g*|f|)=_ from (by ring : (3:ℝ)*(2*y*g*|f|)=6*y*g*|f|)]; exact hY
   unfold glen awash; push_cast; change g*(w*t+f*Real.exp (-Q.mark L μ x)+(Real.exp (y*v)-1)*f)≤u; linarith only [ht,hf',he₂]
end
end YM.PhysicalNext.Repeat.Aroma
