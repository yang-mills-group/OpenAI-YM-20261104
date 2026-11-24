import YM.SchemeRG11.Saddle.Lamina
/-! Integration of coefficient PS. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.SchemeRG11.Sway.Lam
open Function Filter Set MeasureTheory Metric PertExtension.Series Radial Tested
open scoped Classical ContDiff Topology BigOperators NNReal PowerSeries
open Pert.Orb Local
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E][MeasurableSpace E] [BorelSpace E]
local notation "coef" => PowerSeries.coeff (R:=ℂ)

variable (μ: Measure E) [μ.IsAddHaarMeasure]
def Cost(S:E→ℝ)(W:JetArray E)(i:ℕ)(x:E):= (Radial.kernel S x:ℂ)*coef i (W x)
def heart(S:E→ℝ)(W:JetArray E):ℂ⟦X⟧:=PowerSeries.mk fun i=> ∫ x, Cost S W i x ∂μ
def choir(S K:E→ℝ)(W:JetArray E):ℂ⟦X⟧:= heart μ S (fibers S K*W)*(heart μ S (fibers S K))⁻¹
lemma cost_pay{S:E→ℝ}(g:Goal S){W:JetArray E}(h:Ready W)(i): Integrable (Cost S W i) μ:=by
 obtain ⟨c,hc,h⟩:=g -- rename avoid
 rename_i H
 have hm:= H i
 obtain ⟨C,hC,k,he⟩:= hm.2
 apply ((bill_integrable μ k hc).const_mul C).mono' _ (Eventually.of_forall fun x=>?_); swap
 · unfold Cost; rw [norm_mul,Complex.norm_real,Real.norm_eq_abs (Radial.kernel ..),abs_of_pos kernel_pos]; specialize h x; unfold bill; change _≤ C*((1+‖x‖)^k*Real.exp _); rw [← mul_assoc,mul_comm _ (Real.exp _)]; apply mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (he x) (norm_nonneg _) (Real.exp_pos _).le -- conditions order
 unfold Cost Radial.kernel; apply Continuous.aestronglyMeasurable; exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (Smooth.continuousJet ..).neg)).mul hm.1
lemma heart_add{S:E→ℝ}(g:Goal S){W T:JetArray E}(h:Ready W)(hv: Ready T): heart μ S (W+T)=heart μ S W+heart μ S T:=by
 ext n; simp only [heart,PowerSeries.coeff_mk,map_add,Cost,Pi.add_apply,mul_add]; exact integral_add (cost_pay μ g h n) (cost_pay μ g hv n)
lemma heart_scale{S:E→ℝ}(g:Goal S)(t:ℂ⟦X⟧){W:JetArray E}(h:Ready W): heart μ S ((fun _=>t)*W)=t*heart μ S W:=by
 ext n; simp only [heart,PowerSeries.coeff_mk,PowerSeries.coeff_mul,Pi.mul_apply,Cost]
 simp only [Finset.mul_sum,mul_left_comm (Complex.ofReal _)]; change (∫ x,∑ i∈Finset.antidiagonal n, coef i.1 t*Cost S W i.2 x ∂μ)=_; rw [integral_finsetSum]; swap
 · exact fun i _=>(cost_pay μ g h i.2).const_mul _
 simp_rw [integral_const_mul]; rfl
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma heart_face {f K:E→ℝ}:heart μ f (fibers f K)=raise (Yellow μ f K):=by
 ext n; rw [heart,cscale,Yellow,PowerSeries.coeff_mk,PowerSeries.coeff_mk]; unfold Cost; simp_rw [factorR]; rw [Radial.moment,← integral_complex_ofReal]; simp only [normTerm,Complex.ofReal_mul]; apply integral_congr_ae; exact Eventually.of_forall fun i=>mul_comm ..
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma heart_load{K f S:E→ℝ}(h:ContDiffAt ℝ ∞ K 0)(hf:ContDiffAt ℝ ∞ f 0):heart μ S (fibers S K * ChartC (fun x=>(f x:ℂ)))= raise (Yellow μ S (K*f)):=by
 rw [← heart_face]; unfold fibers; rw [mul_assoc]; congr 2; ext1 x
 have he(K:E→ℝ)(hK:ContDiffAt ℝ ∞ K 0): fitR K x=ChartC (fun y=>(K y:ℂ)) x:= (chart_line hK x).symm
 simp only [Pi.mul_apply, he _ h]; rw [he (K*f) (h.mul hf)]
 rw [show (fun y=> (((K*f) y:ℝ):ℂ)) = (fun y=> (K y:ℂ)*(f y:ℂ)) from funext fun i=>Complex.ofReal_mul .., chart_mul (f:=fun y=>(K y:ℂ)) (g:=fun y=>(f y:ℂ)) ((Complex.ofRealCLM).contDiff.contDiffAt.comp (f:=K) 0 h) ((Complex.ofRealCLM).contDiff.contDiffAt.comp (f:=f) 0 hf)]; rfl
lemma choir_face{S K:E→ℝ}(h: ContDiffAt ℝ ∞ K 0)(H: Goal S)(hk:0<K 0){f:E→ℝ}(hf: ContDiffAt ℝ ∞ f 0):choir μ S K (ChartC (fun x=> (f x:ℂ)))=raise (Realm μ S K f):=by rw [choir, heart_load μ h hf, Realm, map_mul, raise_inv (yellow_pos μ H hk).ne',heart_face]
lemma bowl_pos{K f:E→ℝ} (g:Goal f)(h:0<K 0): PowerSeries.constantCoeff (heart μ f (fibers f K))≠0:= by rw [heart_face, ←PowerSeries.coeff_zero_eq_constantCoeff,cscale,PowerSeries.coeff_zero_eq_constantCoeff];exact Complex.ofReal_ne_zero.mpr (yellow_pos μ g h).ne'
lemma choir_add{K S:E→ℝ}(H:Goal S){W T:JetArray E}(h:Ready W)(hv:Ready T):choir μ S K (W+T)=choir μ S K W + choir μ S K T:=by rw [choir,mul_add,heart_add μ H ((factor_ready S K).mul h) ((factor_ready S K).mul hv),add_mul];rfl
lemma choir_scale{K S:E→ℝ}(H:Goal S){W:JetArray E}(h:Ready W)(t:ℂ⟦X⟧): choir μ S K ((fun _=>t)*W) = t* choir μ S K W:=by rw [choir,mul_left_comm _ _ W, heart_scale μ H t ((factor_ready S K).mul h),mul_assoc,choir]
lemma choir_parts{K S:E→ℝ}(H:Goal S)(h:ContDiffAt ℝ ∞ K 0)(hk:0<K 0){f:E→ℂ}(g:ContDiffAt ℝ ∞ f 0):
    choir μ S K (ChartC f)=raise (Realm μ S K (Complex.re ∘ f))+PowerSeries.C Complex.I * raise (Realm μ S K (Complex.im ∘ f)):=by
 let w:=Complex.re ∘ f; let u:= Complex.im ∘ f
 have hw: ContDiffAt ℝ ∞ w 0:= Complex.reCLM.contDiff.contDiffAt.comp (f:=f) 0 g
 have hu: ContDiffAt ℝ ∞ u 0:= Complex.imCLM.contDiff.contDiffAt.comp (f:=f) 0 g
 let A:=Complex.ofRealCLM
 nth_rw 1 [show f=(fun x=>A (w x)+Complex.I*A (u x)) from funext fun i=> by change f i=(↑(f i).re:ℂ)+ Complex.I*(↑(f i).im:ℂ); rw [mul_comm]; exact (Complex.re_add_im ..).symm]; rw [chart_add (f:=fun x=>A (w x)) (g:=fun x=>Complex.I*A (u x)) (A.contDiff.contDiffAt.comp (f:=w) 0 hw) (contDiffAt_const.mul (A.contDiff.contDiffAt.comp (f:=u) 0 hu)), choir_add μ H (chart_ready _) (chart_ready _), show ChartC (fun x=> Complex.I*A (u x))=(fun _=> PowerSeries.C Complex.I)* ChartC (fun x=>A (u x)) from (chart_mul (f:=fun _=> Complex.I) (g:=fun x=>A (u x)) contDiffAt_const (A.contDiff.contDiffAt.comp (f:=u) 0 hu)).trans (by rw [chart_const]),choir_scale μ H (chart_ready _)]
 exact congrArg₂ (· + ·) (choir_face μ h H hk hw) (congrArg (fun x=>PowerSeries.C Complex.I*x) (choir_face μ h H hk hu))
end YM.SchemeRG11.Sway.Lam
