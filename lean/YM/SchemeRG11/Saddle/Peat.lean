import YM.SchemeRG11.Saddle.Lute
/-! Formal rows, powers and product directions for the FP adapters. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.SchemeRG11.Sway.Local
open Function Filter Set MeasureTheory Metric PertExtension.Series Radial Tested
open scoped Classical ContDiff Topology BigOperators NNReal
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F]
lemma order_le_smooth(k:ℕ):(k:WithTop ℕ∞)≤∞:= by exact WithTop.coe_le_coe.mpr le_top
lemma jetLinear (K:E→ℝ)(hk:ContDiffAt ℝ ∞ K 0)(e:F→L[ℝ]E)(n:ℕ)(x:F):
    jet (K ∘ e) n x= jet K n (e x):=by
 have h: ContDiffAt ℝ n K 0:=hk.of_le (order_le_smooth n)
 have hg: ContDiffAt ℝ n (K ∘ e) 0:= ContDiffAt.comp (g:=K) (f:=e) 0 (by rw [map_zero];exact h) e.contDiff.contDiffAt
 rw [homogeneous_derivative _ _ _ hg,homogeneous_derivative _ _ _ h]; simp only [comp_apply,map_smul]
lemma layersWeave (f:E→ℝ)(g:F→ℝ)(hf:ContDiffAt ℝ ∞ f 0)(hg:ContDiffAt ℝ ∞ g 0)(p:E×F)(n:ℕ):
   jet (fun x:E×F=> f x.1+g x.2) n p= jet f n p.1 + jet g n p.2:=by
 let a:E×F→ℝ:= f ∘ ContinuousLinearMap.fst ℝ _ _; let b:E×F→ℝ:=g ∘ ContinuousLinearMap.snd ℝ _ _
 change jet (a+b) n p= _
 rw [←show jet a n p=jet f n p.1 from jetLinear f hf (ContinuousLinearMap.fst ℝ _ _) n p,←show jet b n p=jet g n p.2 from jetLinear g hg (ContinuousLinearMap.snd ℝ _ _) n p]
 unfold jet; rw [iteratedFDeriv_add_apply ..]; swap
 · exact (hf.of_le (order_le_smooth n)).comp (f:=fun x:E×F=>x.1) 0 contDiffAt_fst
 all_goals first | exact mul_add .. | exact (hg.of_le (order_le_smooth n)).comp (f:=fun x:E×F=>x.2) 0 contDiffAt_snd
lemma jetSq {g:F→ℝ}(hg: ContDiffAt ℝ ∞ g 0)(h:∀ (t:ℝ) x,g (t • x)=t^2*g x)(i:ℕ)(x:F): jet g i x= if i=2 then g x else 0:=by
 rw [homogeneous_derivative _ _ _ (hg.of_le (order_le_smooth i))]; simp_rw [h]
 rw [iteratedDeriv_mul_const_field,iteratedDeriv_pow]; split_ifs with hi
 · subst hi; norm_num [Nat.factorial,Nat.descFactorial]; ring
 rcases lt_or_gt_of_ne hi with h|h
 · simp [show 2-i≠0 by omega]
 simp [Nat.descFactorial_eq_zero_iff_lt.mpr h]
lemma tailLift {f:E→ℝ}{g:F→ℝ}(hf:Stationary f)(hg:ContDiffAt ℝ ∞ g 0)(h:∀ (t:ℝ) x,g (t • x)=t^2*g x)(K:E→ℝ)(hK:ContDiffAt ℝ ∞ K 0):
   normTerm (fun p:E×F=>K p.1) (fun p:E×F=>f p.1+g p.2)= fun k (p:E×F)=>normTerm K f k p.1 * kernel g p.2:=by
 let D(p:E×F):=f p.1+g p.2
 have hl(i:ℕ)(p): layers D i p=layers f i p.1:=by
    by_cases hi:i=0
    · simp [hi,layers]
    unfold layers; rw [layersWeave f g hf.smooth hg, jetSq hg h]; simp [hi]
 have hh (i j:ℕ)(p:E×F): Zone.TaylorPow (layers D) i j p= Zone.TaylorPow (layers f) i j p.1:=by
    induction i generalizing j with
    | zero=>rfl
    | succ i ih=>unfold Zone.TaylorPow; unfold Zone.mul; exact Finset.sum_congr rfl (fun u _=> by rw [hl,ih])
 have he(i:ℕ)(p:E×F):expsum (layers D) i i p=expsum (layers f) i i p.1:= Finset.sum_congr rfl fun j _=>congrArg _ (hh j i p)
 funext k p; change integrandSeries D _ k p*Radial.kernel D p=(integrandSeries f K k p.1*Radial.kernel f p.1)*_
 unfold integrandSeries
 rw [show Zone.mul (jet (fun p:E×F=> K p.1)) (fun j=>expsum (layers D) j j) k p= Zone.mul (jet K) (fun j=>expsum (layers f) j j) k p.1 from Finset.sum_congr rfl fun i _=>congrArg₂ (· * ·) (jetLinear K hK (ContinuousLinearMap.fst ℝ E F) i.1 p) (he i.2 p),Radial.kernel,layersWeave f g hf.smooth hg, neg_add, Real.exp_add]; exact (mul_assoc ..).symm
lemma weaveSeed{f:E→ℝ}{g:F→ℝ}(hf:Stationary f)(hg: ContDiffAt ℝ ∞ g 0)(h:∀ (t:ℝ) x,g (t • x)= t^2*g x): Stationary (fun p:E×F=> f p.1+g p.2) where
 smooth:= (hf.smooth.comp (f:=fun p:E×F=>p.1) 0 contDiffAt_fst).add (hg.comp (f:=fun p:E×F=>p.2) 0 contDiffAt_snd)
 base0:=by
    have ha:g 0=0:= by simpa using h 0 (0:F)
    change f 0+g 0=0; simp [ha,hf.base0]
 base1 p:=by rw [layersWeave f g hf.smooth hg,hf.base1,jetSq hg h]; simp
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma weaveCost{f:E→ℝ}{g:F→ℝ}(hf:Stationary f)(hg:ContDiffAt ℝ ∞ g 0)(H:Goal f)(J:Goal g): Goal (fun p:E×F=>f p.1+g p.2):=by
 obtain ⟨c,hc,h⟩:=H; obtain ⟨d,hd,D⟩:=J
 refine ⟨min c d,lt_min hc hd,fun u=>?_⟩
 rw [layersWeave f g hf.smooth hg]; rcases max_cases ‖u.1‖ ‖u.2‖ with ⟨he,hx⟩|⟨he,hx⟩ <;> rw [Prod.norm_def,he]
 · exact (mul_le_mul_of_nonneg_right (min_le_left ..) (sq_nonneg _)).trans ((h u.1).trans ((le_add_of_nonneg_right ((show 0≤d*‖u.2‖^2 by positivity).trans (D u.2)))))
 exact (mul_le_mul_of_nonneg_right (min_le_right ..) (sq_nonneg _)).trans ((D u.2).trans ((le_add_of_nonneg_left ((show 0≤c*‖u.1‖^2 by positivity).trans (h u.1)))))
variable [MeasurableSpace E] [BorelSpace E][MeasurableSpace F] [BorelSpace F]
    (μ: Measure E)[μ.IsAddHaarMeasure](ν: Measure F)[ν.IsAddHaarMeasure]
lemma shade_integrable{g:E→ℝ}(H:Goal g): Integrable (kernel g) μ:=by
 obtain ⟨c,hc,h⟩:=H
 apply (bill_integrable μ 0 hc).mono' (by unfold kernel;exact (Real.continuous_exp.comp (Smooth.continuousJet g _).neg).aestronglyMeasurable) (Eventually.of_forall (fun x=>?_))
 rw [Real.norm_eq_abs,abs_of_pos kernel_pos,bill,pow_zero,one_mul]; exact Real.exp_le_exp.mpr (by linarith [h x])
theorem shade_pos{g:E→ℝ}(H:Goal g):0<∫ x,kernel g x ∂μ:= integral_exp_pos (shade_integrable μ H)
omit [BorelSpace E] [BorelSpace F] in
lemma relocation_split{K f:E→ℝ}{g:F→ℝ}(hK:ContDiffAt ℝ ∞ K 0)(hf:Stationary f)(hg:ContDiffAt ℝ ∞ g 0)(H:∀ (t:ℝ) x,g (t • x)= t^2*g x):
  Radial.moment (μ.prod ν) (fun p:E×F=>K p.1) (fun p:E×F=> f p.1+g p.2)= fun i=>Radial.moment μ K f i*(∫ y,kernel g y ∂ν):=by
 funext i; unfold Radial.moment; rw [tailLift hf hg H K hK]; exact integral_prod_mul ..
open scoped PowerSeries
def Yellow (S K:E→ℝ):ℝ⟦X⟧:= PowerSeries.mk (moment μ K S) -- moment conflict?
def Realm(f K:E→ℝ)(W:E→ℝ):ℝ⟦X⟧:= Yellow μ f (K*W) * (Yellow μ f K)⁻¹
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma zero_fact (f K:E→ℝ)(u:E): integrandSeries f K 0 u=K 0:=by simp [integrandSeries,Zone.mul,expsum,Zone.TaylorPow]
omit [μ.IsAddHaarMeasure] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma yellow_bill (S K:E→ℝ): PowerSeries.constantCoeff (Yellow μ S K)= K 0 * ∫ x,kernel S x ∂μ:=by
 rw [Yellow,←PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_mk]; unfold moment normTerm; simp_rw [zero_fact]; exact integral_const_mul ..
lemma yellow_pos {S K:E→ℝ}(hf:Goal S)(h:0<K 0): 0<PowerSeries.constantCoeff (Yellow μ S K):=by rw [yellow_bill]; exact mul_pos h (shade_pos μ hf)
lemma taxa {E':Type*} [Field E'](a b:E'⟦X⟧)(hb:PowerSeries.constantCoeff b≠ 0)(c:E')(hc:c≠0): PowerSeries.C c * a * (PowerSeries.C c * b)⁻¹=a*b⁻¹:=by
 let P:= PowerSeries.C (R:=E') c * b
 have hl: PowerSeries.constantCoeff P≠0:=by unfold P;rw [map_mul,PowerSeries.constantCoeff_C]; exact mul_ne_zero hc hb
 have hi: IsUnit P:= PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hl)
 refine hi.mul_right_inj.mp ?_
 change P * (_ * a * P⁻¹) = P * (a * b⁻¹)
 calc
   _= PowerSeries.C c*a * (P*P⁻¹):=by ring
   _= PowerSeries.C c*a:=by rw [PowerSeries.mul_inv_cancel _ hl,mul_one]
   _=(PowerSeries.C c*a)*(b*b⁻¹):=by rw [PowerSeries.mul_inv_cancel _ hb,mul_one]
   _=_:=by unfold P; ring
lemma kcal(a:ℕ→ℝ)(c:ℝ): PowerSeries.mk (fun i=>c*a i)=PowerSeries.C c * PowerSeries.mk a:=by
 ext k; rw [PowerSeries.coeff_C_mul]; simp
end YM.SchemeRG11.Sway.Local
