import YM.RG12SharpGram.Weak.Panels

/-!
# Last stage of thermal hazard price

Only ordinary fixed-stage costs in Evident. Ensure log-sized window available one
step above k via true ratio index J growing into each block (positive widths).
Note refactor budget at beginning constraints don't require `Wheel` monotone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12SharpGram.Fence
open Filter Finset Function Lattice MeasureTheory
open RG Wilson Push GridApprox Cells Overlay Next.Rank.Station
open MergeProof.East
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}
variable {A:Levels G}
lemma window_slope (c:ℝ) (hc:0 < c): ∀ᶠ i:ℕ in atTop, let j:= A.clock.J (i+1); c*(j:ℝ) < (A.S.block i).val:=by
   have H:Tendsto (fun i:ℕ=> i+1) atTop atTop := tendsto_atTop_mono (f:=id) (fun i:ℕ=> i.le_succ) tendsto_id; let d:=Real.log 2; have he:0<d:=Real.log_pos (by norm_num)
   filter_upwards [(tendsto_natCast_atTop_atTop.comp (A.fits.deep.comp H) : Tendsto _ _ (atTop:Filter ℝ)).eventually_gt_atTop (c/d)] with i hi; intro j; let z:ℝ:=j; change c/d<z at hi; have hz:0<z:=(div_pos hc he).trans hi
   let X:= A.params (i+1); let L:ℝ:=(A.S.block i).val; have ht:1<L:=by unfold L; exact Nat.one_lt_cast.mpr (show 1 < (A.S.block i).val from lt_of_lt_of_le (by norm_num) (A.S.block_large i))
   have ha: d ≤ Real.log (1+X.paths+X.width⁻¹+X.columns+X.clip.relaxation+X.supportExponent):= Real.log_le_log (by norm_num) (by linarith only [X.paths_pos,(inv_pos.mpr X.width_pos), X.clip.radius_pos,X.price_pos,X.columns_ge])
   have hu : d ≤ (z^2)⁻¹ * Real.log L:=ha.trans ((div_le_iff₀ (Real.log_pos ht)).1 (A.fits.logCost i))
   rw [inv_mul_eq_div,le_div_iff₀ (pow_pos hz _)] at hu; have hv:c<z*d:=(div_lt_iff₀ he).1 hi
   change c*z < L; linarith only [hu, Real.log_le_sub_one_of_pos (zero_lt_one.trans ht),mul_lt_mul_of_pos_right hv hz]
lemma ceiling_ : ∀ᶠ i:ℕ in atTop, room A i (i+1) 2:=by
   filter_upwards [window_slope (A:=A) 1000 (by norm_num)] with i hi
   let L:ℝ:=(A.S.block i).val; let a:=A.S.a (i+1); let j:=A.clock.J (i+1); let z:ℝ:=j
   have hj:4 ≤ z:= by unfold z; exact_mod_cast A.clock.adm (i+1)
   change 1000*z < L at hi; change 2*(a*(2:ℕ)+30*a*(z+5)) < A.S.a i
   rw [show A.S.a i=a*L from by unfold a L; rw [A.S.a_step]; field_simp]
   push_cast; linarith only [mul_lt_mul_of_pos_left (show 2*(2+30*(z+5))<L by linarith only [hi,hj]) (show 0<a from A.S.a_pos _)]

lemma evident (Y:Stage)(L:ℕ) (u:ℝ) (h:DoorRate Y L ≤ u) : (L:ℝ) ≤ u ∧ Y.paths ≤ u ∧ Y.clip.direct ≤ u ∧ Y.clip.linear⁻¹ ≤ u ∧ Y.clip.relaxation ≤ u ∧ Y.width⁻¹ ≤ u:=by
   unfold DoorRate at h
   refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith only [Y.paths_pos,(inv_pos.mpr Y.width_pos), Y.clip.radius_pos,Y.price_pos,Y.columns_ge,Y.drift_ge, (inv_pos.mpr Y.clip.tail_pos), Y.clip.quadratic_pos,h,Nat.cast_nonneg (α:=ℝ) L]
variable (hG:G.Simple) (hp:Evident A)
lemma fiat_log : ∀ᶠ z:ℝ in atTop, ∀ Y:Stage, Y.paths≤Real.log z→ Y.clip.direct ≤ Real.log z → Vac.fiat G Y z ≤ (Real.log z)^3:=by
   let M:ℝ:=Fintype.card PlaqAxes; let E:ℝ:= Module.finrank ℝ G.Mat; have hE:0≤E:=by unfold E; positivity
   have hM:0 ≤ M:=by unfold M; positivity
   filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,Real.tendsto_log_atTop.eventually_ge_atTop (13+2*M+8*E), Real.tendsto_log_atTop.eventually_ge_atTop (Real.log 16)] with z hs ht hy Y hY hd
   let x:= Real.log z; have hx:0≤x:=zero_le_one.trans hs
   have ht': Vac.fiat G Y z ≤ 2*(1+(4*x+1))+1+M*(x+x^2)+4*E*(x+x/2):=by unfold Vac.fiat; unfold M E x; gcongr; exact Y.paths_pos.le
   apply ht'.trans; have he : 2*(1+(4*x+1))+1≤ 13*x^2:= by change 1 ≤ x at hs; nlinarith only [hs]
   have hq:x ≤ x^2:= by change 1 ≤ x at hs; nlinarith only [hs]
   calc
      _ ≤ 13*x^2+M*(2*x^2)+ E*(8*x^2) := by linarith only [he,mul_le_mul_of_nonneg_left hq hM,mul_le_mul_of_nonneg_left hq hE,mul_nonneg hE (sq_nonneg x)]
      _ ≤ x^3 := by change 13+2*M+8*E ≤ x at ht; linarith only [mul_le_mul_of_nonneg_right ht (sq_nonneg x)]

include hG hp
lemma gate_price : ∀ᶠ i:ℕ in atTop, let X:=Real.log (A.clock.hatBeta (i+1)); ((A.S.block i).val:ℝ)≤X ∧ (A.params (i+1)).clip.linear⁻¹≤ X ∧ Vac.treasury A (i+1) ≤ X^3 :=by
   have hs:Tendsto (fun i:ℕ=>i+1) atTop atTop:= tendsto_atTop_mono (f:=id) (fun i:ℕ=> i.le_succ) tendsto_id
   filter_upwards [hp.wheel, hs.eventually (Vac.treasury_stage A hG), ((hat_rate A hG).comp hs).eventually (fiat_log (G:=G))] with i he hi hp; intro x
   let j:=A.clock.hatBeta i; have hv:0<Real.log j:= Real.log_pos (A.fits.delayed i); have hh: Real.log j ≤ x:=Real.log_le_log (zero_lt_one.trans (A.fits.delayed _)) (by change A.clock.bar+G.slopeConstant * A.S.scale i ≤ A.clock.bar+G.slopeConstant * A.S.scale (i+1); exact add_le_add_right (mul_le_mul_of_nonneg_left ((OPE.scale_mono A.S).monotone i.le_succ) (Gauge.slopeConstant_pos hG).le) _ )
   obtain ⟨h0,h1,h2,h3,-⟩:= evident _ _ _ (he.trans (show Real.log (Real.log j) ≤ x from by linarith only [hh,Real.log_le_sub_one_of_pos hv]))
   exact ⟨h0,h3,hi.trans (hp _ h1 h2)⟩

/-- Below actual threshold, *constant* log power. -/
abbrev warm (A:Levels G) (k:ℕ):= A.clock.hatCoupling k * (Real.log (A.clock.hatBeta k))^(6:ℕ)
omit hG hp in
lemma warm_positive (A:Levels G) (k:ℕ): 0 < warm A k:=by
   exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (A.fits.delayed k)))) (pow_pos (Real.log_pos (A.fits.delayed k)) _)
omit hp in
lemma mon_pay (v:ℝ) : ∀ᶠ k:ℕ in atTop, Real.log (A.clock.hatBeta k)^ v ≤ A.clock.monitor k:=by
    have ht:=hat_rate A hG
    filter_upwards [(Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp ht)).eventually_ge_atTop (max 0 v)] with k hk
    let x:=Real.log (Real.log (A.clock.hatBeta k)); change max 0 v ≤ x at hk
    rw [Real.rpow_def_of_pos (Real.log_pos (A.fits.delayed _))]; exact Real.exp_monotone (show x*v ≤ x^2 by linarith only [mul_le_mul_of_nonneg_left ((le_max_right ..).trans hk) ((le_max_left ..).trans hk)])
omit hp in
lemma arrived (A:Levels G) : ∀ᶠ k:ℕ in atTop, warm A k ≤ A.clock.threshold k:=by
    filter_upwards [mon_pay (A:=A) hG 6] with k hk; unfold Calendar.threshold warm; refine mul_le_mul_of_nonneg_left ?_ ((inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (A.fits.delayed _)))).le)
    simpa using hk
lemma lit (p:ℕ) : ∀ᶠ k:ℕ in atTop, let b:= A.clock.hatBeta (k+1); let K:=(A.params (k+1)).clip; let L:= A.S.a k/A.S.a (k+1);∀ r:ℝ,b/2 ≤ r → Real.exp (L^4* Vac.treasury A (k+1)-r*K.linear*(warm A (k+1))^2) ≤ (b^p)⁻¹:=by
   have hs:Tendsto (fun i:ℕ=>i+1) atTop atTop:= tendsto_atTop_mono (f:=id) (fun i:ℕ=> i.le_succ) tendsto_id
   have ht:= (Real.tendsto_log_atTop.comp (hat_rate A hG)).comp hs
   filter_upwards [gate_price hG hp,ht.eventually_ge_atTop 2,ht.eventually_ge_atTop (p:ℝ)] with k hz hp hx; intro b K L r hr
   let x:= Real.log b; have h_x:0<x:= Real.log_pos (A.fits.delayed _); change 2 ≤ x at hp;change (p:ℝ)≤ x at hx
   have h0:0<L:=div_pos (A.S.a_pos _) (A.S.a_pos _); have he: L ≤ x:=by unfold L; rw [A.S.a_step,show A.S.a k / (A.S.a k /↑(A.S.block k).val)=(↑(A.S.block k).val:ℝ) from by have := A.S.a_pos k; field_simp]; exact hz.1
   let x':= Real.sqrt b; have hb:0<b:=zero_lt_one.trans (A.fits.delayed _); have hy : 0<x':=Real.sqrt_pos.mpr hb; have ht:warm A (k+1)= x'^(-1:ℤ)*x^6:=by simp [x',b,x,warm,Calendar.hatCoupling]
   have hs:x^11/2 ≤ r*K.linear*(warm A (k+1))^2 :=by
       have hx' : x⁻¹ ≤ K.linear:= (inv_anti₀ (inv_pos.mpr K.tail_pos) hz.2.1)|>.trans_eq (inv_inv ..)
       apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul hr hx' (inv_nonneg.mpr h_x.le) (hr.trans' (half_pos hb).le)) (sq_nonneg _)) -- order swapped?
       rw [ht,zpow_neg,zpow_one]; apply le_of_eq; field_simp; have hf : x'^2=b:=Real.sq_sqrt hb.le; rw [← hf]
   have hu: L^4*Vac.treasury A (k+1) ≤ x^7:=by
       apply (mul_le_mul_of_nonneg_left hz.2.2 (pow_nonneg h0.le 4)).trans; exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0.le he _) (pow_nonneg h_x.le _)).trans_eq (by ring)
   have hv:16 ≤ x^4:= (show (16:ℝ)=2^4 by norm_num)|>.trans_le (pow_le_pow_left₀ (by norm_num) hp _); have hw:x^2 ≤ x^7:= pow_le_pow_right₀ (by linarith only [hp]) (by omega)
   have hV : L^4 * Vac.treasury A (k+1)- r*K.linear*warm A (k+1)^2 ≤ -((p:ℝ) * Real.log b):=by change _ ≤ -(p*x); linarith only [hu,hs,hw,mul_le_mul_of_nonneg_right hx h_x.le,mul_le_mul_of_nonneg_right hv (pow_nonneg h_x.le 7),pow_nonneg h_x.le 7]
   exact (Real.exp_monotone hV).trans_eq (by rw [Real.exp_neg, Real.exp_nat_mul,Real.exp_log hb])
end YM.RG12SharpGram.Fence
