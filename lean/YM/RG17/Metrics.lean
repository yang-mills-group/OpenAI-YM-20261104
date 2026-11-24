import YM.RG17.Tolls
/-! Bare scaling `r^-n` law **alone**, no non-freeness conclusion yet. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.RG17.TracePay
open Function Set Filter MeasureTheory Boundary Trace Complex
open scoped Topology BigOperators ContDiff ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
variable {μ:Measure E4} {H:Hilbert} {A:ℝ≥0∞}{n:ℕ}
    {v:Test4→ H}(hq: FieldsNorm μ v)

include hq
lemma normsMeter (n:ℕ){r:ℝ}(hr:r>1)(p: Test4) : (∫ x,normTest p x ∂watts μ n r)=↑((r⁻¹)^n*‖v (normalized p r)‖^2:ℝ):=by
    have hx:= scaled_vac_norm v hq p hr
    rw [rescale_integral μ hr] at hx; push_cast at hx
    have hr0:=zero_lt_one.trans hr
    have he : (∫ x,normTest p ((r⁻¹:ℝ) • x) ∂μ)= (‖v (normalized p r)‖:ℂ)^2:=by
       rw [Complex.real_smul] at hx; exact mul_left_cancel₀ (by exact_mod_cast (positive_weight hr).ne') hx.symm
    rw [watts_integral μ hr0,he,Complex.real_smul]; push_cast; rfl
lemma powerTest (hg:Growth μ A n) (ht:A<⊤)(p:Test4) : ∃ C : ℝ, ∀ᶠ r in atTop,
   r⁻¹^n * ‖v (normalized p r)‖^2 ≤ C:=by
   let f:=normTest p
   refine ⟨(orderCost f (n+1)*2^(n+1))*(A.toReal*2^(n+1)),?_⟩
   filter_upwards [eventually_gt_atTop (1:ℝ)] with r hr
   have h:0 ≤ r⁻¹^n*‖v (normalized p r)‖^2:= mul_nonneg (by positivity) (sq_nonneg _)
   have hh:= (powerLaw hg r hr.le).test_abs ht (normTest p); rw [normsMeter hq n hr p,Complex.norm_real,Real.norm_of_nonneg h] at hh; exact hh

-- sparse compacta. Norm density nonnegative. Use inverse stability via radius, not analytic
-- continuation beyond older `Trace`.
omit hq in
lemma lowBill : ∃ p : Test4, CC p ∧ ∀ x:E4, ‖x‖ ≤ 1 → ‖normTest p x‖ ≥ 1/4:=by
   let v:= initial E4
   have hv(ε:ℝ)(he:0<ε): ∀ᶠ x:E4 in 𝓝 0, ‖plus v x-1‖< ε:=by
      have h:(plus v) 0=1:=plus_initial ..
      have hC:=((plus v).continuous.continuousAt (x:=0)).tendsto; rw [h] at hC
      simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp hC ε he
   obtain ⟨δ,hδ,ht⟩:= Metric.mem_nhds_iff.mp (hv (1/2) (by norm_num)); let c:=2/δ
   have hc:0<c:=by unfold c; positivity
   refine ⟨normalized v c,normalized_CC initial_CC _, fun x hx=>?_⟩
   have h:=ht (show c⁻¹ • x∈ Metric.ball (0:E4) δ from Metric.mem_ball.mpr (by rw [dist_zero_right,norm_smul, Real.norm_of_nonneg (inv_pos.mpr hc).le]; unfold c; field_simp; linarith only [hx]))
   change ‖plus v (c⁻¹ • x)-1‖<1/2 at h
   rw [normTest_value,Function.comp_apply, plus_normalized v hc, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]; have hx':=norm_sub_norm_le (1:ℂ) (plus v (c⁻¹ • x)); rw [norm_sub_rev,norm_one] at hx'; nlinarith only [hx',h]
lemma lowerTest {p : Test4}(hP : ∀ x:E4, ‖x‖ ≤ 1→ ‖normTest p x‖ ≥ 1/4) (t:Tempered μ) : (∃ C : ℝ, 0 ≤ C∧ ∀ r≥1,‖v (normalized p r)‖^2 ≤ C*r^n) →
   ∃ B:ℝ≥0∞, B<⊤ ∧ ∀ᶠ r in atTop, μ (Metric.closedBall 0 r) ≤ B*(ENNReal.ofReal r)^n := by
   rintro ⟨C,hC,h⟩
   refine ⟨ENNReal.ofReal (4*C), ENNReal.ofReal_lt_top,?_⟩
   filter_upwards [eventually_gt_atTop (1:ℝ)] with r hr
   let f:=normalized p r
   let q(x:E4):ℝ:= ‖normTest f x‖
   have hx:∀ x:E4, normTest f x=(q x:ℂ):=by intro x; simp only [q,normTest_value,Function.comp_apply,norm_real,Real.norm_of_nonneg (sq_nonneg _)]
   have hN: (∫ x,q x∂μ)= ‖v f‖^2:= by
       apply Complex.ofReal_injective
       have he:=hq f f
       rw [inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (v f)] at he
       rw [← integral_complex_ofReal]; push_cast; refine Eq.trans (integral_congr_ae (ae_of_all _ fun i=>?_)) he.symm
       change (↑(q i):ℂ)=(starRingEnd ℂ (_) * _); rw [← hx,normTest,Probe.sews,Probe.bar_at]; rfl
   have hr0 := zero_lt_one.trans hr
   have hp (x:E4)(hx:‖x‖ ≤ r) : 1/4 ≤ q x :=by
       have h := hP (r⁻¹ • x) (by rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hr0).le]; exact (mul_le_mul_of_nonneg_left hx (inv_pos.mpr hr0).le).trans_eq (inv_mul_cancel₀ hr0.ne'))
       simpa only [q,f,normTest_value,Function.comp_apply,plus_normalized _ hr0] using! h
   let b:=ENNReal.ofReal (1/4:ℝ)
   have ht := meas_ge_le_lintegral_div (f:=ENNReal.ofReal ∘ q) (μ:=μ) (by unfold q; fun_prop) (by unfold b; positivity : b≠0) (by unfold b; finiteness : b≠⊤)
   calc
     _ ≤ μ {x| b ≤ (ENNReal.ofReal ∘ q) x} := measure_mono (fun i hi=> ENNReal.ofReal_le_ofReal (hp i (by simpa using hi)))
     _ ≤ ENNReal.ofReal (‖v f‖^2 / (1/4:ℝ)) := by
       rw [← hN,ENNReal.ofReal_div_of_pos (by norm_num),ofReal_integral_eq_lintegral_ofReal ((t.integrable μ (normTest f)).norm) (ae_of_all _ (fun i=>norm_nonneg _))]; exact ht
     _ ≤ _ := by
       rw [← ENNReal.ofReal_pow hr0.le, ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hC)]; exact ENNReal.ofReal_le_ofReal (by linarith only [h r hr.le])
omit hq
lemma sparseSch {filt:Filter ℝ} (ht:filt≤atTop) (hg:Growth μ A n)(hm:A<⊤)(hv:μ Mink.coneᶜ=0)(h:Tendsto
     (fun r:ℝ=> r⁻¹^n * ∫ x,Real.exp (-(r⁻¹)*time x) ∂μ) filt (𝓝 0)) (p:Probe E4):
     Tendsto (fun r=> ∫ x,p x∂watts μ n r) filt (𝓝 0):=by
   let s := fun r:ℝ=>watts μ n r
   have hG : ∀ᶠ r:ℝ in filt, Growth (s r) A n:=(eventually_ge_atTop (1:ℝ)|>.filter_mono ht).mono fun r hr=>powerLaw hg r hr
   let K:=(2:ℝ)^(n+1) * (A.toReal * 2^(n+1))
   have hK: K≥0:=by unfold K; positivity
   apply Metric.tendsto_nhds.2; intro δ hδ
   obtain ⟨r,hR⟩:= ((continuous_orderCost (V:=E4) (n+1)).continuousAt.tendsto.comp ((cutTest_limit p).sub_const p)).eventually (gt_mem_nhds (a:=δ/(2*(K+1))) (by simp only [orderCost,Probe.size, sub_self,map_zero,zero_add]; positivity))|>.exists
   let q:= Trace.cutTest p r
   -- domination on compact momentum
   let f(x:E4):= Real.exp (-time x)
   have hz: HasCompactSupport (fun x:E4=> ‖q x‖/f x) := by simp_rw [div_eq_mul_inv]; exact (cutTest_CC p r).norm.mul_right
   obtain ⟨D,hD⟩ := (hz.isCompact_range (q.continuous.norm.div (by unfold f; fun_prop) (fun _=> (Real.exp_pos _).ne'))).bddAbove
   have hc x : ‖q x‖ ≤ D*f x:= (div_le_iff₀ (Real.exp_pos _)).mp (hD (Set.mem_range_self _))
   have he:Tendsto (fun r=> ∫ x,q x∂s r) filt (𝓝 0):=by
       apply squeeze_zero_norm' _ (f:=fun r=> ∫ x,q x∂s r) (a:= fun r:ℝ=> D*(r⁻¹^n*∫ x,Real.exp (-(r⁻¹)*time x) ∂μ)) (by simpa only [mul_zero] using h.const_mul D)
       filter_upwards [eventually_ge_atTop (1:ℝ)|>.filter_mono ht,hG] with r hr hR
       have hx:=zero_lt_one.trans_le hr
       have hh:Tempered (s r):= ⟨_,A.toReal,(ENNReal.ofReal_toReal hm.ne).symm ▸ hR⟩
       have hf:Integrable f (s r):= by
          have h: s r (Mink.coneᶜ)=0:=ae_iff.mp (positively hx n hv)
          simpa only [f,neg_mul, one_mul] using! hh.integrable_exp (s r) h zero_lt_one
       rw [← watts_heat μ hx]; exact (MeasureTheory.norm_integral_le_of_norm_le (hf.const_mul D) (ae_of_all _ hc)).trans_eq (integral_const_mul ..)
   filter_upwards [hG, (Metric.tendsto_nhds.mp he (δ/2) (half_pos hδ))] with i hi he
   rw [dist_zero_right] at he ⊢
   have hP : ‖(∫ x,q x∂s i)-(∫ x,p x∂s i)‖ ≤ δ/2:= by
       rw [← MeasureTheory.integral_sub (hi.integrable_schwartz hm _) (hi.integrable_schwartz hm _)]
       refine (hi.test_abs hm (q-p)).trans ?_
       rw [mul_assoc]; have h:orderCost (q-p) (n+1)≤δ/(2*(K+1)):= hR.le
       refine (mul_le_mul h (show K ≤ K+1 from (lt_add_one K).le) hK (by positivity)).trans (le_of_eq ?_)
       field_simp
   linarith only [he,hP,norm_sub_rev (∫ x,q x∂s i) (∫ x,p x∂s i), norm_sub_norm_le (∫ x,p x∂s i) (∫ x,q x∂s i)]
end YM.RG17.TracePay
