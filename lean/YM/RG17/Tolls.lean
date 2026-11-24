import YM.Trace.NoFock

/-!
# Adapter to the non-free test using only a sparse positive theta reading

Need only Tempered info under existing domain in Trace. Here uniform spectral
estimates on POSITIVE scalar (unmixed) measure. Sparse not enough for exact
Schwartz UP TO log bills; argue just to distribute bare order bound
(no log, hence **zero** limit there). Enough to rule out relevant powers
from the NoFock proof. No new cone, continuation or boundary premises.
Do NOT use this as a statement of Spectral log-law for physical theory.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.RG17.TracePay
open Function Set Filter MeasureTheory Boundary Trace Complex
open scoped Topology BigOperators ContDiff ENNReal NNReal Matrix.Norms.Frobenius
variable {μ:Measure E4}

-- normalized backwards. at weight r^{-n}
def watts (μ:Measure E4) (n:ℕ)(r:ℝ):= ENNReal.ofReal ((r⁻¹)^n) • Measure.map (fun x:E4=> r⁻¹ • x) μ
lemma powerLaw {n:ℕ}{A:ℝ≥0∞} (h:Growth μ A n)(r:ℝ)(hr:r≥1) : Growth (watts μ n r) A n:=by
   have hp:0<r:=zero_lt_one.trans_le hr
   have hq:=inv_pos.mpr hp
   intro s hs; have hs0:0<s:=zero_lt_one.trans_le hs
   rw [watts,Measure.smul_apply,smul_eq_mul,Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
   have ht : (fun (x:E4)=>r⁻¹ • x) ⁻¹' Metric.closedBall 0 s ⊆ Metric.closedBall 0 (s*r):=by
       intro x hx
       rw [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg hq.le, inv_mul_eq_div] at hx
       rw [Metric.mem_closedBall,dist_zero_right]; exact (div_le_iff₀ hp).mp hx
   calc _ ≤ _ := mul_le_mul_of_nonneg_left ((measure_mono ht).trans (h (s*r) (one_le_mul_of_one_le_of_one_le hs hr))) zero_le
        _ = _:= by
          rw [mul_comm (ENNReal.ofReal _),mul_assoc, ← ENNReal.ofReal_pow (mul_nonneg hs0.le hp.le), ← ENNReal.ofReal_mul (pow_nonneg (mul_nonneg hs0.le hp.le) _), ← mul_pow, mul_inv_cancel_right₀ hp.ne', ENNReal.ofReal_pow hs0.le]
lemma watts_integral (μ:Measure E4){r:ℝ}(hr:0<r)(n:ℕ){E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] (f:E4→E) : (∫ x,f x ∂watts μ n r)=(r⁻¹)^n • ∫ x,f (r⁻¹ • x) ∂μ:=by
    rw [watts,MeasureTheory.integral_smul_measure ..,ENNReal.toReal_ofReal (pow_nonneg (inv_pos.mpr hr).le _)]
    exact congr_arg _ ((scaleCLE r hr.ne').toHomeomorph.measurableEmbedding.integral_map ..)
lemma watts_heat (μ:Measure E4){r:ℝ}(hr:0<r)(n:ℕ) : (∫ x:E4,Real.exp (-time x) ∂watts μ n r) = (r⁻¹)^n * ∫ x,Real.exp (-(r⁻¹)*time x) ∂μ:=by
    rw [watts_integral μ hr]; exact congr_arg ((r⁻¹)^n • ·) (integral_congr_ae (ae_of_all _ fun i=> by simp [time]))
lemma positively {r:ℝ}(hr:0<r)(n:ℕ) (h:μ Mink.coneᶜ=0): ∀ᵐ x∂watts μ n r,x∈ Mink.cone:=by
    apply ae_iff.mpr; change watts μ n r Mink.coneᶜ=0
    rw [watts,Measure.smul_apply, Measure.map_apply (by fun_prop) Mink.closed_cone.measurableSet.compl, measure_mono_null _ h,smul_zero]
    exact fun p hp hu=>hp (by simpa [Mink.cone,inv_pos.mpr hr,abs_of_pos hr,norm_smul] using! hu)
private lemma totalW {n A}(h:Growth μ A n)(ha:A<⊤): (∫ p, (Trace.weight (n+1) p)⁻¹ ∂μ) ≤ A.toReal * 2^(n+1):=by
   have ht : ∀ᵐ p∂μ, 0≤ (Trace.weight (n+1) p)⁻¹:= ae_of_all _ fun p=> inv_nonneg.mpr (Trace.weight_pos _ _).le
   rw [integral_eq_lintegral_of_nonneg_ae ht (by unfold Trace.weight; fun_prop)]
   exact (ENNReal.toReal_mono (by finiteness : 2^(n+1)*A ≠ ⊤) (h.total_weight μ A n)).trans_eq (by simp [ENNReal.toReal_mul, ENNReal.toReal_pow,mul_comm])
lemma finalOn {P:ℕ}(A:ℝ≥0∞) (ha:A<⊤)
    (H:∀ᶠ r in atTop, μ (Metric.closedBall 0 r) ≤ A * (ENNReal.ofReal r)^P):
    ∃ B:ℝ≥0∞,B<⊤∧Growth μ B P:=by
   obtain ⟨b,hb⟩:= eventually_atTop.mp H
   let c:=max 1 b; have hc:1≤c:=le_max_left ..; have hz:∃ B:ℝ≥0∞, B<⊤∧μ (Metric.closedBall 0 c) ≤ B := ⟨_,ENNReal.mul_lt_top ha (by finiteness),hb _ (le_max_right ..)⟩
   obtain ⟨B,hB,h⟩:=hz; refine ⟨max A B, max_lt ha hB,fun r hr=>?_⟩
   rcases le_or_gt b r with he|he; · apply (hb _ he).trans; exact mul_le_mul_of_nonneg_right (le_max_left ..) zero_le
   have hv : (1:ℝ≥0∞) ≤ ENNReal.ofReal r:=by exact_mod_cast (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr)
   exact (measure_mono (Metric.closedBall_subset_closedBall (he.le.trans (le_max_right ..)))).trans (h.trans ((le_max_right ..).trans (le_mul_of_one_le_right zero_le (one_le_pow₀ hv))))
lemma inferGrowth (t:Tempered μ) {p:ℕ} {R:ℝ} (h:μ Mink.coneᶜ=0) (he:∀ᶠ r in atTop,
    r⁻¹^p * ∫ x,Real.exp (-(r⁻¹)* time x)∂μ≤ R) : ∃ B:ℝ≥0∞,B<⊤∧Growth μ B p:=by
    apply finalOn (ENNReal.ofReal (R / Real.exp (-1))) (by finiteness)
    filter_upwards [he,eventually_gt_atTop (0:ℝ)] with r ht hp
    let g(x:E4):=Real.exp (-(r⁻¹)*time x)
    let V:= ∫ x,g x ∂μ; let e:= Real.exp (-1)
    have hg : Integrable g μ:= t.integrable_exp μ h (inv_pos.mpr hp)
    have hn (x:E4):0 ≤ g x := Real.exp_nonneg _
    have hb: 0 < e := Real.exp_pos _
    calc
      _ ≤ μ {x: E4 | ENNReal.ofReal e ≤ (ENNReal.ofReal ∘ g) x} := measure_mono ?_
      _ ≤ ENNReal.ofReal (V /e) := ?_
      _ ≤ _ := ?_
    · intro x hx; refine ENNReal.ofReal_le_ofReal (Real.exp_monotone ?_)
      have hu:time x≤r := (le_abs_self _).trans ((Trace.norm_time x).trans (by simpa only [dist_zero_right] using Metric.mem_closedBall.mp hx))
      rw [neg_mul,inv_mul_eq_div]; apply neg_le_neg; exact (div_le_one hp).mpr hu
    · apply le_trans (meas_ge_le_lintegral_div (f:=ENNReal.ofReal ∘ g) (μ:=μ) (by unfold g; fun_prop) (by positivity) (by finiteness)); unfold V
      rw [ENNReal.ofReal_div_of_pos hb, ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ hn)] ; exact le_rfl
    have hv : 0 ≤ V:= integral_nonneg hn
    have ht' : (r⁻¹)^p*V ≤ R:=ht
    have hx : 0 ≤ R := (mul_nonneg (pow_nonneg (inv_pos.mpr hp).le _) hv).trans ht'
    have hr : V ≤ R*r^p:= (div_le_iff₀ (pow_pos hp p)).1 (by rwa [inv_pow,inv_mul_eq_div] at ht')
    rw [← ENNReal.ofReal_pow (hp:=hp.le), ← ENNReal.ofReal_mul (show 0≤ _ from div_nonneg hx hb.le)]
    exact ENNReal.ofReal_le_ofReal ((div_le_div_of_nonneg_right hr hb.le).trans_eq (by unfold e; ring))

lemma growthHeat {n:ℕ}{A:ℝ≥0∞}(h:Growth μ A n)(ha:A<⊤)(hp:μ Mink.coneᶜ=0):
    ∃ B≥(0:ℝ), ∀ r:ℝ, 1 ≤ r → r⁻¹^n * ∫ x,Real.exp (-(r⁻¹)* time x)∂μ ≤ B:=by
   obtain ⟨c,hc,he⟩:= Trace.exp_cost zero_lt_one (n+1)
   refine ⟨c*(A.toReal*2^(n+1)),by positivity,fun r hr=>?_⟩
   let M:=watts μ n r; have hr':=zero_lt_one.trans_le hr
   have hT:= powerLaw h r hr
   have hx:Tempered M:= ⟨_, A.toReal, (ENNReal.ofReal_toReal ha.ne).symm ▸ hT⟩
   have hC:M Mink.coneᶜ=0:= ae_iff.mp (positively hr' n hp)
   rw [← watts_heat μ hr']; change (∫ x:E4,Real.exp (-time x)∂M)≤ _
   refine (integral_mono_ae (by simpa only [neg_mul,one_mul] using! hx.integrable_exp M hC zero_lt_one) ((hT.integrable_weight _ ha).const_mul c) ?_).trans ?_
   · filter_upwards [positively hr' n hp] with i hi
     have hp:= he i hi; rw [div_eq_mul_inv] at hp; simp only [neg_mul,one_mul] at hp
     exact (le_mul_of_one_le_left (Real.exp_nonneg _) (le_add_of_nonneg_right (abs_nonneg _))).trans hp
   rw [MeasureTheory.integral_const_mul]; exact mul_le_mul_of_nonneg_left (totalW hT ha) hc
end YM.RG17.TracePay
