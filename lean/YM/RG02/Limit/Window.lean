import YM.RG02.Limit.Radial

/-!
Local Laplace identity on the analytic packet; not a real-domain
uniform Cauchy bound. Works on *any* eventually measurable inner sets S(t)
with the indicated collars. Only extracts the coefficients at a single
finite-order/demand and setup here, no uniform window shrink or remainder
in volume or charged derivatives. This allows identifying from actual Haar
slice integrals (discarded complement CONTROL not inferred). Use only with
zeroth positive gap proved for tested (augmented by scalar, if necessary).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Therm
open Filter Function MeasureTheory Set Metric
open PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Asym
open scoped ContDiff Topology Classical Real
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]

def Collars (r : ℝ)(S : ℝ→ Set E) := ∃ b>0, b≤r ∧ ∀ᶠ t in Tested.germ, MeasurableSet (S t) ∧ disc t b⊆ S t ∧ S t⊆ disc t r

omit [BorelSpace E] [FiniteDimensional ℝ E] in
lemma Collars.raise {S : ℝ→ Set E}{r u : ℝ}(h : Collars r S)(H : r≤u) : Collars u S := by
   obtain ⟨b,hb,hb',he⟩ := h
   refine ⟨b,hb,hb'.trans H,he.mono fun i hi => ⟨hi.1,hi.2.1,Set.Subset.trans hi.2.2 (preimage_mono (ball_subset_ball H))⟩⟩
omit [FiniteDimensional ℝ E] in
lemma Collars.body {r : ℝ}(h : 0<r) : Collars (E:=E) r fun t => disc t r := by
   refine ⟨r,h,le_rfl,Eventually.of_forall ?_⟩
   intro t
   refine ⟨?_,Set.Subset.rfl,Set.Subset.rfl⟩
   unfold disc
   exact isOpen_ball.measurableSet.preimage (continuous_const.smul continuous_id).measurable

section real
variable {K f : E→ℝ}

def Holds (f K : E→ℝ)(r : ℝ) := ∃ c>0,∃ C : ℝ, 0≤C ∧ ∀ (t:ℝ), 0<t→ ∀ u∈disc t r, ‖projection K f t u‖ ≤ C*bill 0 c u

lemma holds (H : Stationary f)(hk : ContinuousAt K 0)(hg : ∃ c>0,∀ u:E,c*‖u‖^2≤jet f 2 u) :
    ∃ r>0,Holds f K r := by
   obtain ⟨c,hc,h⟩ := hg
   obtain ⟨δ,B,hδ,hB,HB⟩ := H.dominated (half_pos hc)
   obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp (hk.norm.eventually (isOpen_Iio.mem_nhds (show ‖K 0‖ < ‖K 0‖+1 by linarith)))
   let C:=‖K 0‖+1
   refine ⟨min ε δ,lt_min hε hδ,c/2,half_pos hc,C,by dsimp only [C]; positivity,?_⟩
   intro t ht u hu
   have hU := (disc_mem ht.le _ u).mp hu
   have heU : ‖K (t • u)‖≤C := le_of_lt (he (a:=t • u) (ball_subset_ball (min_le_left ..) hu))
   have hd := (HB u t ht (hU.le.trans (min_le_right ..))).2
   rw [projection_eq,norm_mul,Real.norm_eq_abs (Real.exp _),abs_of_pos (Real.exp_pos _)]
   apply mul_le_mul heU _ (Real.exp_pos _).le ((norm_nonneg _).trans heU)
   unfold bill; rw [pow_zero,one_mul]; apply Real.exp_le_exp.mpr
   have hh := h u; unfold higher at hd
   rw [Real.norm_eq_abs] at hd; linarith [(abs_le.mp hd).2]

variable (μ : Measure E)[μ.HasTemperateGrowth]

section tail
variable {r : ℝ}
variable (h : Holds f K r) (hf : Measurable f) (hk : Measurable K)
include h μ
include hf hk
lemma pays {t : ℝ}(ht : 0<t) : IntegrableOn (projection K f t) (disc t r) μ := by
   obtain ⟨c,hc,C,hC,H⟩ := h; refine ((bill_integrable μ 0 hc).const_mul C).integrableOn.mono' (projection_meas hk hf t|>.aestronglyMeasurable) ?_
   filter_upwards [ae_restrict_mem (disc_meas ..)] with u hu; exact H t ht u hu

omit hf hk in
lemma annulus {b : ℝ}(hb : 0<b)(n : ℕ) : ∃ D : ℝ,0≤D ∧ ∀ t>0,∀ S : Set E, MeasurableSet S →
      S⊆ disc t r → S⊆(disc t b)ᶜ → ‖∫ u in S,projection K f t u ∂μ‖ ≤ D*t^n := by
   obtain ⟨c,hc,C,hC,H⟩ := h
   have hv := bill_integrable μ n hc
   let A:= fun u : E => C * b⁻¹^n * bill n c u
   have HA : ∀ u, 0 ≤ A u:= fun u=> by unfold A; have := bill_nonneg n c u; positivity
   refine ⟨∫ u, A u ∂μ, integral_nonneg HA, fun t ht S hS hs hs' =>?_⟩
   have hx : Integrable (fun u=> A u*t^n) μ := (hv.const_mul _).mul_const _
   apply le_trans _ ((MeasureTheory.setIntegral_le_integral (s:=S) hx (ae_of_all _ fun u=>mul_nonneg (HA u) (pow_nonneg ht.le n))).trans_eq (integral_mul_const ..))
   apply norm_integral_le_of_norm_le hx.integrableOn; filter_upwards [ae_restrict_mem hS] with u hu
   have hh : b≤t*‖u‖ := le_of_not_gt fun hg => hs' hu ((disc_mem ht.le b u).mpr hg)
   refine (H t ht u (hs hu)).trans ?_
   have hU : 1≤b⁻¹*t*(Radial.zone (E:=E)).w u := by
      rw [mul_assoc,inv_mul_eq_div, le_div_iff₀ hb,one_mul]; refine hh.trans ?_; apply mul_le_mul_of_nonneg_left _ ht.le; simp [Radial.zone]
   refine (le_mul_of_one_le_right (mul_nonneg hC (bill_nonneg ..)) (one_le_pow₀ (n:=n) hU)).trans_eq ?_
   unfold A bill; simp [mul_pow]; ring
end tail

lemma runway {μ : Measure E}[μ.HasTemperateGrowth] {f:E→ℝ}(H : Stationary f)
    (hg : ∃ c>0,∀ u:E,c*‖u‖^2≤jet f 2 u)(hf : Measurable f){K:E→ℝ}(hk : ContDiffAt ℝ ∞ K 0)(hm : Measurable K)
    {r : ℝ}(h : Holds f K r) {S : ℝ→Set E}(hy : Collars r S) :
   Aspiration (fun t=> ∫ u in S t,projection K f t u ∂μ) (fun k=> moment μ K f k) := by
   intro n
   obtain ⟨δ,hδ,H⟩ := H.rescale_estimate μ hk hm hf hg n
   obtain ⟨b,hb,hb',he⟩ := hy
   let η:=min b (δ/2); have hη:0<η := lt_min hb (half_pos hδ)
   have h1 : η ≤ b:= min_le_left ..
   have h2 : η<δ := lt_of_le_of_lt (min_le_right ..) (half_lt_self hδ)
   obtain ⟨C,hC⟩ := H η ⟨hη,h2⟩
   obtain ⟨D,hD,H'⟩ := annulus μ h hη (n+1)
   refine ⟨|C|+D,by positivity,?_⟩
   filter_upwards [hC,he,Tested.eventually_pos] with t ht he' hpos
   rw [add_mul]
   let A := S t
   let B := disc (E:=E) t η
   have hB : MeasurableSet B := disc_meas ..
   obtain ⟨hA,hL,hP⟩ := he'
   have hv : B ⊆ S t := Set.Subset.trans (preimage_mono (ball_subset_ball h1)) hL
   have hq := (pays μ h hf hm hpos).mono_set hP
   have hu : B ∪ (S t \ B) = S t := Set.union_sdiff_cancel hv
   let e := peval (fun k => moment μ K f k) n t
   change ‖(∫ u in S t,projection K f t u ∂μ)-e‖≤_
   rw [← hu,setIntegral_union (by grind) (hA.diff hB) (hq.mono_set hv) (hq.mono_set Set.sdiff_subset),show (∫ u in B,_ ∂μ)+_-e=((∫ u in B,projection K f t u ∂μ)-e)+∫ u in S t \ B,projection K f t u ∂μ by abel]
   apply (norm_add_le ..).trans; apply add_le_add _ (H' t hpos (S t \ B) (hA.diff hB) (Set.Subset.trans Set.sdiff_subset hP) (fun u hu => hu.2))
   exact ht.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hpos.le _))
end real
end YM.RG02.Therm
