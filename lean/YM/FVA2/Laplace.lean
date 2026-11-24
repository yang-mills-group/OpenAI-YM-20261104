import YM.FormalOPE.RG10.StationaryMarks.Asympt

/-!
# Local (germ only) Laplace coefficients invariant under change of slice variables

One auxiliary finite system at a time. Absolutely NO uniform analytic estimates here.
No appeal to global measurability/suppression of any other saddle. Important because the
MS list jets can use a function defined globally only to represent a germ of a stencil;
a local coefficients theorem must not require a strong condition from the analytic task.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GermLaplace
open Filter Function Set Metric PertExtension FormalOPE.RG10 PertExtension.Series.Radial PertExtension.Series.Tested
open FormalOPE.RG10.Inherit MeasureTheory Finset
open scoped Topology ContDiff BigOperators Classical

variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E]
variable (F f K : E → ℝ) {X Y : E→ℝ}

theorem local_stat (h : X=ᶠ[𝓝 0] Y) (hx : PertExtension.Series.Radial.Stationary X) : PertExtension.Series.Radial.Stationary Y where
   smooth := hx.smooth.congr_of_eventuallyEq h.symm
   base0 := h.eq_of_nhds ▸ hx.base0
   base1 x := by rw [← same_jet h]; exact hx.base1 x

lemma equal_jet (h:X=ᶠ[𝓝 0] Y) : jet X=jet Y := funext (fun i=> funext (same_jet h i))

lemma equal_layers (h:X=ᶠ[𝓝 0] Y) : layers X=layers Y := by funext n x; unfold layers; rw [equal_jet h]

lemma priceProof (H : ContDiffAt ℝ ω F 0) : ∀ᶠ x in 𝓝 (0:E), ContinuousAt F x := (H.eventually (by simp)).mono fun _ h=> h.continuousAt

abbrev Gap (F : E→ℝ) := ∃ c : ℝ, 0 < c ∧ ∀ x,c*‖x‖^2 ≤ jet F 2 x

variable [FiniteDimensional ℝ E]
lemma near_floor {F:E→ℝ} (HF : PertExtension.Series.Radial.Stationary F) (h:Gap F):
    ∃ c:ℝ, 0<c ∧ ∀ᶠ x in 𝓝 (0:E), c*‖x‖^2 ≤ F x:= by
  obtain ⟨c,hc,H⟩:=h; obtain ⟨δ,M,hd,hm,h⟩:= deposition F 2 HF.smooth
  refine ⟨c/2, half_pos hc,?_⟩
  filter_upwards [Metric.ball_mem_nhds (0:E) hd, Metric.ball_mem_nhds (0:E) (show (0:ℝ)<(c/2)/(M+1) by positivity)] with x hx he
  have hp := h x (1:ℝ) one_pos (by simpa using (show _ from (mem_ball_zero_iff.mp hx)).le)
  have hh : ‖x‖*(M+1)<c/2 := (lt_div_iff₀ (show 0<M+1 by linarith)).mp (mem_ball_zero_iff.mp he)
  rw [show Series.Zone.eval (jet F) 2 1 x=jet F 2 x from ?_] at hp; swap; · simp [Series.Zone.eval,sum_range_succ,HF.base1,HF.base0]
  simp only [one_smul,Real.norm_eq_abs, one_pow,mul_one] at hp; have H₁: ‖x‖*M≤ c/2 := le_trans (by gcongr; linarith) hh.le
  have hp₁ := (abs_le.mp hp).1; calc
    _ ≤ c * ‖x‖^2 - M*‖x‖^(2+1) := by nlinarith [mul_le_mul_of_nonneg_right H₁ (sq_nonneg ‖x‖)]
    _ ≤ jet F 2 x - M*‖x‖^(2+1):= by gcongr; exact H x
    _ ≤ _:= by linarith

variable [MeasurableSpace E][BorelSpace E] (μ : Measure E)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma local_moments (h:X=ᶠ[𝓝 0] Y) (he:K=ᶠ[𝓝 0] f) : moment μ K X= moment μ f Y:= by
  funext i; unfold moment normTerm integrandSeries kernel; simp_rw [equal_layers h,equal_jet h,equal_jet he]

variable [μ.IsAddHaarMeasure] {F f K}

private def observable (t:ℝ) (K F : E→ℝ) (x:E) := K x * Real.exp (-F x / t^2)

private def sector (μ:Measure E)(K F : E→ℝ)(U:Set E) (t:ℝ):= (t^Module.finrank ℝ E)⁻¹ * ∫ x in U, observable t K F x ∂μ

private lemma sector_ball (t:ℝ)(ht:0<t)(r:ℝ)(K F:E→ℝ): sector μ K F (ball 0 r) t = partialSum μ K F r t:= by
   let A:Set E:=ball 0 r; let D:=disc (E:=E) t r; let f:=observable t K F
   let g:=A.indicator f; have he x: g (t • x)= D.indicator (fun x=>f (t • x)) x:= by by_cases h:t • x∈A; rw [show g (t • x)=f _ from indicator_of_mem h _,indicator_of_mem (s:=D) h]; rw [show g (t • x)=0 from indicator_of_notMem h _,indicator_of_notMem (s:=D) h]
   have hg:= Measure.integral_comp_smul_of_nonneg μ g t (hR:=ht.le)
   simp only [he] at hg; unfold g at hg; rw [integral_indicator (s:=A) Metric.isOpen_ball.measurableSet, integral_indicator (s:=D) (disc_meas ..), smul_eq_mul] at hg
   unfold partialSum; simp_rw [projection_eq]; exact hg.symm

omit [FiniteDimensional ℝ E] in
private lemma outside_patch (t : Set E) (hp:IsCompact t)(hc:ContinuousOn K t){v:ℝ}(hv:0<v)(h:∀ x∈t,v ≤ F x)(k:ℕ) :
    Bill k (sector μ K F t) := by
   obtain ⟨c,hc⟩:= hp.exists_bound_of_continuousOn hc
   obtain ⟨R,hr,H⟩:= StationaryMarks.rapid hv (Module.finrank ℝ E) k
   refine ⟨(|c| * μ.real t)*R, by positivity, ?_⟩
   filter_upwards [eventually_pos] with a ha
   let D := |c| * Real.exp (-v/a^2); have hD:0≤D:=by positivity
   have he: ‖∫ x in t, observable a K F x ∂μ‖ ≤ D*μ.real t := by
       let L := μ.restrict t; have : IsFiniteMeasure L:= ⟨by unfold L; simp [hp.measure_lt_top]⟩
       apply (norm_integral_le_of_norm_le (μ:=L) (integrable_const D) ?_).trans_eq
       · rw [integral_const]; unfold L Measure.real; rw [Measure.restrict_apply_univ, smul_eq_mul,mul_comm]
       filter_upwards [ae_restrict_mem (μ:=μ) hp.measurableSet] with x hx
       rw [observable,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]; exact mul_le_mul ((hc x hx).trans (le_abs_self c)) (Real.exp_le_exp.mpr (by grw [h x hx])) (Real.exp_pos _).le (abs_nonneg c)
   rw [sector,norm_mul, Real.norm_of_nonneg (by positivity:(0:ℝ) ≤ (a^Module.finrank ℝ E)⁻¹)]
   refine (mul_le_mul_of_nonneg_left he (by positivity)).trans ?_; unfold D; obtain he:= H a ha; calc
    _ = |c| * μ.real t*((a^Module.finrank ℝ E)⁻¹ * Real.exp (-v/a^2)) := by ring
    _ ≤ _ := by rw [mul_assoc (|c| * μ.real t) R (a^k)]; gcongr

private lemma update (U : Set E) (h : IsCompact U) (hm:U∈𝓝 (0:E)) (hK:ContinuousOn K U) (hF:ContinuousOn F U)
    (X: PertExtension.Series.Radial.Stationary F) (Y:Gap F) (hf:ContDiffAt ℝ ∞ K 0) (n:ℕ):
    ∃ δ : ℝ, 0<δ ∧ ∀ (r:ℝ),r∈Set.Ioo 0 δ→ ball 0 r ⊆ U ∧ Bill (n+1) (sector μ K F (ball 0 r) -peval (moment μ K F) n) := by
   let F':=U.indicator F; let K':=U.indicator K
   have he: F'=ᶠ[𝓝 0] F := Filter.eventuallyEq_iff_exists_mem.mpr ⟨U,hm,fun x hx=> Set.indicator_of_mem hx _⟩ -- shape
   have hv: K'=ᶠ[𝓝 0] K := Filter.eventuallyEq_iff_exists_mem.mpr ⟨U,hm,fun x hx=> Set.indicator_of_mem hx _⟩
   obtain ⟨d,hd,H⟩:= PertExtension.Series.Radial.Stationary.rescale_estimate μ (local_stat he.symm X) (hf.congr_of_eventuallyEq hv) (ContinuousOn.measurable_piecewise hK continuousOn_const h.measurableSet)
       (ContinuousOn.measurable_piecewise hF continuousOn_const h.measurableSet) (show Gap F' from by unfold Gap; rw [equal_jet he]; exact Y) n
   obtain ⟨b,hb,hB⟩:= Metric.mem_nhds_iff.mp hm; refine ⟨min d b,lt_min hd hb, fun r hr =>?_⟩; have hk: ball 0 r⊆U:= Set.Subset.trans (Metric.ball_subset_ball (hr.2.le.trans (min_le_right ..))) hB
   obtain ⟨c,hc⟩:=H r ⟨hr.1, hr.2.trans_le (min_le_left ..)⟩
   refine ⟨hk,|c|,abs_nonneg _,?_⟩
   filter_upwards [hc, eventually_pos] with t ht hw
   have hρ : sector μ K F (ball 0 r) t=partialSum μ K' F' r t:= by
       rw [← sector_ball μ t hw ]; unfold sector; congr 1; exact setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun x hx=> by simp [observable,K',F',hk hx]
   rw [local_moments K K' μ he hv] at ht -- arguments order
   rw [Pi.sub_apply,hρ]
   exact ht.trans (by gcongr; exact le_abs_self _)

lemma local_bound {c:ℝ}(hc:0<c)(U:Set E)(h:IsCompact U)(hm:U∈𝓝 (0:E)) (hC:∀ x∈U,c*‖x‖^2 ≤ F x)(hK:ContinuousOn K U)(hF:ContinuousOn F U)
    (X: PertExtension.Series.Radial.Stationary F) (Y:Gap F) (hf:ContDiffAt ℝ ∞ K 0): Aspiration (sector μ K F U) (moment μ K F) := by
   intro n; obtain ⟨δ,hδ,H⟩:=GermLaplace.update μ U h hm hK hF X Y hf n; let r:=δ/2; have hr:0<r:=half_pos hδ; let T:=U \ ball 0 r
   obtain ⟨ht,hu⟩:= H r ⟨hr,half_lt_self hδ⟩
   have hcT : Bill (n+1) (sector μ K F T):= outside_patch μ T (h.diff Metric.isOpen_ball) (hK.mono Set.sdiff_subset) (show 0<c*r^2 by positivity) (by rintro x ⟨hx,hx'⟩; have hp : r≤‖x‖:= le_of_not_gt (fun hh=> hx' (mem_ball_zero_iff.mpr hh)); apply le_trans _ (hC _ hx); gcongr) _
   rw [show sector μ K F U - peval (moment μ K F) n = ((sector μ K F (ball 0 r)) - peval (moment μ K F) n) + sector μ K F T by
    funext x; simp only [Pi.sub_apply,Pi.add_apply,sector,T]; let V:= observable x K F; have hp : IntegrableOn V U μ:= ContinuousOn.integrableOn_compact h (hK.mul (Real.continuous_exp.comp_continuousOn (hF.neg.div_const _)))
    rw [setIntegral_sdiff Metric.isOpen_ball.measurableSet hp ht, mul_sub]; abel ]
   exact bill_add hu hcT

section comp
variable (g:E→E)(hg:ContDiffAt ℝ ω g 0) (hy:g 0=0) (hA:fderiv ℝ g 0=ContinuousLinearMap.id ℝ E) {J:E→ℝ}
   (hX: PertExtension.Series.Radial.Stationary F) (hY:Gap F) (hF:ContDiffAt ℝ ω F 0)
include hg hy hX hF
omit μ [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma changed_stat (he : f=ᶠ[𝓝 0] F∘g): PertExtension.Series.Radial.Stationary f := by
  apply local_stat he.symm; have hb: ContDiffAt ℝ ω F (g 0):= by rw [hy]; exact hF
  have hv: fderiv ℝ F 0=0:= by ext1 x; obtain hx:= hX.base1 x; simpa [jet,iteratedFDeriv_one_apply] using hx
  refine ⟨ (hb.comp 0 hg).of_le le_top, Eq.trans (congr_arg F hy) hX.base0,fun x=> ?_⟩
  unfold jet; rw [iteratedFDeriv_one_apply,fderiv_comp 0 (hb.differentiableAt (by simp)) (hg.differentiableAt (by simp)),hy,hv]; simp
include hA
omit μ [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma pulled_cost (he:f=ᶠ[𝓝 0] F∘g) : jet f 2=jet F 2 := by
    have hv: fderiv ℝ F 0=0:= by ext1 x; obtain hx:= hX.base1 x; simpa [jet,iteratedFDeriv_one_apply] using hx
    funext x; rw [same_jet he,Inherit.second hg hy hF hv,hA]; rfl
include hY μ
set_option maxHeartbeats 500000
/-- Orientation-preserving change of variables tangent to identity, possibly only
 on a very small fixed neighborhood. Local Gaussian expansion carries full variable fpdet.
 To use for any other linear tangent, normalize coordinates separately (same basis,
 dimensions and chart normalization on each insertion).
-/
theorem powerSeries_gauge (hK:ContDiffAt ℝ ω K 0)(hJ:ContDiffAt ℝ ω J 0)
   (he:f=ᶠ[𝓝 0] F∘g)(hf:J=ᶠ[𝓝 0] fun x=> K (g x)*(fderiv ℝ g x).det) : moment μ K F=moment μ J f:= by
    have hb:HasStrictFDerivAt g ((ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap) 0:=by
        have hi:=hg.hasStrictFDerivAt (by simp); rw [hA] at hi; exact hi
    let T:=hb.toOpenPartialHomeomorph g
    have ht: T.source∈𝓝 (0:E):= T.open_source.mem_nhds hb.mem_toOpenPartialHomeomorph_source
    have hz: Tendsto g (𝓝 0) (𝓝 0):= by simpa only [hy] using hg.continuousAt.tendsto
    have hp: Filter.map g (𝓝 0)=𝓝 0 := by rw [hb.map_nhds_eq_of_equiv,hy]
    have hx:Gap f:=by unfold Gap; rw [pulled_cost g hg hy hA hX hF he]; exact hY
    have ha:= changed_stat g hg hy hX hF he
    have hw:ContDiffAt ℝ ω f 0 := (( (show ContDiffAt ℝ ω F (g 0) from (by rw [hy]; exact hF)).comp (0:E) hg)).congr_of_eventuallyEq he
    obtain ⟨c,hc,hW⟩:=near_floor hX hY
    obtain ⟨d,hd,hD⟩:=near_floor ha hx
    let A x:=(fderiv ℝ g x).det
    have hρ : ∀ᶠ x:E in 𝓝 0,0<A x:= ((ContinuousLinearMap.continuous_det.continuousAt.comp (hg.fderiv_right (m:=ω) (by simp)).continuousAt)).eventually (lt_mem_nhds (by rw [Function.comp_apply,hA]; exact (show 0<LinearMap.det _ from (by rw [show (ContinuousLinearMap.id ℝ E).toLinearMap=LinearMap.id from rfl,LinearMap.det_id]; norm_num))))
    let S:= {x| x∈ T.source ∧ f x=F (g x) ∧ J x=K (g x)*A x ∧ 0<A x ∧
                      c*‖g x‖^2≤ F (g x) ∧ d*‖x‖^2≤ f x ∧ ContDiffAt ℝ ω g x ∧ ContinuousAt f x ∧ ContinuousAt F (g x) ∧ ContinuousAt J x ∧ ContinuousAt K (g x) }
    have hS:S∈𝓝 (0:E):= ht |> (show T.source∈𝓝 0→ S∈𝓝 0 from fun h=> inter_mem h (he.and (hf.and (hρ.and ((hz.eventually hW).and (hD.and ((hg.eventually (by simp)).and ((priceProof f hw).and ((hz.eventually (priceProof F hF)).and ((priceProof J hJ).and (hz.eventually (priceProof K hK))))))))))))
    obtain ⟨r,hr,ht⟩:= Metric.nhds_basis_closedBall.mem_iff.mp hS
    let U:=Metric.closedBall (0:E) r; let V:=g '' U
    have hU : IsCompact U:= isCompact_closedBall ..; have hu:U∈𝓝 (0:E):= Metric.closedBall_mem_nhds _ hr
    let L x (h:x∈U): x∈ S:= ht h
    have hR x (h:x∈U): f x=F (g x) ∧ J x=K (g x)*A x ∧ 0<A x:= ⟨ (L x h).2.1, (L x h).2.2.1, (L x h).2.2.2.1 ⟩
    have hQ x (h:x∈U): c*‖g x‖^2 ≤ F (g x) ∧ d*‖x‖^2 ≤ f x ∧ ContDiffAt ℝ ω g x ∧ ContinuousAt f x ∧ ContinuousAt F (g x) ∧ ContinuousAt J x ∧ ContinuousAt K (g x):= (L x h).2.2.2.2
    have hV : IsCompact V:=hU.image_of_continuousOn fun x hx=> (hQ x hx).2.2.1.continuousAt.continuousWithinAt
    have hv:V∈𝓝 0 := hp ▸ (Filter.image_mem_map hu : V∈Filter.map g (𝓝 0)) -- motive
    have hh : Aspiration (sector μ J f U) (moment μ J f):= local_bound μ hd U hU hu (fun x hx=> (hQ x hx).2.1) (fun x hx=> (hQ x hx).2.2.2.2.2.1.continuousWithinAt) (fun x hx=> (hQ x hx).2.2.2.1.continuousWithinAt) ha hx (hJ.of_le le_top)
    have hy : Aspiration (sector μ K F V) (moment μ K F) := local_bound μ hc _ hV hv (by rintro x ⟨y,hy,rfl⟩; exact (hQ y hy).1)
            (by rintro x ⟨y,hy,rfl⟩; exact (hQ y hy).2.2.2.2.2.2.continuousWithinAt) (by rintro x ⟨y,hy,rfl⟩; exact (hQ y hy).2.2.2.2.1.continuousWithinAt) hX hY (hK.of_le le_top)
    have H:sector μ K F V = sector μ J f U:= by
       funext a; unfold sector; congr 1; unfold V; rw [ MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul μ hU.measurableSet (f':=fderiv ℝ g) (fun x hx=> ((hQ x hx).2.2.1.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt) (T.injOn.mono (fun x hx=> (L _ hx).1 )) ];
       apply setIntegral_congr_fun hU.measurableSet; intro x hx; obtain ⟨aH,hV,hM⟩:=hR x hx; change |A x| * (K (g x) * Real.exp _) = observable a J f x; unfold observable; rw [aH,hV,abs_of_pos hM]; ring
    rw [H] at hy; exact hy.unique hh
end comp
end YM.FVA2.GermLaplace
