import YM.WilsonCoeffUV.Emit.GaussianConvention
import YM.PertExtension.Aspiration
/-!
# Formal ζ convention = power expansion of one-link normalized Noise toll

Calls the compiler's ordinary Radial determinant convention pinned ADD volume.
Only one coarse link (Z independent of link). This is NOT a remainder theorem for
any fine conditional measure. No corresponding estimate asserted on pushed
partition. Clear g^dim and actual ChartRatio.scale and the Gaussian mass;
ζ lives after division by all three. Thus + log ζ in the raw *action*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Convention
open Filter Function Matrix MeasureTheory Set Lattice FreeResolvent Metric RG Wilson Tree Precision
open PertExtension PertExtension.GaussianScore PertExtension.Series PowerSeries Blue
open scoped BigOperators Topology MatrixOrder ContDiff ENNReal Matrix.Norms.Frobenius
variable {X:Type} [Fintype X]

section algebra
lemma radial_clock (f:Lawn X→ℝ) (x:Lawn X) (k:ℕ): MvPolynomial.eval x (coeff k (Blue.jet f))=Radial.jet f k x:= rayon ..
lemma clock_out {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (M:Lawn X→L[ℝ] E)
    (f:E→ℝ)(h:ContDiffAt ℝ ω f 0) (x:Lawn X)(k:ℕ) :
    Radial.jet (f ∘ M) k x= Radial.jet f k (M x):=by
  unfold Radial.jet
  rw [Next.Foundations.jets_linear M (h.of_le le_top),ContinuousMultilinearMap.compContinuousLinearMap_apply]
lemma expansion_price (F:PowerSeries ℝ)(p:constantCoeff F=0)(k:ℕ): coeff k (raiseE F)= ∑ i∈Finset.range (k+1),(i.factorial:ℝ)⁻¹*coeff k (F^i) := by
  rw [raises p, edit_coeff _ p _ k.lt_succ_self,map_sum]
  apply Finset.sum_congr rfl; intro i _; rw [coeff_C_mul,coeff_exp]; congr 1; norm_num [one_div]
end algebra

section zeta
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{Ñ:ChartRatio G}{n N: Side} (S:StepData n N) (p:LocalRatio Ñ) {κ:ℝ}

def priceAt (G:Gauge)(κ:ℝ) (v:G.Color): ℝ:= κ*G.price (G.lieExp v)
lemma price_cont (κ:ℝ) : ContDiffAt ℝ ω (priceAt G κ) 0:= by
  unfold priceAt
  apply contDiffAt_const.mul; apply Work.F03.price_smooth (A:=fun v=> G.lieExp v); exact G.exp_jet.contDiffAt

lemma clock_color (k:ℕ)(x:Lawn G.ColorIndex): MvPolynomial.eval x (coeff k (jet (weightC G κ)))= Radial.jet (priceAt G κ) k (coatC G x) := by
  rw [radial_clock]; exact clock_out (coatC G).toContinuousLinearMap _ (price_cont κ) x k
include p in
lemma clock_J (k:ℕ)(x:Lawn G.ColorIndex): MvPolynomial.eval x (coeff k (jet (dij Ñ)))= Radial.jet Ñ.J k (coatC G x) := by
  rw [radial_clock]; exact clock_out (coatC G).toContinuousLinearMap _ (p.germ 0 (mem_ball_self p.patch)) x k
lemma towel_cov (κ:ℝ) (x:Lawn G.ColorIndex): Radial.jet (priceAt G κ) 2 (coatC G x)= dotProduct x (towel G κ *ᵥ x)/2:=by
  rw [←clock_color]
  have hy : coeff 2 (Blue.jet (weightC G κ))=paint 2 (orbQ (towel G κ)):=by
    rw [← show coeff 0 (flash (sprig (weightC G κ) 2))=coeff 2 (Blue.jet (weightC G κ)) from by rw [sprig_flash,coeff_mk,Nat.add_zero], flash,coeff_mk]; rw [sprouts_lead (seedPay_green κ) (seed_jets κ).2.2 (by simp [towel]), visible_shine]
  rw [hy, orb_eval]

lemma layers_price (κ:ℝ)(x:Lawn G.ColorIndex)(i:ℕ):
    MvPolynomial.eval x (coeff i (-gust G κ))=Radial.layers (priceAt G κ) i (coatC G x):=by
  unfold Radial.layers gust orbC; simp only [map_neg,map_sub, sprig_flash,coeff_mk,clock_color]
  rw [coeff_C]; by_cases h:i=0
  · subst i; simp [towel_cov,orb_eval]
  simp [h,Nat.add_comm]

include p in
lemma expansion_clock (κ:ℝ)(i:ℕ)(x:Lawn G.ColorIndex):
    MvPolynomial.eval x (coeff i (jet (dij Ñ)*raiseE (-gust G κ)))=Radial.integrandSeries (priceAt G κ) Ñ.J i (coatC G x):=by
  let F:= -gust G κ
  let E : Ink _ →+* PowerSeries ℝ:= map (MvPolynomial.eval x)
  have hF: constantCoeff F=0:=by rw [show F= -gust G κ from rfl,map_neg,gust_zero,neg_zero]
  have hr i : coeff i (E F)=Radial.layers (priceAt G κ) i (coatC G x):= layers_price κ x i
  have hf k i : coeff i ((E F)^k)= Zone.TaylorPow (Radial.layers (priceAt G κ)) k i (coatC G x):=by
    induction k generalizing i with
    | zero=> exact PowerSeries.coeff_one _
    | succ k ih=> simp_rw [pow_succ,coeff_mul, Zone.TaylorPow, Zone.mul,ih,hr]
  have he (j): MvPolynomial.eval x (coeff j (raiseE F))= Radial.expsum (Radial.layers (priceAt G κ)) j j (coatC G x):=by
    change coeff j (E _)=_
    have hg: constantCoeff (E PowerSeries.X)=0:=by simp [E]
    rw [raise_map _ hg hF, expansion_price (E F) (by rw [← coeff_zero_eq_constantCoeff_apply]; unfold E; rw [coeff_map,coeff_zero_eq_constantCoeff_apply,hF,map_zero])]
    simp_rw [hf]; rfl
  simp only [PowerSeries.coeff_mul,map_mul,map_sum,Radial.integrandSeries,Zone.mul]; exact Finset.sum_congr rfl fun i _=>congr_arg₂ (· * ·) (clock_J p i.1 x) (he i.2)

lemma unit_Pos (h:0<κ): (towel G κ).PosDef:=by unfold towel; exact Matrix.PosDef.one.smul h

lemma price_stationary (κ:ℝ) :Radial.Stationary (priceAt G κ):=by
  refine ⟨(price_cont κ).of_le le_top,by simp [priceAt],fun u=>?_⟩
  obtain ⟨x,rfl⟩:= (coatC G).surjective u
  rw [←clock_color,radial_clock,Radial.jet,iteratedFDeriv_one_apply,(seed_jets κ).2.1]; simp

lemma price_coercive (h:0<κ):∃ c>0,∀ u:G.Color,c*‖u‖^2≤ Radial.jet (priceAt G κ) 2 u :=by
  apply Radial.quadratic_min
  intro u hu; obtain ⟨x,rfl⟩:= (coatC G).surjective u
  have he:x≠0:=by rintro rfl; simp at hu
  rw [towel_cov]; exact div_pos (by simpa only [star_trivial] using (unit_Pos h).dotProduct_mulVec_pos (x:=x) he) (by norm_num)

/-- Positive leading mass in density convention used by ζ. -/
def linkMass (G:Gauge) (κ:ℝ) := ∫ x:Lawn G.ColorIndex,Real.exp (-dotProduct x (towel G κ *ᵥx)/2)
lemma link_mass_pos (h:0<κ) : 0< linkMass G κ:= by
  have ht: Law.average (law (K:=towel G κ) (unit_Pos h)) volume 1=1:= Law.empty ..
  unfold Law.average at ht; rw [one_mul] at ht
  have hf: linkMass G κ/linkMass G κ=1 := ht
  have hg : linkMass G κ ≠0:=by intro he; rw [he] at hf; norm_num at hf
  apply lt_of_le_of_ne _ hg.symm
  exact integral_nonneg fun x=> (Real.exp_pos _).le

include p in
lemma zeta_predict (h:0<κ)(i:ℕ): coeff i (ζ Ñ κ) * linkMass G κ= Radial.moment volume Ñ.J (priceAt G κ) i:=by
  let F:= (jet (dij Ñ)*raiseE (-gust G κ))
  let H:Matrix G.ColorIndex G.ColorIndex ℝ:= κ⁻¹ • 1
  have hx : H.transpose=H:= by simp [H]
  let I := (∫ z:Lawn G.ColorIndex, MvPolynomial.eval z (coeff i F) * Real.exp (-dotProduct z (towel G κ *ᵥz)/2))
  rw [show coeff i (ζ Ñ κ)=I/linkMass G κ from (gaussian_centered (H:=H) (unit_Pos h) (precision_one h) hx F i), div_mul_cancel₀ _ (link_mass_pos h).ne']
  rw [Radial.moment,← (PiLp.volume_preserving_toLp G.ColorIndex).integral_comp (MeasurableEquiv.toLp 2 (G.ColorIndex → ℝ)).measurableEmbedding]
  refine integral_congr_ae (Eventually.of_forall fun x=>?_)
  change MvPolynomial.eval x _*_ = Radial.integrandSeries _ _ _ _ * Real.exp (-Radial.jet _ _ (coatC G x))
  rw [show MvPolynomial.eval x (coeff i F)=_ from expansion_clock p κ i x,towel_cov,neg_div]; rfl

/-- Normalizing factor **per coarse bond**, NOT the conditional measure of
fine variables. RC actual density has `1/Z` for each such bond before summing
tags. -/
def oneLink (G:Gauge) (κ g:ℝ)(U:G.El): ℝ:= Real.exp (-κ* G.price U/g^2)
def courseZ (G:Gauge) (κ g:ℝ): ℝ:=∫ U:G.El, oneLink G κ g U ∂G.probHaar
lemma one_density (κ t:ℝ): Continuous (oneLink G κ t):=by unfold oneLink; fun_prop
lemma penaltyZ_same (S:StepData n N)(G:Gauge)(t:ℝ) : courseZ G S.kernel.penalty t=S.penaltyZ (t^2)⁻¹ G:= by
  unfold courseZ StepData.penaltyZ StepData.penaltyWeight oneLink
  congr 1; funext x; ring_nf

/-- Removes the ordinary power at zero coupling, not explained away by using
Lebesgue instead of Probability Haar! -/
def cleared (Ñ:ChartRatio G) (κ g:ℝ): ℝ := ((g^(Module.finrank ℝ G.Color))⁻¹*courseZ G κ g)/(Ñ.scale*linkMass G κ)

abbrev Threshold (G:Gauge) (r:ℝ): Set G.El := G.lieExp '' ball 0 r

include p in
private lemma onChart {r:ℝ}(hr : r≤ Chart.small G Ñ)(b:G.El→ℝ)(h:Measurable b) :
    (∫ x in Threshold G r,b x ∂G.probHaar)= Ñ.scale * (∫ x in ball (0:G.Color) r, Ñ.J x * b (G.lieExp x)) := by
  have hs : ball (0:G.Color) r ⊆ ball 0 Ñ.radius:= ball_subset_closedBall.trans (closedBall_subset_ball ((hr.trans (min_le_left ..)).trans_lt (half_lt_self p.patch)))
  let T : Set G.El:= Threshold G r
  have hT:= ((LocalH.geom_patch G).choose_spec.2 r (hr.trans (min_le_right ..))).1.measurableSet
  have hB:G.lieExp ⁻¹' T ∩ ball 0 Ñ.radius=ball 0 r:= by
    ext x; constructor
    · rintro ⟨⟨z,hz,he⟩,hx⟩; exact p.inject (hs hz) hx he ▸ hz
    exact fun hx=>⟨⟨x,hx,rfl⟩,hs hx⟩
  let E (x:G.Color):= ENNReal.ofReal (Ñ.scale*Ñ.J x)
  have he : Measurable E:= (p.borel.const_mul _).ennreal_ofReal
  let μ:=(volume.restrict (ball 0 r)).withDensity E
  have hZ : MeasurePreserving G.lieExp μ (G.probHaar.restrict T):=by
    have ht : Threshold G r ⊆ Threshold G Ñ.radius:= Set.image_mono hs
    constructor; exact G.lieExp_cont.measurable
    have hx:= congr_arg (fun M:Measure G.El=>M.restrict T) p.actual
    rw [Measure.restrict_restrict_of_subset ht] at hx
    rw [Measure.restrict_map G.lieExp_cont.measurable hT,
        restrict_withDensity (G.lieExp_cont.measurable hT), Measure.restrict_restrict (G.lieExp_cont.measurable hT),hB] at hx
    exact hx
  change (∫ x, b x ∂G.probHaar.restrict T)= _
  rw [← hZ.map_eq,integral_map hZ.measurable.aemeasurable h.aestronglyMeasurable]; unfold μ
  rw [integral_withDensity_eq_integral_toReal_smul he (Eventually.of_forall fun _=> ENNReal.ofReal_lt_top),←integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (isOpen_ball (x:=(0:G.Color))).measurableSet] with x hx
  rw [ENNReal.toReal_ofReal (le_of_lt (mul_pos p.scale (p.pos x (hs hx)))),smul_eq_mul,mul_assoc]

include p in
private lemma interior {r g κ:ℝ}(hr : r≤Chart.small G Ñ)(hg : 0<g) :
    (g^Module.finrank ℝ G.Color)⁻¹*(∫ U in Threshold G r,oneLink G κ g U ∂G.probHaar)=
      Ñ.scale * Radial.partialSum volume Ñ.J (priceAt G κ) r g:= by
  rw [onChart p hr _ (one_density κ g).measurable, mul_left_comm]
  congr 1
  let μ:Measure G.Color:= volume; let U :=ball (0:G.Color) r
  let F (x:G.Color):= Ñ.J x * oneLink G κ g (G.lieExp x)
  let T:= Radial.disc (E:=G.Color) g r
  have he (x : G.Color): Radial.projection Ñ.J (priceAt G κ) g x= F (g • x):= by
    rw [Radial.projection_eq]; unfold F priceAt oneLink; simp
  have hx x: U.indicator F (g•x)=T.indicator (fun z=>F (g•z)) x:=by
    by_cases h:g•x∈U
    · rw [indicator_of_mem h,indicator_of_mem (s:=T) h]
    rw [indicator_of_notMem h, indicator_of_notMem (s:=T) h]
  have hg':=Measure.integral_comp_smul_of_nonneg μ (U.indicator F) g (hR:=hg.le)
  simp_rw [hx] at hg'
  rw [integral_indicator (Radial.disc_meas g r), integral_indicator isOpen_ball.measurableSet,smul_eq_mul] at hg'
  unfold Radial.partialSum; simp_rw [he]; exact hg'.symm

private lemma off_price {r:ℝ}(hr : r≤Chart.small G Ñ)(h:0<r)(hg:0<κ) :
    ∃ b>0,∀ x:G.El,x∈(Threshold G r)ᶜ → b≤κ*G.price x:=by
  let T:Set G.El:= (Threshold G r)ᶜ
  by_cases hx:T.Nonempty
  swap
  · exact ⟨1,one_pos,fun x ht=> (hx ⟨x,ht⟩).elim⟩
  have hf:Continuous fun x:G.El=>κ*G.price x:=by fun_prop
  obtain ⟨x,hx,x'⟩:= (((LocalH.geom_patch G).choose_spec.2 r (hr.trans (min_le_right ..))).1).isClosed_compl.isCompact.exists_isMinOn hx hf.continuousOn
  have hb:x≠1:=by
    intro he; apply hx; rw [he]; exact ⟨0,mem_ball_self h,G.mat_lieExp_zero⟩
  refine ⟨κ*G.price x,mul_pos hg ?_,x'⟩
  apply lt_of_le_of_ne (G.price_range x).1; intro hv; apply hb
  have H:= Branch.price_diff (G:=G) x 1; rw [inv_one,mul_one,←hv] at H; simp only [mul_zero] at H
  exact G.mat_injective (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp H.symm)))

private lemma exterior {r:ℝ}(hr : r≤Chart.small G Ñ)(h:0<r)(hg:0<κ)(N:ℕ) :
    Tested.Bill N (fun g=> (g^Module.finrank ℝ G.Color)⁻¹*(∫ U in (Threshold G r)ᶜ,oneLink G κ g U ∂G.probHaar)):=by
  obtain ⟨B,hB,hV⟩:= off_price hr h hg; let d:= Module.finrank ℝ G.Color
  obtain ⟨C,hC,hK⟩:=Radial.bounded_exp hB (N+d)
  refine ⟨C,hC,?_⟩; filter_upwards [Tested.eventually_pos] with x hx
  have hp : 0<x⁻¹:=inv_pos.mpr hx; let t:= x⁻¹
  let F:=Real.exp (-B*t^2)
  let Z (u:G.El):=F; let T : Set G.El:= (Threshold G r)ᶜ
  have hi:Integrable Z G.probHaar:= integrable_const _
  have hz :0≤F:= (Real.exp_pos _).le
  have ht:= ((LocalH.geom_patch G).choose_spec.2 r (hr.trans (min_le_right ..))).1.measurableSet.compl
  have he x' (hx':x'∈T): ‖oneLink G κ x x'‖≤ Z x':=by
    rw [Real.norm_eq_abs,abs_of_pos (a:=oneLink G κ x x') (Real.exp_pos _)]; apply Real.exp_le_exp.mpr
    rw [show -B*t^2= -B / x^2 from by unfold t; rw [inv_pow, div_eq_mul_inv]]
    rw [neg_mul]; gcongr; exact hV x' hx'
  let I:= (∫ u in T,oneLink G κ x u ∂G.probHaar)
  change ‖(x^d)⁻¹*I‖≤ _
  have ho : ‖I‖ ≤ F:=(norm_integral_le_of_norm_le (Integrable.integrableOn hi (s:=T)) ((ae_restrict_mem ht).mono he)).trans ((setIntegral_le_integral hi (Eventually.of_forall (p:=fun x=>0≤Z x) (fun x=>hz))).trans_eq (by unfold Z; simp))
  have hy : t^d*F≤ C*x^N:=by
    apply le_of_mul_le_mul_left (a:=t^N) _ (pow_pos hp _)
    have H: C=t^N*(C*x^N):=by unfold t; rw [mul_left_comm,←mul_pow,inv_mul_cancel₀ hx.ne',one_pow,mul_one]
    refine le_trans ?_ ((hK t hp.le).trans_eq H)
    rw [←mul_assoc,←pow_add]; unfold t F; gcongr; simp
  rw [norm_mul,Real.norm_eq_abs ((x^d)⁻¹),abs_of_pos (inv_pos.mpr (pow_pos hx _)),←inv_pow]; exact le_trans (mul_le_mul_of_nonneg_left ho (pow_nonneg hp.le _)) hy

include p in
/-- It is exactly the specified one-link normalization before output log. Does
not turn estimates for this scalar into any multi-bond real density estimate. -/
theorem zeta_expansion (hk : 0<κ) : Tested.Aspiration (cleared Ñ κ) (fun i=> PowerSeries.coeff i (ζ Ñ κ)):=by
  intro k
  have hJ:= p.germ 0 (mem_ball_self p.patch)
  have he: Measurable (priceAt G κ):=by unfold priceAt; fun_prop
  obtain ⟨δ,hδ,H⟩:= (price_stationary κ).rescale_estimate volume (hJ.of_le le_top) p.borel he (price_coercive hk) k
  let L:= Chart.small G Ñ; let r:= min δ L/2
  have hp:0<r:= half_pos (lt_min hδ (Chart.Ratio.small_pos p))
  have hu:r<L:=by unfold r; have ht:=min_le_right δ L; linarith [show 0<L from Chart.Ratio.small_pos p]
  obtain ⟨C,h⟩:= H r ⟨hp,by unfold r;have x:=min_le_left δ L; linarith⟩
  obtain ⟨D,hD,hV⟩:= exterior hu.le hp hk (k+1)
  let m:=linkMass G κ
  have hb: 0<Ñ.scale*m:= mul_pos p.scale (link_mass_pos hk)
  refine ⟨(Ñ.scale*|C|+D)/(Ñ.scale*m),div_nonneg (by have ht:=p.scale; positivity) hb.le,?_⟩
  filter_upwards [h,hV,Tested.eventually_pos] with t hv hv' ht
  let T:Set G.El:= Threshold G r; let Q i:=coeff i (ζ Ñ κ); let W:= Tested.peval Q k t
  have hcT:=((LocalH.geom_patch G).choose_spec.2 r (hu.le.trans (min_le_right ..))).1
  have hf := integral_add_compl (s:=T) hcT.measurableSet ((one_density (G:=G) κ t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (μ:=G.probHaar)
  change ‖cleared Ñ κ t-W‖≤_
  let u:=Radial.partialSum volume Ñ.J (priceAt G κ) r t
  let v:=(t^Module.finrank ℝ G.Color)⁻¹*(∫ U in Tᶜ,oneLink G κ t U ∂G.probHaar)
  have he := interior p (g:=t) (κ:=κ) hu.le ht
  rw [show cleared Ñ κ t=(Ñ.scale*u+v)/(Ñ.scale*m) from ?z, div_mul_eq_mul_div]
  case z => unfold cleared courseZ; rw [← hf,mul_add]; rw [show (t^Module.finrank ℝ G.Color)⁻¹* (∫ x in T, oneLink G κ t x ∂G.probHaar)=_ from he]
  have hx := le_trans hv (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg ht.le _))
  rw [show (Ñ.scale*u+v)/(Ñ.scale*m) - W=(Ñ.scale*(u-W*m)+v)/(Ñ.scale*m) from by have hy:0<m:= link_mass_pos (G:=G) hk; have hz:=p.scale; field_simp; ring,norm_div]
  rw [Real.norm_eq_abs (Ñ.scale*m),abs_of_pos hb]; gcongr
  refine le_trans (norm_add_le ..) ?_
  have htT: W*m= ∑ i∈Finset.range (k+1),t^i*Radial.moment volume Ñ.J (priceAt G κ) i:=by simp only [W,Q,Zone.eval,smul_eq_mul,Finset.sum_mul,mul_assoc,m,zeta_predict p hk]
  rw [htT,norm_mul,Real.norm_eq_abs Ñ.scale,abs_of_pos p.scale,add_mul,mul_assoc]
  exact add_le_add (mul_le_mul_of_nonneg_left hx p.scale.le) hv'
end zeta
end YM.WilsonCoeffUV.Convention
