import YM.PertExtension.Interior
/-! # Parametric Laplace theorem for tree-slice steps with full-rank marks

finite-dimensional, no uniform in cutoff here. allow dummy coordinates and
coercivity solely on internal A. Includes Gaussian moments weighted now also
by melding amplitude/tests, finite densities with LOCAL masks. Fits the units
used in Orb expansion of the bare Wilson plot, with more group-read topology.
Proves constancy of the coefficients so that field reparametrizations preserve
calibration while period-chart recentered in the actual atlas. Estimates here
for rescaled footprint y-coordinate after non-equivariant completion. -/
noncomputable section
namespace YM.Contacts.Milling
open Function Set Filter Metric MeasureTheory PertExtension.Series PertExtension.Series.Radial Zone
open scoped Topology BigOperators ContDiff Classical
variable {E V : Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
   [NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V] {K f : E × V→ℝ}{c R C :ℝ}
def Hilly (f:E×V→ℝ)(c R C:ℝ):Prop := ∀ x∈closedBall (0:E) R, ∀ y:V,c*‖(x,y)‖^2 - C ≤ jet f 2 (x,y)
lemma girth (x:E)(y:V)(h:‖x‖≤ R): 1+‖(x,y)‖ ≤ (1+R)*(1+‖y‖):= by
  rw [Prod.norm_def]; have hX:=norm_nonneg x; have hj:=norm_nonneg y; rcases le_total ‖x‖ ‖y‖ with a|a; · rw [max_eq_right a]; nlinarith
  rw [max_eq_left a]; nlinarith
lemma dominate (hc:0<c)(h:Hilly f (c+c) R C) {x:E}(hx:x∈closedBall 0 R)(y:V):
    shade c (x,y)* kernel f (x,y) ≤ Real.exp C * Real.exp (-c*‖y‖^2):= by
  unfold shade kernel; simp only [← Real.exp_add]; apply Real.exp_monotone; have he:=h x hx y; have hp :‖y‖≤ ‖(x,y)‖:= le_max_right ..; nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hp 2) hc.le]
variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace V][BorelSpace V]

lemma zoomBound (hc:0<c)(h:Hilly f (c+c) R C)(H:(Radial.zone (E:=E×V)).Invoice A) : ∃ (D:ℝ)(k:ℕ),0≤D∧∀ x∈closedBall 0 R,∀ y:V, ‖A (x,y)*kernel f (x,y)‖≤ D*Radial.bill k c y:= by
    obtain ⟨D,k,hD,H⟩:=H; refine ⟨D*(1+|R|)^k*Real.exp C,k,by positivity,fun x hx y=>?_⟩
    have hh:=girth x y (mem_closedBall_zero_iff.mp hx); have hv : kernel f (x,y) ≤ Real.exp C * Real.exp (-c*‖y‖^2):= (le_mul_of_one_le_left kernel_pos.le (Real.one_le_exp (show 0 ≤ c*‖(x,y)‖^2 from by positivity))).trans (dominate hc h hx y); rw [norm_mul,Real.norm_of_nonneg kernel_pos.le]; let u:=1+‖y‖
    calc
      _ ≤ (D*(1+‖(x,y)‖)^k)*(Real.exp C*Real.exp (-c*‖y‖^2)):= mul_le_mul (H _) hv kernel_pos.le (by positivity)
      _ ≤ (D*((1+|R|)*u)^k)*(Real.exp C*Real.exp (-c*‖y‖^2)):= by unfold u; gcongr; exact hh.trans (by gcongr; apply le_abs_self)
      _ = _:= by unfold u Radial.bill Radial.zone; simp only [mul_pow]; ring
lemma zpo (hF : Radial.Stationary f)(hK : ContDiffAt ℝ ∞ K 0) (hc:0<c) (h:Hilly f (c+c) R C) (n : ℕ) : ∃ δ>0,∃ (e:ℕ)(D:ℝ),0≤ D ∧ ∀ x∈closedBall (0:E) R,∀ t>0,t≤δ → ∀ y∈ disc t δ,
    ‖projection K f t (x,y)-poly K f n t (x,y)‖ ≤ D*t^(n+1)*Radial.bill e c y:= by
  let Z : Zone (E×V):= Radial.zone; obtain ⟨δ,M,e,hδ,hM,H⟩:=((integrand hK hF hc).fits n).cost
  let r:=δ/(3+|R|); refine ⟨r,by unfold r; positivity,e,M*(1+|R|)^e*Real.exp C,by positivity,fun x hx t ht he y hy=>?_⟩
  have hb :=mem_closedBall_zero_iff.mp hx; have hR : 0≤ R:= (norm_nonneg x).trans hb
  have hh := H (x,y) t ht (show t*(1+‖(x,y)‖)≤δ from ?_); swap
  · have hr:= disc_mem ht.le r y|>.mp hy
    have hO := (le_div_iff₀ (show 0<3+|R| by positivity)).1 he; have hv:r ≤ δ/2:= by apply div_le_div_of_nonneg_left hδ.le (by norm_num) (by linarith only [abs_nonneg R])
    rw [Prod.norm_def]; rcases le_total ‖x‖ ‖y‖ with a|a; · rw [max_eq_right a]; nlinarith only [hr,hv,he]
    rw [max_eq_left a]; rw [abs_of_nonneg hR] at hO; nlinarith
  have hu:=girth x y hb; let g:=1+‖(x,y)‖; let d:=1+‖y‖
  change ‖insertion f K t (x,y)-eval (integrandSeries f K) n t (x,y)‖≤ M*g^e*shade c (x,y)*t^(n+1) at hh
  unfold projection poly; rw [← sub_mul,norm_mul, Real.norm_of_nonneg kernel_pos.le]; apply (mul_le_mul_of_nonneg_right hh kernel_pos.le).trans; calc
    _ = M*t^(n+1)*g^e*(shade c (x,y)*kernel f (x,y)):=by ring
    _ ≤ M*t^(n+1)*((1+|R|)*d)^e*(Real.exp C*Real.exp (-c*‖y‖^2)):= by unfold d g; exact mul_le_mul (by gcongr; rwa [abs_of_nonneg hR]) (dominate hc h hx y) (by unfold shade kernel; positivity) (by positivity)
    _ = _:= by unfold Radial.bill Radial.zone d; simp only [mul_pow]; ring
lemma intBound (hF : Radial.Stationary f)(hK : ContDiffAt ℝ ∞ K 0) (hc:0<c) (h:Hilly f (c+c) R C) (n : ℕ) : ∃ (e:ℕ)(D:ℝ),0≤D ∧ ∀ x∈closedBall 0 R,∀ t∈ Ioc (0:ℝ) 1,∀ y:V, ‖poly K f n t (x,y)‖ ≤ D*Radial.bill e c y := by
  obtain ⟨D,e,hD,H⟩:=hF.coeffBound hK n; refine ⟨e,D*(1+|R|)^e* Real.exp C,by positivity,fun x hx t ht y=>?_⟩
  unfold poly; rw [norm_mul,Real.norm_of_nonneg kernel_pos.le]; calc
    _ ≤ D * ((1+|R|)*(1+‖y‖))^e * (Real.exp C*Real.exp (-c*‖y‖^2)) := by
      refine mul_le_mul ((H _ t ht.1.le ht.2).trans ?_) ?_ kernel_pos.le (by positivity)
      · apply mul_le_mul_of_nonneg_left _ hD; unfold Radial.zone; dsimp only; gcongr ?_ ^e; exact (girth x y (mem_closedBall_zero_iff.mp hx)).trans (by gcongr; apply le_abs_self)
      exact (le_mul_of_one_le_left kernel_pos.le (Real.one_le_exp (by positivity : 0≤ c*‖(x,y)‖^2))).trans (dominate hc h hx y)
    _ = _:= by unfold Radial.bill Radial.zone; simp only [mul_pow];ring
section int
variable (μ : Measure V)[μ.HasTemperateGrowth]
abbrev mural (K f:E × V→ℝ)(n:ℕ)(x:E) : ℝ:=∫ y, normTerm K f n (x,y) ∂μ
def ash (K f:E× V→ℝ)(t:ℝ)(s:Set V)(x:E) : ℝ:=∫ y in s, projection K f t (x,y) ∂μ
include μ
lemma sized {s:Set V}{F:V→ℝ}(n:ℕ)(h:0<c)(hc:0≤C)(hp:∀ᵐ y ∂μ.restrict s, ‖F y‖ ≤ C*Radial.bill n c y)(he:AEStronglyMeasurable F (μ.restrict s)): IntegrableOn F s μ ∧ ‖∫ y in s,F y ∂μ‖≤ C*∫ y,Radial.bill n c y ∂μ:= by
  let g (y:V) := C*Radial.bill n c y; have hg : Integrable g μ:= (bill_integrable μ n h).const_mul _
  exact ⟨hg.integrableOn.mono' he hp, (norm_integral_le_of_norm_le hg.integrableOn hp).trans ((setIntegral_le_integral hg (Eventually.of_forall fun y=> mul_nonneg hc (bill_nonneg ..))).trans_eq (integral_const_mul ..))⟩
lemma termInt (hF : Radial.Stationary f)(hK : ContDiffAt ℝ ∞ K 0) (hc:0<c) (h:Hilly f (c+c) R C) {x:E}(hx:x∈closedBall 0 R)(n): Integrable (fun y:V=> normTerm K f n (x,y)) μ:= by
  obtain ⟨D,k,hD,H⟩:= zoomBound hc h ((integrand hK hF hc).invoice n); exact ((bill_integrable μ k hc).const_mul D).mono' ((Smooth.continuousTerms K f n).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable (Eventually.of_forall (H _ hx))
lemma album (hF : Radial.Stationary f)(hK : ContDiffAt ℝ ∞ K 0) (hc:0<c) (h:Hilly f (c+c) R C) {x:E}(hx:x∈closedBall 0 R)(n)(t:ℝ): Integrable (fun y:V=> poly K f n t (x,y)) μ ∧ (∫ y, poly K f n t (x,y) ∂μ)= eval (mural μ K f) n t x:= by
  simp_rw [show ∀ y:V, poly K f n t (x,y)= ∑ i∈Finset.range (n+1),t^i * normTerm K f i (x,y) from fun y=> by unfold poly Zone.eval normTerm; simp only [Finset.sum_mul,smul_eq_mul,mul_assoc]]
  have he (i:ℕ):= (termInt μ hF hK hc h hx i).const_mul (t^i); exact ⟨integrable_finsetSum _ (fun i _=> he i),by rw [integral_finsetSum _ (fun i _=> he i)]; exact Finset.sum_congr rfl fun i _=> integral_const_mul ..⟩
lemma shadowBall {r:ℝ}(hr:0<r) (n k:ℕ) (hF : Radial.Stationary f)(hK : ContDiffAt ℝ ∞ K 0) (hc:0<c) (h:Hilly f (c+c) R C) :
    ∃ M:ℝ,0≤M∧∀ t∈ Ioc (0:ℝ) 1,∀ s:Set V, s⊆(disc t r)ᶜ → MeasurableSet s → ∀ x∈closedBall (0:E) R, ‖∫ y in s,poly K f n t (x,y) ∂μ‖ ≤ M*t^k := by
  obtain ⟨e,D,hD,H⟩:= intBound hF hK hc h n
  let v:=Radial.bill (e+k) c (E:=V); let M:= D*(r⁻¹)^k; have hu : 0≤M:= by unfold M; positivity
  refine ⟨M*∫ y,v y ∂μ,mul_nonneg hu (integral_nonneg fun _=>bill_nonneg ..),fun t ht s hs he x hx=>?_⟩
  apply (sized μ _ hc (mul_nonneg hu (pow_nonneg ht.1.le k)) ?_ (album μ hF hK hc h hx n t).1.integrableOn.1).2.trans_eq (mul_right_comm ..); filter_upwards [ae_restrict_mem he] with y hy
  have hR : r ≤ t*‖y‖ := not_lt.mp ((hs hy) ∘ (disc_mem ht.1.le r y).2)
  have hQ : 1≤ t*(1+‖y‖)*r⁻¹ := by apply (le_mul_inv_iff₀ hr).2; linarith only [hR,ht.1]
  apply (H _ hx t ht y).trans; calc
     _ ≤ D*Radial.bill e c y*(t*(1+‖y‖)*r⁻¹)^k:= le_mul_of_one_le_right (mul_nonneg hD (bill_nonneg ..)) (one_le_pow₀ hQ)
     _ = _:= by unfold Radial.bill Radial.zone M; simp only [pow_add,mul_pow]; ring
/-! Direct uniform, with three constraints. Allowed convert set costs by any post-ball diffeo, need not be invariant direction. -/
theorem perspective (hF : Radial.Stationary f)(hK : ContDiffAt ℝ ∞ K 0) (hm:Measurable K)(hf:Measurable f)(hc:0<c) (h:Hilly f (c+c) R C)(n):
    ∃ δ>0,∀ r>0,∃ D:ℝ,0≤D ∧ ∀ᶠ t in 𝓝[>] (0:ℝ),∀ s:Set V, MeasurableSet s → disc t r ⊆ s→ s⊆disc t δ → ∀ x∈closedBall (0:E) R, IntegrableOn (fun y=>projection K f t (x,y)) s μ ∧
        ‖ash μ K f t s x - eval (mural μ K f) n t x‖ ≤ D*t^(n+1) := by
  obtain ⟨δ,hδ,e,D,hD,H⟩:= zpo hF hK hc h n; refine ⟨δ,hδ,fun r hr=> ?_⟩; obtain ⟨Q,hQ,hX⟩:= shadowBall μ hr n (n+1) hF hK hc h
  let D':= D*∫ y:V,Radial.bill e c y ∂μ; refine ⟨D'+Q,add_nonneg (mul_nonneg hD (integral_nonneg fun _=>bill_nonneg ..)) hQ,?_⟩
  filter_upwards [self_mem_nhdsWithin,eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (show 0 < min 1 δ from lt_min zero_lt_one hδ))] with t (ht:0<t) hy s hs hh hz x hx
  obtain ⟨hO,Hs⟩:= album μ hF hK hc h hx n t; let d y:= projection K f t (x,y) - poly K f n t (x,y)
  have hD : ∀ᵐ y ∂μ.restrict s, ‖d y‖ ≤ (D*t^(n+1))*Radial.bill e c y:=by filter_upwards [ae_restrict_mem hs] with y hw; exact H _ hx t ht (hy.le.trans (min_le_right ..)) y (hz hw)
  let p := fun y:V => projection K f t (x,y); have hv (x:V):p x=d x+ _ := (sub_add_cancel (p x) (poly K f n t _)).symm; obtain ⟨h1,h2⟩:= sized μ e hc (mul_nonneg (by positivity) (pow_nonneg ht.le _)) hD (((projection_meas hm hf t).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable.sub hO.integrableOn.1)
  have hp : IntegrableOn p s μ:= by simp_rw [funext hv]; exact h1.add hO.integrableOn
  refine ⟨hp,?_⟩; change ‖(∫ y in s,p y ∂μ)-  (eval (mural μ K f) n t x)‖ ≤ _; rw [← Hs,← integral_add_compl hs hO, sub_add_eq_sub_sub]; apply (norm_sub_le ..).trans
  rw [← integral_sub hp hO.integrableOn]; apply (add_le_add h2 (hX t ⟨ht,hy.le.trans (min_le_left ..)⟩ sᶜ (compl_subset_compl.mpr hh) hs.compl x hx)).trans_eq; unfold D'; ring
end int
end YM.Contacts.Milling
