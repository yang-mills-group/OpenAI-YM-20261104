import YM.Contact.Rescale

/-! Power counting for Taylor-cut channels in the relative Euclidean space. `Growth` and
`Estimate` are analytic bounds on actual kernels (no assertions that an arbitrary hierarchy
possesses these bounds). -/

set_option autoImplicit false
noncomputable section
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff BigOperators Pointwise
namespace YM.Contacts
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E]
variable {G:Type*} [NormedAddCommGroup G]

/-- Pointwise envelope *only off* the center. -/
def Estimate (R p C:ℝ) (f:E→G) := ∀ y:E,y≠0 → ‖y‖≤R → ‖f y‖≤ C*‖y‖^p

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] in
lemma Estimate.mono {f:E→G}{R p C C' R':ℝ}(h:Estimate R p C f)(hR:R' ≤ R)(hC:C≤C'):
  Estimate R' p C' f:= fun y hy hh=> (h y hy (hh.trans hR)).trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (norm_nonneg _) _))

def Growth (p:ℝ)(f:E→G) := AEStronglyMeasurable f ∧ ∀ R:ℝ,0<R→∃ C:ℝ,0≤C∧ Estimate R p C f

def PowerCount (u w q:ℕ):ℤ := (u:ℤ)-(q:ℤ)-(w:ℤ)

lemma pc_threshold (u w q:ℕ) {ε:ℝ} (hε:ε<1): -(q:ℝ) < w-u-ε+((PowerCount u w q+1).toNat:ℕ):=by
  unfold PowerCount; set m:= (u:ℤ)-(q:ℤ)-(w:ℤ)+1
  have h : ((u:ℤ)-(q:ℤ)-(w:ℤ)+1:ℤ) ≤ (m.toNat:ℕ):= Int.self_le_toNat _
  have h':(u:ℝ)-q-w+1≤(m.toNat:ℕ):=by exact_mod_cast h
  linarith only [h',hε]

lemma pc_count (u w q:ℕ): (PowerCount u w q+1).toNat ≤ u+1:=by unfold PowerCount; omega

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] in
lemma chi_lt_zero (s:ℝ)(hs:0<s)(y:E)(hy:2*s<‖y‖):chi s y=0:=by
  apply chi_zero; rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hs).le]; apply (le_inv_mul_iff₀ hs).mpr; exact (mul_comm ..).trans_le hy.le

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] in
lemma rem_continuous (φ:Trial E)(s:ℝ)(m:ℤ): Continuous (remainder s m φ):= φ.continuous.sub (by
  unfold taylorCut; split_ifs
  · exact ((lamp.continuous).comp ((continuous_norm.comp ((continuous_const_smul s⁻¹).comp continuous_id)).pow 2)).smul
       (continuous_finsetSum _ fun i _=> (jet_smooth i φ (0:E)).continuous)
  exact continuous_const)

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] in
lemma rem_outside (s:ℝ)(hs:0<s)(m:ℤ)(φ:Trial E) {R : ℝ}(h:support (φ:E→ℂ)⊆closedBall 0 R) {y:E}(hh:R<‖y‖)(hp:2*s<‖y‖) : remainder s m φ y=0:=by
  have hz: φ y=0:=by
    apply Function.notMem_support.mp; intro hx; exact not_lt_of_ge (mem_closedBall_zero_iff.mp (h hx)) hh
  rw [remainder,taylorCut,hz]; split_ifs; rw [chi_lt_zero _ hs _ hp,zero_smul,sub_zero];rw [sub_zero]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] in
lemma rem_tame (s:ℝ)(hs:0<s)(m:ℤ) : ∃ C:ℝ,0≤C∧ ∀ (φ:Trial E) {B:ℝ}, Major (m+1).toNat φ B → ∀ y:E, ‖remainder s m φ y‖ ≤ ‖y‖^(m+1).toNat * (C*B) := by
  let k:ℕ:=(m+1).toNat; let a:ℝ:=(max 1 s⁻¹)^k; have ha:1 ≤ a:= one_le_pow₀ (le_max_left ..)
  have hk:((Finset.range k).card:ℝ)+1≥1:=le_add_of_nonneg_left (by positivity)
  let c':=((Finset.range k).card+1:ℝ)*a; have hc:1 ≤ c':=(one_le_mul_of_one_le_of_one_le hk ha)
  refine ⟨c',zero_le_one.trans hc,fun φ {B} h y=>?_⟩
  have hf:0≤B:= h.nonneg
  by_cases he : ‖y‖≤s
  · apply (remainder_near s hs h y he).trans; gcongr; apply le_mul_of_one_le_left hf hc
  have he := not_le.mp he
  by_cases hh:m<0
  · simp only [remainder,taylorCut,if_neg (not_le.mpr hh),sub_zero]; rw [show (m+1).toNat=0 from by omega]; exact h.value y |>.trans (by dsimp [c']; nlinarith only [hf,hc])
  have hk':k=m.toNat+1:=by dsimp [k]; omega
  have hm (i:ℕ)(hi:i ≤ k): ‖y‖^i ≤ a * ‖y‖^k:=by
      by_cases hz : 1 ≤ ‖y‖
      · calc
             _ ≤ ‖y‖^k:=pow_le_pow_right₀ hz hi
             _ ≤ _ :=(le_mul_of_one_le_left (pow_nonneg (norm_nonneg _) _) ha)
      · have ht : 1 ≤ a * ‖y‖^k:=by
              dsimp [a]; rw [← mul_pow];apply one_le_pow₀; calc
                    _ = s⁻¹ * s := (inv_mul_cancel₀ hs.ne').symm
                    _ ≤ s⁻¹ * ‖y‖ := by gcongr
                    _ ≤ _ := (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg y))
        exact (pow_le_one₀ (norm_nonneg _) (not_le.mp hz).le).trans ht
  rw [remainder,taylorCut,if_pos (not_lt.mp hh),polynomial,← hk']
  apply (norm_sub_le ..).trans
  have h0: ‖φ y‖ ≤ ‖y‖^k*a*B:=h.value y|>.trans (le_mul_of_one_le_left hf (by rw [mul_comm]; simpa only [pow_zero] using (hm 0 (Nat.zero_le _))))
  have hz:∀ i∈Finset.range k, ‖jet i φ 0 y‖ ≤ ‖y‖^k*a*B:=fun i hi=> (norm_jet h (Finset.mem_range.mp hi).le (0:E) y).trans (by rw [sub_zero]; grw [hm i (Finset.mem_range.mp hi).le]; exact le_of_eq (by ring))
  have hS : ‖∑ i∈Finset.range k,jet i φ 0 y‖ ≤ (Finset.range k).card * (‖y‖^k*a*B):= (norm_sum_le ..).trans (Finset.sum_le_card_nsmul _ _ _ hz |>.trans_eq (nsmul_eq_mul ..))
  have hχ: ‖chi s y • ∑ i∈Finset.range k,jet i φ 0 y‖ ≤ (Finset.range k).card * (‖y‖^k*a*B):=by
      rw [norm_smul,Real.norm_of_nonneg (chi_nonneg ..)]; exact (mul_le_of_le_one_left (norm_nonneg _) (chi_le_one ..)).trans hS
  exact (add_le_add h0 hχ).trans_eq (show _ = _ by change _ = ‖y‖^k * _;dsimp [c']; ring)

def normal (E:Type*)[AddCommGroup E][Module ℝ E] : ℕ := Module.finrank ℝ E

section
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma meas_power (p:ℝ): Measurable (fun x:E=>‖x‖^p):= continuous_norm.measurable.pow_const _
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma meas_power' (p:ℝ):AEStronglyMeasurable (μ:=(volume:Measure E)) (fun x:E=>‖x‖^p):= (meas_power p).aestronglyMeasurable
end
variable [(volume:Measure E).IsAddHaarMeasure] (hd : 0 < normal E)
include hd
lemma bound_power (p:ℝ)(h:-↑(normal E)<p)(R:ℝ): Integrable ((closedBall 0 R).indicator (fun x:E=>‖x‖^p)):=by
  rw [integrable_indicator_iff measurableSet_closedBall]
  apply IntegrableOn.mono_set (t:=ball (0:E) (R+1)) _ (closedBall_subset_ball (lt_add_one _))
  refine integrableOn_ball_of_norm_le_rpow (C:=1) (α:= -p) hd (neg_lt.mp h) ?_ (meas_power' p); filter_upwards with y; simp [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg y) p)]

lemma absolute (s:ℝ)(hs:0<s)(m:ℤ)(p:ℝ)(h:-↑(normal E)<p+((m+1).toNat:ℕ))(R:ℝ) : ∃ C:ℝ,0≤C∧ ∀ φ:Trial E,support ⇑φ⊆closedBall 0 R → ∀ {B},Major (m+1).toNat φ B →
    Integrable (fun y=>‖y‖^p * ‖remainder s m φ y‖) ∧ ∫ y,‖y‖^p * ‖remainder s m φ y‖ ≤ C*B:=by
  classical obtain ⟨c,hc,H⟩:= rem_tame (E:=E) s hs m
  let R':=max (2*s) R
  let μ(x:E):ℝ:= ‖x‖^p; let τ(x:E):ℝ:= ‖x‖^(p+((m+1).toNat:ℕ)); let cut(x:E):ℝ:= ((closedBall 0 R')).indicator τ x
  have hg:Integrable cut:= bound_power hd (p+((m+1).toNat:ℕ)) h R'
  refine ⟨c*(∫ y,cut y),mul_nonneg hc (integral_nonneg (fun x=> ?_)),fun φ hp B' hB=>?_⟩
  · by_cases hx:x∈(closedBall 0 R'); unfold cut; rw [indicator_of_mem hx]; apply Real.rpow_nonneg (norm_nonneg x); rw [show cut x=0 by simp [cut,hx]]; exact le_refl _
  let f(y):= μ y * ‖remainder s m φ y‖
  have _ : Nontrivial E:= Module.nontrivial_of_finrank_pos hd
  have hm : ∀ᵐ y ∂(volume:Measure E), ‖f y‖ ≤ cut y * (c*B'):= by
     filter_upwards [(volume:Measure E).ae_ne 0] with y hy
     rw [Real.norm_of_nonneg (show 0≤f y from mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _))]; by_cases hx:y∈(closedBall 0 R')
     · unfold f cut μ τ; rw [indicator_of_mem hx, Real.rpow_add (norm_pos_iff.mpr hy),Real.rpow_natCast, mul_assoc];exact mul_le_mul_of_nonneg_left (H φ hB y) (Real.rpow_nonneg (norm_nonneg _) _)
     unfold f cut; rw [indicator_of_notMem hx]; rw [mem_closedBall_zero_iff,not_le] at hx; rw [rem_outside s hs _ _ hp (lt_of_le_of_lt (le_max_right ..) hx) (lt_of_le_of_lt (le_max_left ..) hx),norm_zero,zero_mul,mul_zero]
  have ht:= hg.mul_const (c*B')
  have hf:= ht.mono' (show AEStronglyMeasurable f from (by exact (meas_power' p).mul ((rem_continuous φ s m).aestronglyMeasurable.norm))) hm
  exact ⟨hf,(integral_mono_ae hf ht (hm.mono fun y hy=> (le_abs_self _).trans hy)).trans_eq (by rw [integral_mul_const]; ring)⟩

/-- Uniform absolute integral estimate at one subtraction length. The constant does not depend on the tested kernel except through the displayed envelope. -/
lemma Abs_pair (s:ℝ)(hs:0<s)(m:ℤ)(p:ℝ)(h:-↑(normal E)<p+((m+1).toNat:ℕ))(R:ℝ) : ∃ C:ℝ,0≤C∧ ∀ φ:Trial E,support ⇑φ⊆closedBall 0 R → ∀ {f:E→ℂ}{D B},0≤D→ Major (m+1).toNat φ B → AEStronglyMeasurable f → Estimate (max (2*s) R) p D f →
    Integrable (fun y=> remainder s m φ y * f y) ∧ ∫ y, ‖remainder s m φ y * f y‖ ≤ D*C*B:=by
  obtain ⟨c,hc,H⟩:=absolute hd s hs _ p h R
  refine ⟨c,hc,fun φ hφ f D B hD hB hf hF=>?_⟩
  obtain ⟨hg,hL⟩:=H φ hφ hB
  let μ(x:E):ℝ:= ‖x‖^p
  let w(y:E):= remainder s m φ y*f y; let z(y:E):=μ y * ‖remainder s m φ y‖
  have _ : Nontrivial E:= Module.nontrivial_of_finrank_pos hd
  have hw : ∀ᵐ y∂(volume:Measure E), ‖w y‖ ≤ D * z y:=by
    filter_upwards [(volume:Measure E).ae_ne 0] with y hy
    by_cases hx:‖y‖ ≤ max (2*s) R
    · dsimp [w,z,μ]; rw [norm_mul,←mul_assoc D,mul_comm]; exact mul_le_mul_of_nonneg_right (hF y hy hx) (norm_nonneg (remainder s m φ y))
    have hh:= not_le.mp hx; dsimp [w,z]; rw [rem_outside s hs _ _ hφ (lt_of_le_of_lt (le_max_right ..) hh) (lt_of_le_of_lt (le_max_left ..) hh),zero_mul,norm_zero,mul_zero,mul_zero]
  have ht:Integrable w:= (hg.const_mul D).mono' ((rem_continuous φ s m).aestronglyMeasurable.mul hf) hw
  refine ⟨ht,(integral_mono_ae ht.norm (hg.const_mul D) hw).trans ?_⟩
  rw [integral_const_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left hL hD

section
omit hd
lemma quasi_pull {r:ℝ}(hr:r≠0): Measure.QuasiMeasurePreserving (fun y:E=>r • y):= ⟨
   ((continuous_const_smul r).comp continuous_id).measurable, by
     intro s h; exact_mod_cast (congr($((volume:Measure E).map_addHaar_smul hr) s)).trans (by simp [Measure.smul_apply,h])⟩
end

/-- Uniform relative-error estimate after changing variables to scaled coordinates. -/
lemma abs_shrinking (m:ℤ)(p:ℝ)(h:-↑(normal E)<p+((m+1).toNat:ℕ))(R:ℝ) : ∃ C:ℝ,0≤C∧ ∀ φ:Trial E,support ⇑φ⊆closedBall 0 R → ∀ {r},0<r→ ∀ {f:E→ℂ}{D B},0≤D→ Major (m+1).toNat φ B → AEStronglyMeasurable f → Estimate (max 2 R) p D (fun z:E=>f (r • z)) →
    Integrable (fun y=> remainder r m (shrinking r φ) y * f y) ∧ ∫ y, ‖remainder r m (shrinking r φ) y * f y‖ ≤ D*C*B:=by
  obtain ⟨c,hc,hc'⟩:= Abs_pair hd 1 zero_lt_one m p h R
  refine ⟨c,hc,fun φ hφ r hr f D B hD hB hf hF=>?_⟩
  let w(y:E):= remainder 1 m φ y * f (r • y)
  obtain ⟨hw,hL⟩:= hc' φ hφ hD hB (hf.comp_quasiMeasurePreserving (quasi_pull hr.ne')) (show Estimate (max (2*1) R) p D (f ∘ (fun y:E=> r • y)) from by change Estimate (max (2*1) R) p D ((fun z:E=>f (r • z))); simpa only [mul_one] using hF)
  have he : (fun y=> remainder r m (shrinking r φ) y * f y)= shrink r w:=by
    funext y; rw [shrinking_fun,remainder_shrink r]; simp only [shrink_apply, w, Complex.real_smul, smul_inv_smul₀ hr.ne' y, mul_assoc]
  rw [he]
  refine ⟨hw.comp_smul (inv_pos.mpr hr).ne'|>.smul _,?_⟩
  have ht : ‖(r^(normal E):ℝ)⁻¹‖=(r^normal E)⁻¹:=Real.norm_of_nonneg (inv_pos.mpr (pow_pos hr _)).le
  simp_rw [congr_fun he,shrink_apply, norm_smul]
  unfold normal at ht
  simp_rw [ht]; rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg _ (fun z=> ‖w z‖) hr.le]; rwa [smul_eq_mul,inv_mul_cancel_left₀ (pow_pos hr _).ne']

/-- Scalar channel of the root prescription. -/
def average (s:ℝ)(m:ℤ)(f:E→ℂ) (φ:E→ℂ) := ∫ y, remainder s m φ y * f y

section
omit hd [(volume:Measure E).IsAddHaarMeasure] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
-- `unfold` before rewriting multilinear derivative maps
lemma rem_add (s : ℝ)(m:ℤ)(φ ψ:Trial E): remainder s m (φ + ψ : Trial E) = remainder s m φ+remainder s m ψ:= by
  funext y
  have hj:polynomial m.toNat (φ + ψ : Trial E) 0 y=polynomial m.toNat φ 0 y+polynomial m.toNat ψ 0 y:= by simp [polynomial,show jet (E:=E) _ (_ :Trial E) 0 y=jetLM _ 0 _ y from rfl,← Finset.sum_add_distrib]
  unfold remainder taylorCut; dsimp; split_ifs; · rw [hj,add_apply]; ring
  rw [add_apply,sub_zero,sub_zero,sub_zero]
lemma rem_smul (s:ℝ)(m:ℤ)(φ:Trial E)(v:ℂ): remainder s m (v • φ:Trial E) = v • remainder s m φ:=by
  funext y
  have hj:polynomial m.toNat (v • φ:Trial E) 0 y=v • polynomial m.toNat φ 0 y:= by simp [polynomial,show jet (E:=E) _ (_ :Trial E) 0 y=jetLM _ 0 _ y from rfl,Finset.mul_sum]
  unfold remainder taylorCut; dsimp; split_ifs; · rw [hj,smul_apply,smul_eq_mul,smul_eq_mul]; ring
  rw [sub_zero,sub_zero,smul_apply,smul_eq_mul]
end

variable {s:ℝ}(hs:0<s){m:ℤ}{p:ℝ}(hh:-↑(normal E)<p+((m+1).toNat:ℕ)){f:E→ℂ}(h:Growth p f)
include hs hh h

lemma integral_paid (R:ℝ)(hR:0<R): ∃ C:ℝ, 0≤C∧∀ (φ:Trial E), support ⇑φ ⊆ closedBall 0 R →∀ {B},Major (m+1).toNat φ B → Integrable (fun y=>remainder s m φ y * f y) ∧ ‖average s m f φ‖ ≤ C*B :=by
  obtain ⟨a,ha,hL⟩:= Abs_pair hd s hs m p hh R
  obtain ⟨D,hD,H⟩:= h.2 _ (hR.trans_le (le_max_right ..))
  exact ⟨D*a,mul_nonneg hD ha,fun φ hp _ hφ=> ⟨(hL φ hp hD hφ h.1 H).1,(norm_integral_le_integral_norm _).trans (hL φ hp hD hφ h.1 H).2⟩⟩

lemma integrable_pair (φ:Trial E): Integrable (fun y=>remainder s m φ y * f y):=by
  obtain ⟨R,hR,hφ⟩:= φ.hasCompactSupport.isBounded.exists_pos_norm_le
  exact (Classical.choose_spec (integral_paid hd hs hh h R hR)|>.2 φ
    (fun x hx=> mem_closedBall_zero_iff.mpr (hφ x (subset_closure hx))) (Classical.choose_spec (φ.majorant _))).1

def avgLM : Trial E →ₗ[ℂ] ℂ where
  toFun φ:=average s m f φ
  map_add' φ ψ:=by
    unfold average; simp_rw [rem_add, Pi.add_apply, add_mul]; exact integral_add (integrable_pair hd hs hh h φ) (integrable_pair hd hs hh h ψ)
  map_smul' v φ:=by
    unfold average; simp only [rem_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]; exact integral_const_mul v _

lemma controls_average: Controlled (avgLM hd hs hh h) (m+1).toNat :=by
  intro R hR
  obtain ⟨C,hC,H⟩:= integral_paid hd hs hh h R hR
  exact ⟨C,hC,fun φ hφ B hB=> by change ‖average ..‖≤ _; exact (H φ (hφ.trans Set.inter_subset_right) hB).2 ⟩

def reading : Reading E:=(controls_average hd hs hh h).view _

@[simp] lemma reading_apply (φ:Trial E):reading hd hs hh h φ=average s m f φ:=rfl

omit hs hh h hd [FiniteDimensional ℝ E] [BorelSpace E] [(volume:Measure E).IsAddHaarMeasure] in
lemma reads_separated (φ:Trial E) (hx:(0:E)∉tsupport φ) : average s m f φ = ∫ y, φ y * f y:=by
  unfold average; apply integral_congr_ae; filter_upwards with y; congr 1
  unfold remainder taylorCut; split_ifs
  · rw [polynomial,Finset.sum_eq_zero (fun i _=> ?_),smul_zero,sub_zero]; unfold jet
    have h := Function.notMem_support.mp (show (0:E)∉support (iteratedFDeriv ℝ i (⇑φ)) from fun hy=> hx (support_iteratedFDeriv_subset i hy))
    simp [h]
  rw [sub_zero]

end YM.Contacts
