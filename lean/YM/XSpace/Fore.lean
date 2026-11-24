import YM.XSpace.Prima

/-!
# Convergent cover quadratures
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Playpen
open MeasureTheory Function Set Filter Future Lattice Scale Sail Further.FreeCovariance.KP
open scoped Topology BigOperators
variable {b:ℝ}
def actual (a:ℝ)(x:Cover):= a • rcast x
def dock (a:ℝ)(x:Cover): Set E4:={p| mark a p=x}
private lemma docking (h:0<b)(x:Cover): MeasurableSet (dock b x)∧ volume (dock b x) = ENNReal.ofReal (b^4):=by
  let v(z:ℤ):= Ico (b*(z:ℝ)) (b*((z:ℝ)+1)); rw [show dock b x=WithLp.ofLp ⁻¹' pi univ (fun i=>v (x i)) from ?_]
  · have hh:=PiLp.volume_preserving_ofLp Axis; have he: MeasurableSet (pi univ fun i=>v (x i)):=MeasurableSet.pi countable_univ fun i _=> measurableSet_Ico
    refine ⟨hh.measurable he,?_⟩; rw [hh.measure_preimage he.nullMeasurableSet]; change Measure.pi _ _=_; rw [Measure.pi_pi]; have ht(k:ℤ): volume (v k)=ENNReal.ofReal b:=by unfold v; rw [Real.volume_Ico]; congr 1; ring
    simp_rw [ht]; simp [ENNReal.ofReal_pow h.le]
  ext p; simp only [dock,mark,v,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_pi,Set.mem_univ,forall_true_left,funext_iff,Int.floor_eq_iff,le_div_iff₀ h,div_lt_iff₀ h,mem_Ico,mul_comm]
def steps (a:ℝ)(v:Cover→ℂ)(p:E4):ℂ:=(a:ℂ)⁻¹^4*v (mark a p)
lemma current (p:ℝ)(h:0<p)(x:E4) : ‖actual p (mark p x)-x‖≤2*p:=by
  apply le_of_sq_le_sq _ (by positivity); rw [PiLp.norm_sq_eq_of_L2]; 
  calc
    _ ≤ ∑ _:Axis,p^2:=Finset.sum_le_sum fun i _=> pow_le_pow_left₀ (norm_nonneg _) (marked_bound h x i) _
    _ = _:=by simp; ring
lemma fees_ok (v:Cover→ℂ)(h:0<b): Measurable (steps b v):=by
  apply Measurable.const_mul; apply (measurable_of_countable v).comp
    (show Measurable (mark b) from measurable_pi_lambda _ (fun i=> ?_))
  exact (((EuclideanSpace.proj i (𝕜:=ℝ)).continuous.measurable).div_const b).floor
lemma exch (v:Cover→ℂ)(h:0<b)(hx: Integrable (steps b v)): HasSum v (∫ x:E4, steps b v x):=by
  have he: ∀ n,MeasurableSet (dock b n):=fun _=>(docking h _).1; have hs:(⋃ i,dock b i)=Set.univ:= Set.eq_univ_of_forall fun x=> mem_iUnion.mpr ⟨_,(show mark b x=mark b x from rfl)⟩
  have H:= hasSum_integral_iUnion (f:=steps b v) he (fun i j hij=> Set.disjoint_left.mpr (fun v (h: mark b v=i) (g: mark b v=j)=>hij (h.symm.trans g))) hx.integrableOn
  rw [hs,setIntegral_univ] at H; apply H.congr_fun -- method?
  intro i; symm; change (∫ x in dock b i, _)=v i; rw [setIntegral_congr_fun (g:=fun _=>(b:ℂ)⁻¹^4*v i) (he _) (fun x (hx: mark b x=i)=> by simp [steps,hx]), setIntegral_const]; simp only [measureReal_def,(docking h i).2, ENNReal.toReal_ofReal (pow_nonneg h.le _), Complex.real_smul]; rw [Complex.ofReal_pow, inv_pow, mul_inv_cancel_left₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr h.ne'))]

variable {ι:Type*}{L: Filter ι}{A:ι→ℝ}
lemma marks (u:E4)(S:Tendsto A L (𝓝 0))(he:∀ᶠ i in L,0<A i): Tendsto (fun i=> actual (A i) (mark (A i) u)) L (𝓝 u):=by rw [tendsto_iff_dist_tendsto_zero]; exact squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) (he.mono fun i hi=> dist_eq_norm (actual (A i) (mark (A i) u)) u ▸ current _ hi u) (by simpa using S.const_mul 2)
abbrev Issued (L:Filter ι)(p:ι→Cover→ℂ): Prop:= (∀ᶠ i in L,Summable (p i)) ∧ Likely L fun i=> ∑' x:Cover,p i x
lemma flight [L.IsCountablyGenerated](p:ι→Cover→ℂ){f:E4→ℝ}(he:∀ᶠ i in L,0<A i)(hf:Integrable f)(u:E4→ℂ)
    (hp: ∀ᶠ i in L,∀ᵐ x:E4, ‖steps (A i) (p i) x‖ ≤ f x)(h: ∀ᵐ x:E4,Tendsto (fun i=> steps (A i) (p i) x) L (𝓝 (u x))): (∀ᶠ i in L,Summable (p i)) ∧ Tendsto (fun i=>∑' x:Cover,p i x) L (𝓝 (∫ x,u x)):=by
  have hx:∀ᶠ i in L, HasSum (p i) (∫ x,steps (A i) (p i) x):= by filter_upwards [he,hp] with i hi hh; exact exch _ hi (hf.mono' ((fees_ok _ hi).aestronglyMeasurable) hh)
  exact ⟨hx.mono (fun i hi => hi.summable),(tendsto_integral_filter_of_dominated_convergence f (he.mono fun i hi=>(fees_ok _ hi).aestronglyMeasurable) hp hf h).congr' (hx.mono fun i hi=> hi.tsum_eq.symm)⟩
lemma speeds [L.IsCountablyGenerated](p:ι→Cover→ℂ){f:E4→ℝ}(he:∀ᶠ i in L,0<A i)(hf:Integrable f)
    (hp: ∀ᶠ i in L,∀ᵐ x:E4, ‖steps (A i) (p i) x‖ ≤ f x)(h: ∀ᵐ x:E4,Likely L (fun i=> steps (A i) (p i) x)): Issued L p:=by
  classical
  let u (x:E4) := if he:Likely L (fun i=> steps (A i) (p i) x) then he.choose else 0
  obtain ⟨P,T⟩:=flight p he hf u hp (h.mono fun x hx=> by rw [show u x=hx.choose from dif_pos hx]; exact hx.choose_spec)
  exact ⟨P,_,T⟩
open Metric
lemma almost_all : ∀ᵐ x:E4,x≠0 := mem_ae_iff.mpr (by change volume ({x:E4 | x≠0}ᶜ)=0; simp)
lemma near_minor (b:ℝ): Integrable ((ball (0:E4) b).indicator (fun x=>(‖x‖^3)⁻¹)):=by
  apply IntegrableOn.integrable_indicator _ measurableSet_ball; apply integrableOn_ball_of_norm_le_rpow (by simp [E4,Axis]) (α:= (↑(3:ℕ):ℝ)) (by norm_num [E4,YM.Axis]) (C:=1) _ ((measurable_norm.pow_const _).inv.aestronglyMeasurable)
  apply Eventually.of_forall; intro p; rw [Real.rpow_neg (norm_nonneg _),Real.rpow_natCast]; simp

-- bound uses rough native amplitude λ^-3 for x near origin of integral
lemma close_pay (C B:ℝ)(p:ι→Cover→ℂ)(hc:0≤C)(he:∀ᶠ i in L, 0<A i)(H:∀ᶠ i in L,∀ x:Cover,p i x≠0→ A i*Drama.area x ≤ B ∧ ‖p i x‖ ≤ C*A i*(Drama.area x^3)⁻¹): ∀ᶠ i in L,∀ᵐ x:E4, ‖steps (A i) (p i) x‖ ≤ C*64*(ball (0:E4) (4*B+1)).indicator (fun x=>(‖x‖^3)⁻¹) x:=by
  filter_upwards [he,H] with i hi hh; filter_upwards [almost_all] with x hx; let y:=mark (A i) x; set a:=A i; have he:y=mark a x:=rfl; unfold steps; by_cases h:p i y=0; rw [← he,h,mul_zero,norm_zero]; exact mul_nonneg (by positivity) (indicator_nonneg (fun i _=> by positivity) _)
  set K:=Drama.area y; have hk :0<K:=Drama.included y; rw [← he]; have hw:=hh y h; change a*K ≤ B ∧ ‖p i y‖ ≤C*a*(K^3)⁻¹ at hw
  have hx':‖x‖ ≤ 4*(a*K):=calc
     _ ≤ 2*a+ ‖actual a y‖:= by have hh:=current a hi x; rw [← he,norm_sub_rev] at hh; exact (norm_le_norm_sub_add x (actual a y)).trans (by linarith)
     _ ≤ _:= by rw [actual,norm_smul,Real.norm_of_nonneg hi.le]; have hh:‖rcast y‖≤2*(reach y:ℝ):=(west _).2; unfold K Drama.area; nlinarith [Drama.room y]
  have hh:0<‖x‖:=norm_pos_iff.mpr hx
  rw [indicator_of_mem (by rw [mem_ball_zero_iff]; linarith [hw.1]), norm_mul,norm_pow,norm_inv,Complex.norm_real,Real.norm_of_nonneg hi.le]; apply (mul_le_mul_of_nonneg_left hw.2 (pow_nonneg (inv_nonneg.mpr hi.le) 4)).trans; calc
    _ = C*((a*K)^3)⁻¹:= by field_simp
    _ ≤ _:= by
      rw [mul_assoc C]; gcongr C*?_; have ht:(a*K:ℝ)>0:=by positivity
      field_simp; exact (pow_le_pow_left₀ hh.le hx' 3).trans_eq (by ring)
end YM.XSpace.Playpen
