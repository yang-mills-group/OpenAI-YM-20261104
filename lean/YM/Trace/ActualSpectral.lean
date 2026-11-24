import YM.Trace.Tauberian
import YM.Trace.Center
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Trace
open Set Filter MeasureTheory Function Boundary Complex
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace ContDiff ENNReal
variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order} (Y : Spec.Final C F S)
variable {μ : Measure E4}

abbrev thetaV (Y : Spec.Final C F S) (e : ℝ) := oneWave Y (S.pin 4 (theta Y e))
/-- Engineering and inverse-square-log coincidence rate in future comparison, **explicit hypothesis**
after conversion to physical labels, with actual fixed vacuum centering. -/
def LogLaw (a : ℝ) := Tendsto (fun R=> (logWeight R : ℂ) * restTrace Y (meanExact Y) R⁻¹) atTop (𝓝 ↑a)

lemma actual_thermal {a : ℝ} (e : ℝ) (h : Tendsto (fun R=> (logWeight R : ℂ) * restTrace Y e R⁻¹) atTop (𝓝 ↑a))
    (ht : FieldsNorm μ (thetaV Y e)) (hf : μ Mink.coneᶜ=0) (hm : Tempered μ) : Thermal μ a where
   future := hf
   symmetric g := scalar_measure_fixed Y _ (theta_fixed Y e) μ hm ht g
   integrates hs := hm.integrable_exp μ hf hs
   rate := by
      have hp := continuous_re.continuousAt.tendsto.comp h
      exact hp.congr' ((eventually_gt_atTop 0).mono (fun R hr => by
          have := heat_eq_rest Y hm hf e R⁻¹ (inv_pos.mpr hr) ht |>.trans integral_complex_ofReal
          dsimp only [Function.comp_apply]; rw [this,mul_re]; simp))

noncomputable def pairMomentum : E4 →L[ℝ] VPair := LinearMap.toContinuousLinearMap {
    toFun x := points (![ -x,x])
    map_add' := fun x y => PiLp.ext (fun i=> by fin_cases i <;> simp [points]; abel)
    map_smul' r x := PiLp.ext (fun i=> by fin_cases i <;> simp [points]) }
lemma pairMomentum_le (x y : E4) : dist x y ≤ dist (pairMomentum x) (pairMomentum y) := by
    rw [dist_eq_norm,dist_eq_norm, ← map_sub]
    exact PiLp.norm_apply_le (pairMomentum (x-y)) 1
lemma pair_dot (x : VPair) (p) : inner ℝ x (pairMomentum p) = inner ℝ (x 1-x 0) p := by
    rw [PiLp.inner_apply,Fin.sum_univ_two]
    simp [pairMomentum,points]; rw [inner_sub_left,sub_eq_add_neg,add_comm]

noncomputable def relative2 : Joint 2 →L[ℂ] Test4 :=
    (SchwartzMap.compCLMOfAntilipschitz ℂ pairMomentum.hasTemperateGrowth (AntilipschitzWith.of_le_mul_dist (K:=1) (by simpa using pairMomentum_le))).comp plus
lemma relative2_formula (f p) : relative2 f p = ∫ x, Probe.plane p (x 1-x 0)*f x := by
    change plus f (pairMomentum p)=_
    rw [plus_eq]; apply integral_congr_ae; filter_upwards with i
    rw [Probe.plane_dot p (i 1-i 0)]; unfold Probe.plane; rw [pair_dot]
lemma integrable_heat_probe (φ : Joint 2) {s:ℝ} (hs : 0<s) (hm : Tempered μ) (hf : μ Mink.coneᶜ=0) :
    Integrable (Function.uncurry fun x p => Probe.plane p (x 1-x 0)*damping ((s:ℂ)*I) p *φ x)
       (volume.prod μ) := by
       letI := hm.finite_compacts
       apply (integrable_prod_iff (by unfold Function.uncurry damping Probe.plane; fun_prop)).mpr
       let w (x : E4):=Real.exp (-s*Mink.clockL x)
       have he (p : VPair) (x:E4): ‖Probe.plane x (p 1-p 0) * damping (↑s*I) x * φ p‖ = w x * ‖φ p‖ := by simp [w]
       simp only [Function.uncurry_apply_pair]
       refine ⟨ae_of_all _ fun p => Integrable.mono' ((hm.integrable_exp μ hf hs).mul_const ‖φ p‖) (by unfold damping; fun_prop)
            (ae_of_all _ fun x => by simp),?_⟩
       simp_rw [show ∀ p x, ‖_‖=w x*‖φ p‖ from he, integral_mul_const]
       exact (φ.integrable.norm.const_mul _)

lemma joint_boundary (e : ℝ) (H : FieldsNorm μ (thetaV Y e)) (hm : Tempered μ) (hf : μ Mink.coneᶜ=0) (φ : Joint 2) :
     (Y.A.world.W 2 (fun _ => S.pin 4 (theta Y e))) φ = ∫ p, relative2 φ p∂μ := by
    let O : S.Tag := ⟨4,theta Y e⟩
    let L (s : ℝ) (x) := liftTwo Y O ((s:ℂ)*I) x
    have h (s:ℝ) (_hs:0<s) (x : VPair) : Y.A.waves.restricted (fun _=>S.pin 4 O.2) (s • (![0,1] : Heights 2)) x = L s x := by
         unfold Waves.restricted L liftTwo Boundary.shift height2; congr 2; ext1 i
         fin_cases i <;> simp [time]
    have hM (s : ℝ) (hs : 0<s) (x:VPair) : L s x = ∫ p, _ ∂μ := heatPoint_eq Y hm hf e H (by simpa [upper]) x
    have hx : (![0,1] : Heights 2) ∈ east 2 := by
          intro i j hij; fin_cases i <;> fin_cases j <;> try contradiction
          exact (zero_lt_one : (0:ℝ)<1)
    have he := Y.realization.chosen.emerges.profile 2 (fun _ => S.pin 4 (theta Y e)) (![0,1] : Heights 2) hx φ
    let K (x : VPair) (p : E4) (s : ℝ) := Probe.plane p (x 1 - x 0) * damping (s*I) p * φ x
    let r := relative2 φ
    have hs (s : ℝ) (p) : (∫ x,K x p s)= damping (s*I) p * r p  := by
          unfold K r; rw [relative2_formula,← integral_const_mul]; apply integral_congr_ae; filter_upwards with x

          ring
    have hd : (fun s : ℝ=> Waves.atSlopes Y.A.waves (fun _=>S.pin 4 (theta Y e)) (![0,1]) s φ) =ᶠ[𝓝[>] 0] fun s => ∫ p,damping (s*I) p * r p ∂μ := by
       haveI := hm.finite_compacts
       filter_upwards [self_mem_nhdsWithin] with s (hp:0<s)
       unfold Waves.atSlopes
       change (∫ p, Y.A.waves.restricted (fun _=>S.pin 4 O.2) _ p * _) = _
       simp_rw [show ∀ x, Y.A.waves.restricted ..= _ from fun x : VPair => ((h _ hp x).trans (hM s hp x) :
            Y.A.waves.restricted .. = ∫ p, Probe.plane p (x 1-x 0)* damping (↑s*I) p ∂μ), ← integral_mul_const]
       rw [integral_integral_swap (integrable_heat_probe φ hp hm hf)]
       exact integral_congr_ae (Filter.Eventually.of_forall (fun i => hs _ i))
    refine tendsto_nhds_unique_of_eventuallyEq he (g:=fun s : ℝ=> ∫ p,damping (s*I) p * r p ∂μ) ?_ hd
    refine tendsto_integral_filter_of_dominated_convergence (fun x:E4 => ‖r x‖) (.of_forall fun _=> by unfold damping; fun_prop)
       ?_ ((Tempered.integrable μ hm ..).norm) (.of_forall fun x => ?_)
    swap
    · simpa only [damping,ofReal_zero,zero_mul,mul_zero,exp_zero,one_mul] using! (by fun_prop : ContinuousAt
        (fun s : ℝ=> cexp ((time x: ℂ)*I*(s*I)) * r x) (0:ℝ)).tendsto |>.mono_left nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin] with i (hi : i>0)
    filter_upwards [(show ∀ᵐ p ∂μ, p∈Mink.cone from ae_iff.mpr hf)] with y hy
    norm_num; exact mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr
       (mul_nonneg hi.le ((Mink.cone_self y|>.mp hy).1))))
-- measure-as-tempered distribution lemma
/-- Positive scalar measure interpreted as a (weak) tempered distribution. -/
def Tickets {μ:Measure E4} (h : Tempered μ) : Distn E4 := by
   let L : Test4 →ₗ[ℂ] ℂ := { toFun f := ∫ p,f p∂μ
                              map_add' f g := integral_add (h.integrable μ f) (h.integrable μ g)
                              map_smul' c f := by exact MeasureTheory.integral_smul c f }
   apply ContinuousLinearMap.mk L (continuous_of_continuousAt_zero L _) -- tactic goal value? non-prop elimination issue use proof then refine exact
   obtain ⟨n,A,ht⟩ := h
   let k := ((2:ℝ)^(n+1)) * (Real.toNNReal A*(2^(n+1))) + 1
   have hk : 0<k := by dsimp only [k]; positivity
   have hb (f) : ‖L f‖ ≤ orderCost f (n+1)*k := (ht.test_abs ENNReal.ofReal_lt_top f).trans (by
     rw [mul_assoc]; apply mul_le_mul_of_nonneg_left ?_ (orderCost_nonneg ..)
     unfold k; rw [ENNReal.ofReal,ENNReal.coe_toReal]; linarith)
   change ContinuousAt L 0
   unfold ContinuousAt; rw [L.map_zero]
   refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (.of_forall fun _=> norm_nonneg _)
       (.of_forall hb) ((continuous_orderCost _|>.continuousAt.tendsto.mul_const k).trans (by
          simp only [orderCost,Probe.size,map_zero,zero_add,zero_mul]; exact tendsto_id)))

lemma Tickets_eval {μ} (h : Tempered μ) (f) : Tickets h f = ∫ x, f x ∂μ := rfl

/-- Wightman two-point of the centered field with both positions read in R^-1 units,
including the adjoint first (label is self-adjoint). No scaling of the field included here. -/
def spacetimeScaled (e R : ℝ) (φ : Joint 2) : ℂ := Y.A.world.W 2 (fun _:Fin 2=>S.pin 4 (theta Y e)) (normalized φ R)
lemma scaling_formula (e : ℝ) (H : FieldsNorm μ (thetaV Y e)) (hm : Tempered μ) (hf : μ Mink.coneᶜ=0) (φ : Joint 2) {R : ℝ} (hr : 1<R) :
     logWeight R • spacetimeScaled Y e R φ = ∫ p, relative2 φ p∂rescaled μ R := by
  have Hc : FiniteDimensional ℝ VPair := inferInstance
  rw [spacetimeScaled,joint_boundary Y e H hm hf,rescale_integral _ hr]
  congr 1 ; apply MeasureTheory.integral_congr_ae
  filter_upwards with i
  change plus (normalized φ R) (pairMomentum i)=plus φ (pairMomentum (R⁻¹ • i))
  rw [plus_normalized _ (zero_lt_one.trans hr), pairMomentum.map_smul]

/-- Reduction for the actual ordered construction. This theorem requires the Euclidean
leading estimate `LogLaw`; it **proves** the spectral, relative and joint-distribution
limits under that rate and the calculation of the reference Laplace integrals (shadow
for the reference measure). Uses the same stress `theta Y e` / `traceField Y`, the same
`Contour` and the same Wightman system. No choice of a new physical model. -/
theorem conditional_distributional {A : ℝ} (e : ℝ) (H : e=meanExact Y) (h : LogLaw Y A)
   (ν : Measure E4) (hg : Shadow ν) (hl : ∀ x∈Mink.inside, ∫ p, exponential p x∂ν=A/(Mink.m x)^4)
   (hv : Tempered ν): ∃ M : Measure E4,∃ hm : Tempered M, FieldsNorm M (thetaV Y e) ∧ Thermal M A ∧
          (∀ s>0, restTrace Y e s = (∫ p,Real.exp (-s*time p)∂M : ℝ)) ∧
          (∀ φ : E4→ℂ, Continuous φ→HasCompactSupport φ→ Tendsto (fun r => ∫ p,φ p∂rescaled M r) atTop (𝓝 (∫ p,φ p∂ν))) ∧
          (∀ φ : Test4, (∫ k,φ k∂M) = Tickets hm φ ∧ Tendsto (fun r => ∫ p, φ p ∂rescaled M r) atTop (𝓝 (Tickets hv φ))) ∧
          (∀ φ : Joint 2, Tendsto (fun r => logWeight r • spacetimeScaled Y e r φ) atTop (𝓝 (∫ p, relative2 φ p∂ν))) := by
   obtain ⟨M,hm,hM,hS,he⟩ := centered_spectral Y
   have heq : FieldsNorm M (thetaV Y e) := by subst e; exact he
   have ht : Thermal M A := actual_thermal Y e (by subst e; exact h) heq hM hm
   have hmatch := ht.matches hg hl
   obtain ⟨m',B,hρ⟩:=hv
   obtain ⟨C,hC,hB⟩:=Thermal.growth_bound ht
   have hvague := hmatch.vagueC (hB.mono (fun i hi => hi.finite_compacts hC.ne)) (hρ.finite_compacts (by finiteness))
   have hs := hmatch.schwartz hC ENNReal.ofReal_lt_top hB hρ
   refine ⟨M,hm,heq,ht,H ▸ hS,hvague, fun φ=>⟨rfl,hs φ⟩,fun φ=> (hs _).congr' ?_⟩
   exact (eventually_gt_atTop (1:ℝ)).mono fun r hr => (scaling_formula Y e heq hm hM φ hr).symm
end YM.Trace
