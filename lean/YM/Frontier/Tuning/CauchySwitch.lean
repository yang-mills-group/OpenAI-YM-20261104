import YM.Frontier.Tuning.ContourGerm

/-! First coefficient subtraction without assuming commutation of mesh-direction jets. One finite-order consequence of Cauchy on a compact unit contour. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Frontier.Tuning.CauchySwitch
open Filter Function Set MeasureTheory Complex Metric Topology ContourGerm
open ConnectedActivityE6.Blaze
open scoped Topology Real ContDiff Interval
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E][FiniteDimensional ℝ E]{x:E}{j:ℕ}{g:E→ℂ→ℂ}
local notation "μ" => (volume.restrict (Icc 0 (2*π)):Measure ℝ)
def turn (t:ℝ):= circleMap 0 1 t
lemma turn_norm (t:ℝ): ‖turn t‖=1:=by simp [turn]
lemma turn_b (t:ℝ):turn t∈ sphere (0:ℂ) 1:=by rw [mem_sphere,dist_zero_right];exact turn_norm t
lemma turn_large (t:ℝ):turn t∈ ball (0:ℂ) 2:= by rw [mem_ball,dist_zero_right]; exact (turn_norm t).trans_lt (by norm_num)
lemma turn_ne (t:ℝ):turn t≠0:= by rw [← norm_ne_zero_iff,turn_norm]; exact one_ne_zero

def gback (z:ℂ):= (2*↑π*Complex.I)⁻¹ * Complex.I / z
def reads (f:E→ℂ→ℂ)(y:E)(θ:ℝ):=gback (turn θ) * f y (turn θ)
lemma read_bound (t:ℝ): ‖gback (turn t)‖=‖gback 1‖:=by unfold gback; rw [norm_div,norm_div,turn_norm,norm_one]
lemma read_eq {f:ℂ→ℂ}(hF:DifferentiableOn ℂ f (closedBall (0:ℂ) 1)): deriv f 0=∫ t,gback (turn t)*f (turn t) ∂μ:=by
  have h :=DifferentiableOn.deriv_eq_smul_circleIntegral one_pos hF; rw [circleIntegral_def_Icc] at h
  have hp (t:ℝ): gback (turn t)*f (turn t) = (2*(Real.pi:ℂ)*Complex.I)⁻¹ • (deriv (circleMap 0 1) t • ((1/(turn t-0)^2) • f (turn t))):=by
    unfold gback; rw [sub_zero,one_div, smul_eq_mul, smul_eq_mul,smul_eq_mul,deriv_circleMap]; unfold turn; field_simp [show ∀ t:ℝ, circleMap (0:ℂ) 1 t ≠ 0 from turn_ne]
  simp_rw [hp]
  rw [integral_smul]; change _ = (2*(π:ℂ)*Complex.I)⁻¹ • ∫ t, deriv (circleMap 0 1) t • ((1/(circleMap 0 1 t-0)^2) • f (circleMap 0 1 t)) ∂μ
  rw [h,smul_eq_mul,smul_eq_mul]; rw [inv_mul_cancel_left₀] <;> first | rfl | exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) Complex.I_ne_zero

lemma swap_first (hP:Box (closedBall 0 2) g x j):
    let f(y:E):= deriv (g y) 0; ContDiffAt ℝ (j:WithTop ℕ∞) f x ∧ ∀ k≤j,∀ m:Fin k→E,iteratedFDeriv ℝ k f x m=deriv (fun t=>iteratedFDeriv ℝ k (fun y=>g y t) x m) 0:=by
  intro first
  obtain ⟨B,hB⟩:=hP.funds; obtain ⟨W,hW,ht,hx⟩:= _root_.mem_nhds_iff.mp hB
  have hz (q:ℝ):turn q∈ closedBall (0:ℂ) 2:= ball_subset_closedBall (turn_large q)
  have hc i (hi:i∈W): Continuous (reads g i):=continuous_iff_continuousAt.mpr (fun t=>by
     unfold reads gback
     have hT (t:ℝ):ContinuousAt turn t:=by unfold turn;fun_prop
     exact ((continuousAt_const: ContinuousAt (fun _:ℝ=> (2*↑π*I)⁻¹*I) t).div (hT t) (turn_ne t)).mul (((hW hi _ (hz t)).2.continuousAt).comp (hT t)))
  have hϕ:= hW
  let D:= ‖gback 1‖* B
  have hh (t y) (hy:y∈ W):Brush j D 1 (fun y=> reads g y t) y:=by unfold reads; unfold D; rw [← read_bound t]; exact ComplexBrush.smul_left _ ((hϕ hy _ (hz t)).1)
  haveI : IsFiniteMeasure μ:= isFiniteMeasure_restrict.mpr (ne_of_lt (show (volume:Measure ℝ) (Icc 0 (2*π))<⊤ from IsCompact.measure_lt_top isCompact_Icc))
  have hm: Meristem (reads g) x μ j:= ⟨W,ht.mem_nhds hx,ae_of_all _ (fun t y hy=>(hh t y hy).smooth),fun i hi=>⟨fun _=>D,integrable_const _,fun y hy=> (Meristem.legs ht (fun t s hs=>(hh t s hs).smooth) (fun t ht=>(hc t ht).stronglyMeasurable) hi hy).aestronglyMeasurable,ae_of_all _ (fun t y hy=>by simpa using! (hh t y hy).order i hi)⟩⟩
  obtain ⟨h₁,h₂⟩:=hm.calls
  let f : E→ℂ := fun y=>∫ t,reads g y t ∂μ
  change ContDiffAt _ _ f _ at h₁
  have he : first =ᶠ[𝓝 x] f:= (show ∀ᶠ i in 𝓝 x, i∈W from ht.mem_nhds hx).mono (fun y hy=>read_eq (fun t hb=> (hW hy t (closedBall_subset_closedBall (by norm_num) hb)).2.differentiableWithinAt))
  refine ⟨h₁.congr_of_eventuallyEq he,fun k hk m=>?_⟩
  change _ = _
  rw [(he.iteratedFDeriv (𝕜:=ℝ) k).eq_of_nhds,(h₂ k hk).2, ContinuousMultilinearMap.integral_apply (h₂ k hk).1]
  have hZ:= (h₂ k hk).2
  have hg' v : JetF (reads g) k x v= gback (turn v) • JetF g k x (turn v) := by
      dsimp only [reads,JetF]; simp_rw [← smul_eq_mul (gback _)]
      exact iteratedFDeriv_const_smul_apply' ((hW hx _ (hz v)).1.smaller hk).smooth 
  simp_rw [hg']
  have hhJ:= JetHol.derivative_exchange ht (Metric.isOpen_ball (x:=(0:ℂ)) (ε:=2)) (g:=g) (by intro y hy;exact ⟨fun z hz=> (hW hy z (ball_subset_closedBall hz)).2.differentiableWithinAt,fun z hz=> (hW hy z (ball_subset_closedBall hz)).1⟩)
  apply Eq.trans _ (read_eq (hhJ k hk x hx m|>.mono (closedBall_subset_ball (by norm_num)))).symm
  exact integral_congr_ae (ae_of_all _ fun z=>rfl)
end YM.Frontier.Tuning.CauchySwitch
