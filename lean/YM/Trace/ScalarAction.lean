import YM.Trace.Fields
import YM.Next.BOUNDARY.Decomposition
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.Trace
open Boundary MeasureTheory Mink Set Filter Function Complex
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace ContDiff NNReal ENNReal
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order} (Y : Spec.Final C f S)
lemma shell_apply (k) (g h : Lorentz) (u : S.Field k) : Y.action.spin.shell k (g*h) u = Y.action.spin.shell k g (Y.action.spin.shell k h u) := by
   have ht := Y.realization.qt.letters
   exact S.pin_inj _ <| (ht.ties ..).symm.trans (by rw [← ht.ties,← ht.ties]; exact ht.representation ..)
lemma shell_one (k : ℕ) (u : S.Field k) : Y.action.spin.shell k 1 u=u :=
   S.pin_inj _ ((Y.realization.qt.letters.ties ..).symm.trans (Y.realization.qt.letters.identity _))

lemma boost_fix {k : ℕ} (u : S.Field k) (h : ∀ p, Y.sector.turns.act k p u=u) (i : SpaceAxis) (t : ℝ) :
       Y.action.spin.shell k ((Ray.fromAxis i).boost t) u=u := by
   have hv := Y.phase.transport.spots.infinitesimal k (Ortho.plane timeAxis i.castSucc) u
   simp_rw [h] at hv
   have he := hv.unique (hasDerivAt_const _ _)
   let K := Ray.fromAxis i; let g (t : ℝ) := (Y.action.spin.shell k (K.boost t)).toLinearMap.restrictScalars ℝ |>.toContinuousLinearMap
   have h0 : HasDerivAt (fun t : ℝ => g t u) 0 0 := by
      have hQ:= Y.realization.qt.letters.boosts k i u
      rwa [he,smul_zero] at hQ
   have hA (t : ℝ) : HasDerivAt (fun t : ℝ => g t u) 0 t := by
     have hh := ((hasDerivAt_const (F:=S.Field k →L[ℝ] S.Field k) (0:ℝ) (g t)).clm_apply h0)
     have hE (s : ℝ) : g t (g s u) = g (s+t) u := by dsimp only [g,Ray.boost_add]; simp [shell_apply,add_comm] -- fix
     rw [show (0:(S.Field k →L[ℝ] S.Field k)) (g 0 u)=0 from rfl,g t|>.map_zero,add_zero] at hh
     rw [← sub_self t] at hh
     have := hh.comp_sub_const t t
     simp_rw [hE, sub_add_cancel] at this
     exact this
   exact (is_const_of_deriv_eq_zero (fun t => (hA t).differentiableAt) (fun t=> (hA t).deriv) t 0).trans
       (by change Y.action.spin.shell k _ u=u; rw [K.boost_start, shell_one])

open Next.BOUNDARY.Descent

theorem shell_fixed {k : ℕ} (u : S.Field k) (h : ∀ p : Ortho, Y.sector.turns.act k p u=u) (g : Lorentz) :
    Y.action.spin.shell k g u=u := by
   nth_rw 1 [← factors g]
   rw [shell_apply, shell_apply,shell_apply]
   rw [Y.realization.qt.letters.spatial, h]
   simp only [boost]
   simp_rw [boost_fix _ _ h]
lemma pin_scalar {k : ℕ} (u : S.Field k) (h : ∀ p : Ortho, Y.sector.turns.act k p u=u) (g : Lorentz) :
    Y.action.spin.rail g (S.pin k u)=S.pin k u := by rw [Y.realization.qt.letters.ties,shell_fixed _ _ h]
private lemma joint_moved (u : Test4) (g : Lorentz) : Joint.push (.motion g) u = Probe.along g.sends.symm u := by
   ext1 x; simp [Poincare.sends, Poincare.motion]
lemma scalar_transport {k : ℕ} (u : S.Field k) (h : ∀ p : Ortho, Y.sector.turns.act k p u=u) (g : Lorentz) (φ : Test4) :
    Y.action.action.V (.motion g) (oneWave Y (S.pin k u) φ) = oneWave Y (S.pin k u) (Probe.along g.sends.symm φ) := by
   let b := S.pin k u
   have H := Y.realization.qt.covariance.covariance (.motion g) b φ Y.action.operators.omega
   erw [pin_scalar _ _ h,joint_moved] at H
   refine H.trans ?_
   rw [(by apply Subtype.ext (Y.realization.qt.covariance.vacuum ..) : Subtype.mk (p:=fun x => x∈Y.action.operators.domain)
      (Y.action.action.V (.motion g) Y.action.operators.omega.val) _ = Y.action.operators.omega)]
   rfl

omit Y
lemma plus_moved (g : Lorentz) (f : Test4) (p : E4) : plus (Probe.along g.sends.symm f) p = plus f ((g⁻¹).dual.act p) := by
   have ht := g⁻¹.dual_sent p
   have he (x : E4) : Probe.plane (g.sends x) p = Probe.plane x (g⁻¹.dual.act p) := congrArg (fun v : ℝ=> cexp ((v:ℂ)*I)) (by simpa using (ht (g.sends x)).symm)
   simp_rw [plus_eq]
   have hq : MeasurableEmbedding (g.sends) := g.sends.toHomeomorph.measurableEmbedding
   rw [← g.preserves.integral_comp hq]; simp_rw [he,Probe.along_at, g.sends.symm_apply_apply]

lemma plus_ahead_eq (a : E4) (f : Test4) (p : E4) : plus (Probe.ahead a f) p = plus f p * Probe.plane p a := by
   simp_rw [plus_eq,Probe.ahead_at,← MeasureTheory.integral_mul_const]
   rw [← integral_add_right_eq_self (μ:=volume) (f:=fun x : E4 => Probe.plane x p * f (x-a)) a]
   apply integral_congr_ae; filter_upwards with x
   rw [Probe.plane_dot (x+a), Probe.plane_add, add_sub_cancel_right,Probe.plane_dot _ x]; ring

def FieldsNorm (μ : Measure E4) {H : Hilbert} (v : Test4 → H) : Prop := ∀ f g : Test4,
    inner ℂ (v f) (v g)=∫ k, star (plus f k)*plus g k∂μ
lemma general_charge_char (μ : Measure E4) (f : Test4) (p : E4):
    charFun (charge μ f) p = ∫ k, star (plus f k) * plus (Probe.ahead p f) k ∂μ := by
   rw [charFun_apply,charge,integral_withDensity_eq_integral_toReal_smul (measurable_price f) (.of_forall (fun _ => by finiteness))]
   apply integral_congr_ae; filter_upwards with x; rw [plus_ahead_eq,value_price,Complex.real_smul,
     ← Complex.normSq_eq_norm_sq]
   rw [← mul_assoc, mul_comm (star _) (plus f _),← starRingEnd_apply,mul_conj]; rfl
lemma charge_finite_tempered (μ : Measure E4) (h : Tempered μ) (f : Test4) : IsFiniteMeasure (charge μ f) := by
   apply isFiniteMeasure_withDensity
   obtain ⟨n,A,h⟩ := h
   have H : Integrable (fun x=> ‖plus f x‖^2) μ := by
     refine h.integrable_prod ENNReal.ofReal_lt_top (plus f) (plus f) _ ((plus f).continuous.norm.pow _|>.aestronglyMeasurable)
       1 (fun x=> by simp [sq])
   simp_rw [price_ofReal]; rw [← ofReal_integral_eq_lintegral_ofReal H (ae_of_all _ (by intro; exact sq_nonneg _))]; finiteness

/-- Spectral testing determines a *tempered nonnegative* measure without specifying other PVM components. -/
theorem charge_interrupt (μ ν : Measure E4) (hμ : Tempered μ) (hν : Tempered ν) {H : Hilbert} (v : Test4→H)
     (h : FieldsNorm μ v) (g : FieldsNorm ν v) : μ=ν := by
   have hcost (i : Test4) : charge μ i=charge ν i := by
      letI := charge_finite_tempered μ hμ i
      letI := charge_finite_tempered ν hν i
      apply Measure.ext_of_charFun
      ext1 p
      rw [general_charge_char, general_charge_char,← h _ (Probe.ahead p i), ← g i _]
   obtain ⟨u,_,hS⟩ := plus_fits (V:=E4)
   let k (n) := price (u n); let W (n) := Function.support (plus (u n)); let D := disjointed W
   have hW (n): MeasurableSet (W n) := (plus (u n)).continuous.isOpen_support.measurableSet
   have hd : univ = ⋃ n,D n := Eq.symm (Subset.antisymm (subset_univ _) (fun x _ => iUnion_disjointed (f:=W) ▸ mem_iUnion.mpr (hS x)))
   have hw (n) : μ.restrict (D n)=ν.restrict (D n) := by
      have eq (μ : Measure E4) :=
        -- divide by local price
        (withDensity_mul (μ.restrict (D n)) (measurable_price (u n)) ((measurable_price (u n)).inv))
      have hh (μ : Measure E4) : (μ.restrict (D n)).withDensity (k n * (k n)⁻¹)= μ.restrict (D n) := (withDensity_congr_ae
         ((ae_restrict_mem (MeasurableSet.disjointed hW n)).mono (fun _ hk =>
            ENNReal.mul_inv_cancel (pow_ne_zero _ (by exact enorm_ne_zero.mpr (disjointed_subset _ _ hk))) (by exact ENNReal.pow_ne_top (by exact enorm_ne_top))))).trans withDensity_one
      rw [← hh μ, eq μ, ← hh ν, eq ν,← restrict_withDensity (MeasurableSet.disjointed hW n), ← charge.eq_def, hcost,charge,
         restrict_withDensity (MeasurableSet.disjointed hW n)]
   conv_lhs => rw [← Measure.restrict_univ (μ:=μ), hd, Measure.restrict_iUnion (disjoint_disjointed _) (MeasurableSet.disjointed hW)]
   conv_rhs => rw [← Measure.restrict_univ (μ:=ν),hd,Measure.restrict_iUnion (disjoint_disjointed _) (MeasurableSet.disjointed hW)]
   change Measure.sum (fun i => μ.restrict (D i)) = _; simp_rw [hw]; rfl

include Y
theorem scalar_inner_kernel {k : ℕ} (u : S.Field k) (h : ∀ p : Ortho, Y.sector.turns.act k p u=u) (g : Lorentz)
     {μ : Measure E4} (hμ : FieldsNorm μ (oneWave Y (S.pin k u))) : FieldsNorm (Measure.map g.act μ) (oneWave Y (S.pin k u)) := by
  let a := g.dual⁻¹
  let z := S.pin k u; let v := oneWave Y z
  let ha : (Y.action.operators.H →ₗᵢ[ℂ] Y.action.operators.H) := ⟨(Y.action.action.V (.motion a)).toLinearMap,Y.action.action.usual _⟩
  intro i j
  rw [(show MeasurableEmbedding ⇑g.act from g.sends.toHomeomorph.measurableEmbedding).integral_map]
     -- `map g.act` not sends
  simp_rw [show ⇑g.act =⇑a⁻¹.dual.act from (by rw [show a⁻¹=g.dual from inv_inv _,Lorentz.dual_involution]),← plus_moved]
  rw [← hμ _ _,← scalar_transport Y _ h a, ← scalar_transport Y _ h a]
  exact (ha.inner_map_map (v i) (v j)).symm

omit Y

set_option maxHeartbeats 2000000
lemma tempered_push (μ : Measure E4) (h : Tempered μ) (g : Lorentz) : Tempered (Measure.map g.act μ) := by
  obtain ⟨d,A,h⟩ := h
  let k := max 1 ‖g⁻¹.act‖
  refine Exists.intro d (Exists.intro (A*k^d) ?_)
  change ∀ (r:ℝ), 1 ≤ r → (μ.map fun v=>g.act v) (Metric.closedBall 0 r) ≤ _
  intro r hr
  have hk : 1 ≤ k := le_max_left ..
  rw [Measure.map_apply (show Measurable g.act from g.act.continuous.measurable) Metric.isClosed_closedBall.measurableSet]
  calc
    _ ≤ μ (Metric.closedBall 0 (k*r)) := measure_mono fun x (hx : dist (g.act x) 0 ≤ r) => by
       simp only [Metric.mem_closedBall,dist_zero_right] at hx ⊢
       -- norm of inverse controls support
       rw [← Lorentz.starts g x]
       exact g⁻¹.act.le_opNorm _ |>.trans (mul_le_mul (le_max_right ..) hx (norm_nonneg _) (by linarith))
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (k*r)^d := h _ (one_le_mul_of_one_le_of_one_le hk hr)
    _ = _ := by
       rw [mul_comm A _, ENNReal.ofReal_mul (pow_nonneg (by linarith) _), ENNReal.ofReal_mul (show 0 ≤ k by linarith), ENNReal.ofReal_pow (show 0 ≤ k by linarith)]
       ring

include Y in
theorem scalar_measure_fixed {k : ℕ} (u : S.Field k) (h : ∀ p, Y.sector.turns.act k p u=u)
    (μ : Measure E4) (hm : Tempered μ) (he : FieldsNorm μ (oneWave Y (S.pin k u))) (g : Lorentz) : Measure.map g.act μ = μ :=
  charge_interrupt _ _ (tempered_push _ hm g) hm _ (scalar_inner_kernel Y u h g he) he
end YM.Trace
