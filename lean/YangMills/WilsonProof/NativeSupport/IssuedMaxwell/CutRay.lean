import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.NegativePupil
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.CutRay
open YM YM.XSpace Filter Set
open scoped ContDiff Topology
variable {n:ℕ} {x:YM.Points n}
theorem distinct (hx:x∈conf n)(t:ℝ)(ht:0<t):t • x∈conf n:=by
  intro i j eq
  apply hx
  change t • x i=t • x j at eq
  exact (smul_right_injective _ ht.ne').eq_iff.mp eq
theorem above (hx:x∈conf n)(c:Shade.Cut):∀ᶠ t:ℝ in atTop,t • x∈Photo.Good c n:=by
  have step (i j:Fin n):∀ᶠ t:ℝ in atTop,i≠j→5*c.rOut<‖t • x i-t • x j‖:=by
    by_cases he:i=j
    · exact Filter.Eventually.of_forall fun _ hn=>False.elim (hn he)
    · have hn:0<‖x i-x j‖:=norm_pos_iff.mpr (sub_ne_zero.mpr (fun h=>he (hx h)))
      filter_upwards [eventually_gt_atTop (5*c.rOut/‖x i-x j‖),eventually_gt_atTop (0:ℝ)] with t ht hz _
      rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hz]
      exact (div_lt_iff₀ hn).mp ht
  exact (Filter.eventually_all.mpr fun i=>Filter.eventually_all.mpr (step i))
theorem original {f:YM.Points n→ℂ}(hx:x∈conf n)(c:Shade.Cut)
    (smooth:∀y∈conf n,ContDiffAt ℝ ω f y)
    (dead:∀y∈conf n,y∈Photo.Good c n→f y=0):f x=0:=by
  have ray:AnalyticOnNhd ℝ (fun t:ℝ=>f (t • x)) (Ioi 0):=by
    intro t ht
    exact ((smooth _ (distinct hx t ht)).comp t (contDiffAt_id.smul contDiffAt_const)).analyticAt
  obtain ⟨T,hT⟩:=eventually_atTop.mp ((above hx c).and (eventually_gt_atTop (0:ℝ)))
  let s:=max T 0 + 1
  have hs:T<s:=by dsimp [s];have:=le_max_left T 0;linarith
  have hp:0<s:=by dsimp [s];have:=le_max_right T 0;linarith
  have old : (fun t:ℝ=>f (t • x)) =ᶠ[𝓝 s] 0:=by
    filter_upwards [lt_mem_nhds hs] with t ht
    exact dead _ (distinct hx t (hT t ht.le).2) (hT t ht.le).1
  simpa using ray.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioi hp old (show (1:ℝ)∈Ioi 0 by simp)
end IssuedMaxwell.CutRay
end
