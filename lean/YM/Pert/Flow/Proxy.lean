import YM.Pert.Flow.Border
/-! Log-interpolated Wilson-kinetic proxy. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Pert.Flow
open Function Filter Topology Extraction Asymptotics
open scoped Topology
variable {G : Gauge} {C : Family G} {F : Order} (P : Strain C F) (hg : G.Simple)

def proxy (t : ℝ) : ℝ := (Real.sqrt (interpolated P t))⁻¹

lemma level_leads : Tendsto (fun t=> interpolated P t / t) atTop (𝓝 (2*b0 G)) := by
   let v:=2*b0 G
   let B := interpolated P
   refine Metric.tendsto_nhds.2 (fun ε hε=> ?_)
   obtain ⟨m,hm⟩:= ((secant_call P (show 0 < ε/2 from half_pos hε)).and (eventually_ge_atTop 0)).exists
   filter_upwards [eventually_gt_atTop (m+1),
       Metric.tendsto_nhds.1 (tendsto_id (α:=ℝ) |>.const_div_atTop (B m-v*m)) (ε/2) (half_pos hε)] with t ht h
   rw [Real.dist_eq] at h ⊢
   rw [id_eq,sub_zero] at h
   have hi:= hm.1 t (show m≤t from by linarith)
   change |B t-B m-v*(t-m)| ≤ _ at hi
   change |B t/t-v|<_
   have hx:0<t:= lt_of_le_of_lt ((hm.2.trans (by linarith))) ht
   have hf : ε/2*(t-m) ≤ ε/2*t := by nlinarith [hm.2]
   have hτ : (ε/2*t)/t=ε/2 := by field_simp
   calc
         _ ≤ |(B t-B m-v*(t-m))/t| + |(B m-v*m)/t| := (le_of_eq (congr_arg abs (show _ = (B t-B m-v*(t-m))/t+(B m-v*m)/t from by
             field_simp; ring))).trans (abs_add_le _ _)
         _ < ε/2+ε/2 := by rw [abs_div,abs_of_pos hx]; exact add_lt_add_of_le_of_lt ((div_le_div_of_nonneg_right (hi.trans hf) hx.le).trans_eq hτ) h
         _ = _:= by ring

include hg
lemma level_infinite : Tendsto (interpolated P) atTop atTop := by
    have hc:=Gauge.slopeConstant_pos hg
    let b:= 2*b0 G
    have hv : b>0 := by dsimp only [b]; rwa [b0_normalizes]
    have hp:∀ᶠ t:ℝ in atTop,b/2*t ≤ interpolated P t := by
       apply ((level_leads P).eventually (lt_mem_nhds (show b/2<b from half_lt_self hv))).and (eventually_gt_atTop (0:ℝ)) |>.mono
         fun t h => le_of_lt ((lt_div_iff₀ h.2).mp h.1)
    exact tendsto_atTop_mono' _ hp (tendsto_id.const_mul_atTop (half_pos hv))

lemma root_infinite : Tendsto (fun t=> Real.sqrt (interpolated P t)) atTop atTop := by
    refine tendsto_atTop.2 (fun a=> ((level_infinite P hg).eventually_ge_atTop (a^2)).mono (fun t ht=> ?_))
    exact (le_abs_self a).trans ((Real.sqrt_sq_eq_abs a).symm.trans_le (Real.sqrt_le_sqrt ht))

lemma proxy_positive : ∀ᶠ t:ℝ in atTop, 0 < proxy P t := by
   filter_upwards [(level_infinite P hg).eventually_gt_atTop 0] with t ht
   exact inv_pos.mpr (Real.sqrt_pos.mpr ht)

lemma proxy_zero : Tendsto (proxy P) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (root_infinite P hg)

theorem proxy_asymptotic : Tendsto (fun t=> proxy P t * Real.sqrt t) atTop (𝓝 (Real.sqrt (2*b0 G))⁻¹) := by
   have hc := Gauge.slopeConstant_pos hg; rw [←b0_normalizes] at hc
   have hh := Real.continuous_sqrt.continuousAt (x := 2*b0 G) |>.tendsto.comp (level_leads P)
   apply (hh.inv₀ (Real.sqrt_ne_zero'.2 hc)).congr'
   filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
   simp only [Function.comp_apply, proxy]
   rw [Real.sqrt_div' _ ht.le,inv_div,mul_comm,div_eq_mul_inv]

omit hg in
lemma step_levels {u : ℝ} (hu : 0 ≤ u) :
   Tendsto (fun t=> interpolated P (t+u) - interpolated P t) atTop (𝓝 (2*b0 G*u)) := Metric.tendsto_nhds.2 (fun ε hε=> by
     let η:= ε/(u+1)
     filter_upwards [secant_call P (show 0<η from div_pos hε (by linarith))] with t ht
     have h:=ht (t+u) (by linarith)
     rw [Real.dist_eq]; rw [show t+u-t=u from add_sub_cancel_left ..] at h
     exact h.trans_lt (by dsimp only [η];rw [div_mul_eq_mul_div]; exact (div_lt_iff₀ (show 0 < u+1 from by linarith)).2 (by nlinarith only [hε]))
   )

lemma level_forward {u : ℝ} (hu : 0 ≤ u) : Tendsto (fun t=> interpolated P (t+u) / interpolated P t) atTop (𝓝 1) := by
   let B:=interpolated P; have hb:=level_infinite P hg
   have hc := (step_levels P hu).mul (tendsto_inv_atTop_zero.comp hb)
   rw [mul_zero] at hc
   have ht := (tendsto_const_nhds (x:=1)).add hc
   rw [add_zero] at ht
   apply ht.congr' ((hb.eventually_gt_atTop 0).mono fun t hx=> by
      change 1+(_-B t)*(B t)⁻¹ = _
      change 0 < B t at hx
      change 1+(B (t+u)-B t)*(B t)⁻¹ = B (t+u)/B t
      field_simp
      ring)

theorem proxy_running {u:ℝ} (hu:0<u) :
    Tendsto (fun t=> (proxy P (t+u)-proxy P t)/(proxy P t)^3) atTop (𝓝 (-(b0 G)*u)) := by
   let B:=interpolated P
   have hq := level_forward P hg hu.le
   have hd := hq.add ((Real.continuous_sqrt.continuousAt).tendsto.comp hq)
   rw [Real.sqrt_one,show (1:ℝ)+1=2 from by norm_num] at hd
   have hv := (step_levels P hu.le).neg.div hd two_ne_zero
   rw [show -(2*b0 G*u)/2 = -b0 G*u from by ring] at hv
   apply hv.congr' ((eventually_atTop.2 <| (eventually_atTop.mp ((level_infinite P hg).eventually_gt_atTop 0)).imp (fun k hk t ht=> by
      let a:= B (t+u); let b:=B t
      have hx:0<b:= hk _ ht
      have hy:0<a:= hk _ (ht.trans (by linarith))
      let q:=Real.sqrt a; let p:=Real.sqrt b
      have hpP : p>0:= Real.sqrt_pos.2 hx
      have hqP : q>0:= Real.sqrt_pos.2 hy
      have hp0:= Real.sq_sqrt hx.le; have hq0:=Real.sq_sqrt hy.le
      have hpq: a/b+q/p>0:=by dsimp only [q,p]; positivity
      change -(a-b)/(a/b+Real.sqrt _)=(q⁻¹-p⁻¹)/(p⁻¹)^3
      rw [Real.sqrt_div (x:=a) (y:=b) hy.le]
      change -(a-b)/(a/b+q/p)=(q⁻¹-p⁻¹)/(p⁻¹)^3
      field_simp
      rw [←hq0,←hp0]
      dsimp only [p,q]; ring)))
end YM.Pert.Flow
