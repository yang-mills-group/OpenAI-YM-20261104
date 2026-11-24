import YM.RegulatorIR.Laplace.Store

/-! Uniform localization on group collars via `isolated`. No regularity at the
kernel branch discontinuity requested. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Laplace.Bundle
open Lattice PertExtension Series Series.Radial MeasureTheory Filter Function Set Metric Geometry
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical
variable {G:Gauge} {E I:Type}[Fintype E][Fintype I] {F A:Hook G E I} (H:Bundle F A)
variable {r R:ℝ}
include H
lemma gaps (_hR:0≤R){C : Set (RoomK G E)}(hc:IsClosed C)(he:1∉C): ∃ c>0,∃ d>0,∀ t∈Ioo (0:ℝ) d,∀ x:Meadow G I,‖x‖≤R→∀ v∈C,c≤F t (Chart.expLinks G I (t • x)) v:= by
 -- sequence k with low costs at arbitrarily small t
 by_contra! Hv
 let y (i:ℕ):ℝ:= (1+i:ℝ)⁻¹
 have hp (i:ℕ):0<y i:=by dsimp only [y]; positivity
 choose t ht z hz f hf Hu using fun i=>Hv (y i) (hp i) (y i) (hp i)
 obtain ⟨w,hw,v,hv,hm⟩:= hc.isCompact.tendsto_subseq hf
 have hy:Tendsto y atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_left _ 1 tendsto_natCast_atTop_atTop)
 have h₁:Tendsto t atTop (𝓝 0):=squeeze_zero (fun i=>(ht i).1.le) (fun i=>(ht i).2.le) hy
 let g(i:ℕ):= Chart.expLinks G I (t i • z i)
 have h₂: Tendsto g atTop (𝓝 1):= by
    have h: Tendsto (fun i=> t i • z i) atTop (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero.mpr (by
      apply squeeze_zero (g:=fun i=>t i*R) (fun _=>norm_nonneg _) (fun i=>by rw [norm_smul_of_nonneg (ht i).1.le];exact mul_le_mul_of_nonneg_left (hz i) (ht i).1.le)
      convert h₁.mul_const R using 1; simp)
    exact expOrigin (G:=G) I ▸ (((expMeadow I).tendsto 0).comp h)
 have h₃: Tendsto (fun i=>F (t i) (g i) (f i)) atTop (𝓝 0):= squeeze_zero (fun i=>H.nonneg ..) (fun i=>(Hu i).le) hy
 apply he; rw [← H.isolated _ _ _ w (h₁.comp hv.tendsto_atTop) (h₂.comp hv.tendsto_atTop) hm (h₃.comp hv.tendsto_atTop)]
 exact hw

private lemma budget : ∃ a:ℝ, 0 ≤ a ∧ ∀ t∈ Icc (0:ℝ) 1,∀ x y,‖A t x y‖≤a:=by
 let S : Set (ℝ × RoomK G I ×RoomK G E):= Icc 0 1 ×ˢ (univ ×ˢ univ)
 obtain ⟨c,hc⟩:= ((show IsCompact S from isCompact_Icc.prod (isCompact_univ.prod isCompact_univ))).exists_bound_of_continuousOn H.cased.continuousOn
 exact ⟨|c|,abs_nonneg _,fun t ht x y=> (hc (t,x,y) ⟨ht,mem_univ x,mem_univ y⟩).trans (le_abs_self _)⟩

lemma out (N:ℕ) (hR:0 ≤ R) (hr:r < Chart.small G (Orb.tray G))(hx:0<r): ∃ C:ℝ,0≤C ∧ ∀ᶠ t in 𝓝[>] (0:ℝ),∀ y:Meadow G I, ‖y‖ ≤ R → let u:=Chart.expLinks G I (t • y); ‖(t^dim G E)⁻¹ * (∫ x in (Chart.chamber G E r)ᶜ, tilt F A t u x ∂Chart.physical G E)‖ ≤ C*t^N:= by
 let S:= Chart.chamber G E r; let μ:= Chart.physical G E
 have hS:IsOpen S:= Chart.Ratio.chamber_open (Orb.traySpec G) hr.le
 have hz : (1:RoomK G E) ∈ S := fun i _=>⟨0,mem_ball_self hx,G.mat_lieExp_zero⟩
 obtain ⟨c,hc,d,hd,hD⟩:= gaps H hR hS.isClosed_compl (notMem_compl_iff.mpr hz)
 obtain ⟨a,ha,ha'⟩:= H.budget
 let n:=dim G E; obtain ⟨C,hC,Hc⟩:= bounded_exp hc (n+N)
 refine ⟨a*C,mul_nonneg ha hC,?_⟩
 filter_upwards [Tested.eventually_small (lt_min hd zero_lt_one)] with t ht
 have hg:t<1:= ht.2.trans_le (min_le_right ..); have ht':0<t:= ht.1
 intro y hy V
 let K:= a*Real.exp (-c/t^2); let P:= tilt F A t V
 have h : ‖∫ z in Sᶜ,P z ∂μ‖ ≤ K := by
    have hi : Integrable (fun _:RoomK G E=>K) (Chart.physical G E):= integrable_const _
    refine (norm_integral_le_of_norm_le hi.integrableOn ?_).trans ((setIntegral_le_integral hi (Eventually.of_forall fun _=>mul_nonneg ha (Real.exp_pos _).le)).trans_eq ?_)
    · filter_upwards [ae_restrict_mem hS.measurableSet.compl] with x hh
      unfold P tilt; rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]; apply mul_le_mul (ha' _ ⟨ht'.le,hg.le⟩ _ _) (Real.exp_le_exp.mpr (by grw [show c ≤ F t V x from hD t ⟨ht', ht.2.trans_le (min_le_left ..)⟩ y hy x hh])) (Real.exp_pos _).le ha
    simp
 change ‖(t^n)⁻¹*_‖ ≤ _
 rw [norm_mul,Real.norm_of_nonneg (by positivity : 0≤(t^n)⁻¹)]
 apply le_trans (mul_le_mul_of_nonneg_left h (by positivity : 0≤(t^n)⁻¹))
 apply le_of_mul_le_mul_right (a:=(t⁻¹)^N) _ (by positivity)
 have hv : 0<t⁻¹:= inv_pos.mpr ht'
 calc
  _ = a*( (t⁻¹)^(n+N)*Real.exp (-c*(t⁻¹)^2)):=by rw [pow_add, mul_right_comm _ _ (_^N)];unfold K; simp only [inv_pow, ← div_eq_mul_inv]; ring
  _ ≤ a*C:= mul_le_mul_of_nonneg_left (le_trans ?_ (Hc (t⁻¹) hv.le)) ha
  _ ≤ _ := by apply le_of_eq; rw [mul_assoc (a*C),← mul_pow,mul_inv_cancel₀ ht'.ne',one_pow,mul_one]
 -- remaining
 gcongr; linarith

lemma beats : Rated G I (normalized F A) (tomorrow F A) :=by
 intro D hd n
 obtain ⟨r,hr,Hh⟩:= H.entry.range_cap (Chart.tangent G E) H.m_K (m_F F H.burden) (show 0 ≤ max 1 D from hd.trans (le_max_right ..)) n
 let d := min (r/2) (Chart.small G (Orb.tray G)/2)
 have hx := Chart.Ratio.small_pos (Orb.traySpec G)
 have ht: 0<d:=by unfold d;exact lt_min (half_pos hr) (half_pos hx)
 have he:d< Chart.small G (Orb.tray G):=lt_of_le_of_lt (min_le_right ..) (half_lt_self hx)
 obtain ⟨C,hc,Hc⟩:= Hh d ⟨ht,lt_of_le_of_lt (min_le_left ..) (half_lt_self hr)⟩
 obtain ⟨b,hb,Hb⟩:= H.out (n+1) hd he ht
 refine ⟨C+b,add_nonneg hc hb,?_⟩
 filter_upwards [Tested.eventually_pos,Hc,Hb] with t hr hv hg
 intro x hy
 have hβ: ‖((1:ℝ),x)‖ ≤ max 1 D:= by rw [Prod.norm_def];exact max_le_max (by norm_num) hy
 have hx := hv ((1:ℝ), x) hβ
 let T:= Chart.chamber G E d; let k:= dim G E; let u:= Chart.expLinks G I (t • x)
 let v:= (t^k)⁻¹ * (∫ y in Tᶜ, tilt F A t u y ∂Chart.physical G E)
 let g:= Tested.peval (tomorrow F A x) n t;let p:= segment (Chart.tangent G E) (aura A) (priceMap F) t d (1,x)
 unfold normalized scan; rw [← integral_add_compl (s:=T) (Chart.Ratio.chamber_open (Orb.traySpec G) he.le |>.measurableSet) (H.reading t u),mul_add]
 rw [show _ * (∫ y in T, _∂Chart.physical G E)=p from H.transforms t hr x ht he]
 change ‖p + v -g‖ ≤ (C+b)*_
 rw [show p+v-g= p-g+v by abel];exact (norm_add_le ..).trans ((add_le_add hx (hg x hy)).trans_eq (add_mul ..).symm)
end YM.RegulatorIR.Laplace.Bundle
