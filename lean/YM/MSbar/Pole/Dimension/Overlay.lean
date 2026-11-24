import YM.MSbar.Pole.Dimension.Round
import YM.MSbar.Pole.Analysis.Rapid
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! Padding independence of the dimensional integral. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Radial
open Function Set Filter MeasureTheory
open scoped Topology ContDiff Classical BigOperators Real
variable {H : ℝ × ℂ → ℂ}
local notation "T" => Ioi (0:ℝ)
local notation "ω" => volume.restrict T
variable (p : fullPlane H) (h : Globular H)
include p
lemma up_plane (h : Globular H) : fullPlane (higher H) := smooth isOpen_univ
    (show ContinuousOn (1:Price ℂ).val _ from continuousOn_const) p h.even
private lemma lane (s : ℝ) : Integrable (fun r : ℝ => H (s,(r:ℂ)) * (r:ℂ)) ω := by
  let L : ℝ →L[ℝ] ℝ × ℂ:= (ContinuousLinearMap.inr ℝ ℝ ℂ).comp Complex.ofRealCLM
  let P (i : ℝ) := H (s,(i:ℂ)); let q := Moment (ticket (@id ℂ)); let J := ticket (@id ℝ)
  let U := ((1 : Price ℂ).back (@Prod.snd ℝ ℂ)); let b : ℝ × ℂ:= (s,0)
  have hb (x:ℝ):b+L x=(s,(x:ℂ)):=by simp [b,L]
  have he := comp_affine_bill L b p --args
    (show MapsTo (fun x=> b+L x) T (univ ×ˢ univ) from fun _ _ => ⟨mem_univ _,mem_univ _⟩)
    (show Bills T 1 1 (fun x=> U (b+L x)) from Bills.const _) (q:=J) (bill_byprice (s:=J) (fun x hx=>?_))
  · -- use jBarrel? simpler integrable via power bill rapid
    have hk : Packet T 1 J P:= he.congr (fun _ _=> Eventually.of_forall fun x=>(congr_arg H (hb x)).symm)
    apply rapid_pay (hp:=?_) _ measurableSet_Ioi
    · have hB : Bills T (1*J) 1 (fun x=> ‖(x:ℂ)‖):= bill_single (l:=1) zero_le_one (fun x hx=>by simp [J])
      exact (hk.values.norm.spend hB).dominates fun x hx=>by change ‖P x*(x:ℂ)‖ ≤ ‖‖P x‖ * ‖(x:ℂ)‖‖; simp
    · have hy : ContDiffOn ℝ ∞ (fun x=>P x*(x:ℂ)) T := fun x hx=> ((hk.smooth _ hx).mul Complex.ofRealCLM.contDiff.contDiffAt).contDiffWithinAt
      exact hy.continuousOn.aestronglyMeasurable measurableSet_Ioi
  rw [Price.back_apply,hb,moment_apply]
  change 1+|x|≤_
  simp only [ticket_apply,id_eq,Complex.norm_real,Real.norm_eq_abs]
  exact le_mul_of_one_le_left (by positivity) (by simp)
include h
lemma across (s : ℝ) : (∫ x : ℂ,higher H (s,x))=(π:ℂ) * H (s,0) := by
  let K (x:ℂ) := higher H (s,x); let V (r:ℝ) := H (s,(r:ℂ)); let P(r:ℝ):=r • K (r:ℂ)
  have hG := round_higher p h
  have hm: Integrable P ω:= by
    have hh := lane (up_plane p h) s; simp_rw [mul_comm] at hh; simpa only [P,K,Complex.real_smul] using! hh
  have ht t (hp : 0<t) : HasDerivAt V ((-2:ℝ) • P t) t := by
    have hx := nose p h s t hp
    convert hx using 1
    unfold P K; simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_ofNat]; rw [mul_assoc]
  have ha : Tendsto V atTop (𝓝 0) := by
    let r (t:ℝ) := Radius s (t:ℂ)
    have he' : Tendsto r atTop atTop := tendsto_atTop_mono (f:=id) (fun t=> ?_) tendsto_id
    · -- V -> through vanishes
      have hh := (vanishesAtTop p (mem_univ (0:ℂ)) 0).comp he'
      simp only [Function.comp_def,Complex.cpow_zero,mul_one] at hh
      exact hh.congr (fun t=> (h.radius s _).symm)
    have hj := Radius_sq s (t:ℂ)
    simp at hj; change t≤_
    nlinarith [Radius_nonneg s (t:ℂ)]
  have hc := p.smooth (s,0) ⟨mem_univ _,mem_univ _⟩ |>.continuousAt
  have hh : ContinuousAt V 0 := by
    let f (t:ℝ): ℝ × ℂ:= (s,(t:ℂ)); have he : f 0=(s,0):=by simp [f]
    exact ContinuousAt.comp (f:=f) (he ▸ hc) (show Continuous f from by unfold f; fun_prop).continuousAt
  have hFP : (-2:ℝ) • (∫ r,P r ∂ω)= -H (s,0) := by
    have hx := integral_Ioi_of_hasDerivAt_of_tendsto hh.continuousWithinAt ht (hm.smul (-2:ℝ)) ha
    rw [← integral_smul]; simpa only [V,Complex.ofReal_zero,zero_sub] using hx
  let Q:=Ioo (-π) π; let R := Complex.polarCoord
  rw [← Complex.integral_comp_polarCoord_symm]
  change (∫ p in R.target, p.1 • K (R.symm p)) = _
  have hr : R.target = T ×ˢ Q := Complex.polarCoord_target
  have hl : (∫ p in R.target, p.1 • K (R.symm p))=(∫ p : ℝ × ℝ in R.target, P p.1) := setIntegral_congr_fun R.open_target.measurableSet
    fun a ha => congr_arg (a.1 • ·) (hG _ _ _ _ (by rw [Complex.norm_polarCoord_symm]; simp))
  rw [hl,hr, MeasureTheory.Measure.volume_eq_prod,setIntegral_prod]
  · simp only [setIntegral_const]; rw [integral_smul]; unfold Q; rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]; rw [Complex.real_smul,sub_neg_eq_add, ← two_mul]; simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
    rw [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_ofNat] at hFP; linear_combination -(π:ℂ)*hFP
  letI : IsFiniteMeasure ((volume:Measure ℝ).restrict Q) := inferInstanceAs (IsFiniteMeasure ((volume:Measure ℝ).restrict (Ioo _ _)))
  have he:= hm.comp_fst ((volume:Measure ℝ).restrict Q)
  rw [Measure.prod_restrict] at he
  exact he
end YM.MSbar.Pole.Radial
