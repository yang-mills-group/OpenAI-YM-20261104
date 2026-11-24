import YM.XSpace.Satin
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Symbol amplitude prices on the period and infinite mesh

Prove order-zero gauge-motion **potential** not just curl bound. Uses the improved Δ
σ-small estimate using sinc and exact parity; avoids estimating asymptotic integrals
for an inverse order −1 *remainder*. Integrable origin bounds also needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Sail
open Filter Set Metric Function Lattice Bloch Laurent Complex MeasureTheory Further.FreeCovariance.KP
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {Z:Type*}
lemma sinc_diff : ContDiff ℝ ∞ Real.sinc:= by
  apply contDiff_iff_contDiffAt.mpr; intro x; by_cases he:x=0
  · rw [he,Real.sinc_eq_dslope]; obtain ⟨p,hp⟩:= (Real.analyticAt_sin (x:=0)); exact (show AnalyticAt ℝ _ _ from ⟨_,hp.has_fpower_series_dslope_fslope⟩).contDiffAt.of_le le_top
  have ht : Real.sinc =ᶠ[𝓝 x] (fun y=> Real.sin y/y):= (eventually_ne_nhds he).mono fun y hy=> Real.sinc_of_ne_zero hy
  exact (Real.contDiff_sin.contDiffAt.div (f:=Real.sin) (g:=id) contDiffAt_id he).congr_of_eventuallyEq ht
lemma sinc_bound : ∃ b:ℝ, 0<b∧∀ r:ℝ, |r|≤earth/2→ b ≤ Real.sinc r:=by
  let S:= closedBall (0:ℝ) (earth/2)
  obtain ⟨r,hr,h⟩:= (isCompact_closedBall ..).exists_isMinOn (show S.Nonempty from ⟨0,mem_closedBall_self (by positivity [earth_pos])⟩) Real.continuous_sinc.continuousOn
  refine ⟨Real.sinc r,?_,fun r' hr'=>h (mem_closedBall_zero_iff.mpr hr')⟩
  have he : |r| ≤ 3*Real.pi/2/2:= mem_closedBall_zero_iff.mp hr
  have hf (x:ℝ) (hx: 0<x) (hy: x < Real.pi):0<Real.sinc x:=by rw [Real.sinc_of_ne_zero hx.ne']; exact div_pos (Real.sin_pos_of_pos_of_lt_pi hx hy) hx
  have hp:= Real.pi_pos; rcases lt_trichotomy r 0 with hx|hx|hx
  · rw [← Real.sinc_neg r]; apply hf _ (neg_pos.mpr hx); linarith [abs_neg r,(abs_le.mp he).1]
  · simp [hx]
  apply hf r hx; linarith [(abs_le.mp he).2]

def tile (i:Axis)(p:E4) := Real.sinc (p i/2)
def spinner (p:E4):ℝ:= ∑ i,‖tooth p i‖^2
def lamp (p:E4):ℂ := spinner p
lemma tooth_price (p:E4)(i: Axis): ‖tooth p i‖^2=(p i)^2* (tile i p)^2 := by
  rw [q_exact,song,london_at,basis_inner,norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,sq_abs]
  unfold tile; by_cases h:p i=0; simp [h]; rw [Real.sinc_of_ne_zero (div_ne_zero h (two_ne_zero))]; field_simp
lemma spine_eq (p:E4): ((∑ i,(p i)^2:ℝ):ℂ)=spine p:=by unfold spine; rw [PiLp.norm_sq_eq_of_L2]; simp
lemma lamp_charge (p:E4): lamp p=∑ i:Axis,tooth p i*star (tooth p i):=by
  unfold lamp spinner; rw [Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro i _; rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
@[simp] lemma lamp_zero : lamp 0=0:=by simp [lamp_charge,q_exact,song]
lemma lower_price : ∃ b:ℝ,0<b∧∀ p:E4,p∈search→ b*‖p‖^2 ≤ spinner p:=by
  obtain ⟨b,hb,h⟩:= sinc_bound
  refine ⟨b^2,by positivity, fun p hp=>?_⟩
  unfold spinner; rw [PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
  refine Finset.sum_le_sum fun i _=>?_; rw [tooth_price,Real.norm_eq_abs,sq_abs,mul_comm (b^2)]; gcongr
  apply h; rw [abs_div,abs_of_pos (a:=(2:ℝ)) two_pos]; gcongr; exact (hp.1 i).le
lemma light (p:E4)(hp:p∈search): spinner p>0:=by obtain ⟨b,hb,H⟩:=lower_price; exact lt_of_lt_of_le (by positivity [norm_pos_iff.mpr (search.out hp)]) (H p hp)

abbrev Tw (f:E4→ℂ)(W: Further.FreeCovariance.KP.Window)(k:ℤ):= Weight (ι:=Unit) W k (fun _=> f)
lemma lamp_paid : Tw lamp search 2:= by
  simp_rw [Tw,show lamp = fun p=> ∑ i:Axis,tooth p i*star (tooth p i) from funext lamp_charge]
  exact Weight.sum_finite Finset.univ _ (fun i _=> (tooth_go (ι:=Unit) i).1.times (tooth_go i).1.conjugated)

lemma inverse : Tw (fun p=> (lamp p)⁻¹) search (-2):=by
  let j:= fun (p:E4)=> lamp p*(spine p)⁻¹; obtain ⟨b,hb,h⟩:= lower_price
  have ht : Tw j search 0:= lamp_paid.times ((reciprocal_high (ι:=Unit)).use rake_subset)
  have hf (p:E4)(hp:p∈search): b≤‖j p‖:=by unfold j lamp spine; rw [norm_mul,norm_inv,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (light p hp).le,Real.norm_of_nonneg (sq_nonneg _), ← div_eq_mul_inv,le_div_iff₀ (pow_pos (norm_pos_iff.mpr (search.out hp)) _)]; exact h p hp
  apply ( (ht.reverse b hb (fun _=> hf)).times ((reciprocal_high (ι:=Unit)).use rake_subset)).stay; intro _ p hp; unfold j; have he : spine p ≠0 := spine_pos (search.out hp); simp only [mul_inv_rev,inv_inv]; rw [mul_right_comm, mul_inv_cancel₀ he,one_mul]

private lemma even_d {f:E4→ℂ} (h:ContDiff ℝ ∞ f) (hf: ∀ᶠ p in 𝓝 0,f (-p)=f p): fderiv ℝ f 0=0:= by
  have ht := (h.differentiable (by simp) 0).hasFDerivAt
  let L:=fderiv ℝ f 0
  have hh : HasFDerivAt (fun z=> f (-z)) (-L) 0:=by
    let Y:= (- (ContinuousLinearMap.id ℝ E4)); have hz:Y 0=0:=map_zero _
    convert! (show HasFDerivAt f L (Y 0) from hz.symm ▸ ht).comp 0 Y.hasFDerivAt using 1; unfold Y; simp
  apply ContinuousLinearMap.ext; intro u; change L u=0; have he : L = -L:=ht.unique (hh.congr_of_eventuallyEq (hf.mono fun _ hx=>hx.symm)); have hb : (2:ℝ) • L u=0:=by rw [two_smul]; nth_rw 1 [he]; rw [neg_apply,neg_add_cancel]
  exact (smul_eq_zero.mp hb).resolve_left (by norm_num)

lemma lamp_minus : Tw (fun p=>lamp p-spine p) search 4:=by
  have h (i:Axis): Tw (fun p=> ((tile i p:ℂ))^2-1) search 2:=by
    let L (p:E4):= (tile i p:ℂ)^2-1
    have hu : ContDiff ℝ ∞ L:=by
      have ht : ContDiff ℝ ∞ (tile i):= sinc_diff.comp (f:=fun p:E4=>p i/2) (by fun_prop)
      exact ((Complex.ofRealCLM.contDiff.comp ht).pow 2).sub contDiff_const
    refine (Plain.sample L hu).two_powers (by positivity [earth_pos]) search_short (fun _=>by simp [L,tile]) (fun _=> even_d hu (Eventually.of_forall fun p=> by simp [L,tile,neg_div]))
  let L (i:Axis)(p:E4):= ((p i:ℝ):ℂ); have hh (i): Tw (L i) search 1:=by refine (Plain.sample (L i) (Complex.ofRealCLM.contDiff.comp (f:=fun p:E4=>p i) (by fun_prop))).one_power (by positivity [earth_pos]) search_short ?_; intro _; simp [L]
  have he p: lamp p-spine p=∑ i:Axis,L i p*L i p*((tile i p:ℂ)^2-1):=by unfold lamp spinner; rw [← spine_eq,Complex.ofReal_sum,Complex.ofReal_sum, ← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [tooth_price]; unfold L; push_cast; ring
  simp_rw [he]; exact Weight.sum_finite Finset.univ _ (fun i _=> ((hh i).times (hh i)).times (h i))
lemma diff_inverse : Tw (fun p=> (lamp p)⁻¹-(spine p)⁻¹) search 0:=by
  refine ((lamp_minus.times inverse|>.times ((reciprocal_high (ι:=Unit)).use rake_subset)).opposite).stay ?_
  intro _ p hp; have he:spine p≠0:= spine_pos (search.out hp); have hl: lamp p≠0:= Complex.ofReal_ne_zero.mpr (light p hp).ne'; field_simp; ring
private lemma house_c : ∀ᶠ x in 𝓝 0, house x=1:=by
  have h(i:Axis):∀ᶠ x:E4 in 𝓝 0, beam (x i)=1:=by
    have ht:= Real.pi_pos
    have hp : Continuous fun x:E4=>x i:=by fun_prop
    filter_upwards [(hp.tendsto 0).eventually (lt_mem_nhds (show -3*Real.pi/4 < (0:E4) i from by change _<(0:ℝ); linarith)),
      (hp.tendsto 0).eventually (gt_mem_nhds (show (0:E4) i < 3*Real.pi/4 from by change (0:ℝ)<_; linarith))] with x hx hu
    unfold beam; rw [at_corner _ hx.le,at_line _ (by unfold mural; linarith),sub_zero]
  filter_upwards [eventually_all.mpr h] with x hx; simp [house,hx]
lemma diff_cut : Tw (fun p=> house p-breeze 1 p) search 2:=by
  have he := house_smooth.sub (breeze_smooth 1); refine (Plain.sample _ he).two_powers (by positivity [earth_pos]) search_short (fun _=>by simp [house_core,breeze,polar]) fun _=> ?_
  apply even_d he; filter_upwards [house_c, (continuous_neg.tendsto 0).eventually (show ∀ᶠ x in 𝓝 (-0), house x=1 by rw [neg_zero]; exact house_c)] with x hx hp; simp [hp,hx,breeze,polar]
end YM.XSpace.Sail
