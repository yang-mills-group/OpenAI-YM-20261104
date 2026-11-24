import YM.RG02.Flat.Ion

/-!
# The per-bond Markov noise normalizer

Keep that scalar AS WELL AS the field-dependent denominator. Here is its
perturbative interpretation with positive leading cost, same Haar chart.
Exact cancellations of the actual factors in a normalized pointwise
comparison at physical β need no bounds, but if reading an unnormalized
(free energy/constant) term this parameter cost must be kept. Gap estimates
pointwise; no claim of volume, lattice schedule or horizon uniformity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Friction
open Filter Function MeasureTheory Set Metric Matrix Lattice Wilson RG Precision Bid
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Therm Asym
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{c f : Side}(S : StepData c f)

abbrev E (G : Gauge) := Unit → G.Color
abbrev W (G : Gauge) := Unit → G.El
abbrev cardinal (G : Gauge) := Module.finrank ℝ (E G)
noncomputable abbrev rate (G : Gauge) := Chart.tangent G Unit
noncomputable abbrev roll (G : Gauge) := Chart.physical G Unit

def life (t : ℝ) (u : W G) := S.penaltyWeight (t^2)⁻¹ (u ())
lemma line (t : ℝ) : Continuous (life (G:=G) S t) := (S.penaltyWeight_cont _).comp (continuous_apply ..)

lemma listing (G : Gauge)(t : ℝ) : S.penaltyZ (t^2)⁻¹ G=∫ u:W G,life S t u∂roll G := by
    let F (_ : Unit) := S.penaltyWeight (G:=G) (t^2)⁻¹
    have hm : life S t=fun u:W G=>∏ i:Unit,F i (u i) := by funext u; simp; rfl
    rw [hm]; change _= ∫ x:W G,(∏ i:Unit,F i (x i)) ∂ Measure.pi (fun _=>G.probHaar)
    rw [integral_fintype_prod_eq_prod F]; simp; rfl

def jetBase (u:E G):= S.kernel.penalty* G.price (G.lieExp (u ()))
def hinge (u:ℝ×E G):= jetBase S u.2
def form (u v:E G) := S.kernel.penalty* inner ℝ (u ()) (v ())

theorem smooth : ContDiffAt ℝ ω (hinge (G:=G) S) 0 := by
   refine contDiffAt_const.mul ?_
   apply Work.F03.price_smooth (A:= fun x : ℝ × E G => G.lieExp (x.2 ()))
   exact G.exp_jet.contDiffAt.comp (f:=fun x : ℝ×E G=>x.2 ()) 0 ((contDiffAt_apply ℝ G.Color () _).comp (f:=Prod.snd) 0 contDiffAt_snd)

private theorem cost : hinge S (0 : ℝ× E G) = 0 ∧ fderiv ℝ (hinge S) (0:ℝ×E G)=0 ∧ ∀ u v : ℝ×E G, Work.F05.bend (hinge (G:=G) S) 0 u v=form S u.2 v.2 := by
   have hm := Work.F03.hessian_of_limit (Q:=fun i j => form S i.2 j.2) (f:=hinge (G:=G) S) ((smooth S).of_le le_top) ?_ ?_ ?_
   · obtain ⟨a,b,h⟩ := hm; refine ⟨a,b,fun x y=>?_⟩; rw [Work.F05.bend_apply]; exact h x y
   · intro x
     have hv : HasDerivAt (fun t:ℝ=> G.mat (G.lieExp (t • x.2 ()))) (G.colorMat (x.2 ())) 0 := by
        have he := G.expDiff_zero
        have hp : HasDerivAt (fun t:ℝ=> t • x.2 ()) (x.2 ()) 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const (x.2 ())
        exact (show HasFDerivAt (fun u:G.Color=>G.mat (G.lieExp u)) G.colorMat.toContinuousLinearMap ((0:ℝ) • x.2 ()) by rw [zero_smul]; exact he).comp_hasDerivAt 0 hp
     have h := (Work.F03.price_limit (G:=G) (V:=fun t : ℝ => G.lieExp (t • x.2 ())) (by simp) hv).const_mul S.kernel.penalty
     simpa only [hinge,jetBase,Prod.smul_snd, Pi.smul_apply, form,real_inner_self_eq_norm_sq,mul_div_assoc] using h
   · intro u v w; unfold form; simp [inner_add_left, mul_add]
   intro u v; unfold form; rw [real_inner_comm]

def Γ (G : Gauge) : GaussianScore.Law (E G) := by
    let P:=Work.F05.bend (hinge S (G:=G)) 0
    let L:= LinearMap.inr ℝ ℝ (E G)
    let H:= P.compl₁₂ L L
    have he x y : H x y=form S x y := (cost S).2.2 ((0:ℝ),x) ((0:ℝ),y)
    refine ⟨H,?_,?_,?_⟩
    · intro x y; simp only [he]; unfold form; rw [real_inner_comm]
    · refine ⟨S.kernel.penalty/2, half_pos S.kernel.penalty_pos,fun x=>?_⟩
      have hp : ‖x‖=‖x ()‖:= le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i=> by cases i; rfl)) (norm_le_pi_norm x ())
      rw [hp, he,form,real_inner_self_eq_norm_sq]; exact le_of_eq (by ring)
    simp_rw [he]; unfold form; fun_prop

lemma Γ_apply (x y:E G): (Γ S G).P x y=form S x y := (cost S).2.2 ((0:ℝ),x) ((0:ℝ),y)
lemma direction (G : Gauge) : Steer (Γ S G) (hinge S) 0 0 := by
    obtain ⟨hx,hp,hh⟩ := cost S (G:=G)
    refine ⟨⟨(smooth S).of_le le_top,hx,fun u=>?_⟩,fun i v=>?_⟩
    · unfold Radial.jet; rw [iteratedFDeriv_one_apply,hp]; simp
    simp only [mul_zero,smul_zero,sub_zero,zero_add,Γ_apply];
    unfold jet; rw [← show ![(i,v),(i,v)] = fun _=>(i,v) from funext fun j=>by fin_cases j <;> rfl,← Work.F05.bend_apply,hh]
    norm_num; ring

variable (P : ChartRatio G)(H : LocalRatio P)
include H

-- Haar entry includes P.scale.
def jac (P : ChartRatio G) (x : ℝ × E G) := Complex.ofReal (jacobian P x.2)
lemma costs : ContDiffAt ℝ ∞ (jac P) 0 := by
  refine Complex.ofRealCLM.contDiff.contDiffAt.comp (f:=fun x:ℝ× E G=>jacobian P x.2) 0 ?_
  exact ((Chart.Ratio.jacobian_smooth (U:=Unit) H).of_le le_top).comp (f:=Prod.snd) (0:ℝ× E G) contDiffAt_snd
private lemma inner {t : ℝ}(ht : 0<t){r : ℝ} (h : 0<r)(hr : r< Chart.small G P) :
    ((t:ℂ)^cardinal G)⁻¹*Complex.ofReal (∫ x in chamber G Unit r, life S t x ∂roll G)=
       ∫ u in disc t r, Therm.sheet (hinge S) (jac P) t u ∂ rate G := by
   let f' (u:E G):= Chart.jacobian P u*life S t (Chart.expLinks G Unit u)
   rw [Chart.Ratio.chamber_integral H (life S t) (line S t|>.measurable) hr h]
   change ((t:ℂ)^_)⁻¹ * ↑(∫ x in Metric.ball 0 r,f' x∂rate G) = _
   let A := Metric.ball (0:E G) r
   let B := disc (E:=E G) t r
   have he (u:E G) : Therm.sheet (hinge S) (jac P) t u = Complex.ofReal (f' (t • u)) := by
      unfold f' Therm.sheet Therm.turbine hinge life StepData.penaltyWeight jac jetBase; dsimp only [Chart.expLinks]
      push_cast; congr 3
      field_simp
   simp_rw [he]; symm; refine (integral_ofReal (𝕜:=ℂ) (μ:=(rate G).restrict (disc t r)) (f:=fun x=>f' (t • x))).trans ?_; symm
   have hg:= Measure.integral_comp_smul_of_nonneg (rate G) (A.indicator f') t (hR:=ht.le)
   have hh x : A.indicator f' (t • x)=B.indicator (fun u:E G=> f' (t • u)) x:= by
      by_cases hv : x∈ B
      · rw [indicator_of_mem (s:=A) (show t•x∈A from hv), indicator_of_mem hv]
      rw [indicator_of_notMem (s:=A) (show t•x∉A from hv), indicator_of_notMem hv]
   simp_rw [hh] at hg; rw [integral_indicator (s:=A) isOpen_ball.measurableSet,integral_indicator (s:=B) (disc_meas ..)] at hg
   change _=Complex.ofReal (∫ u in B,f' (t • u) ∂rate G)
   rw [hg,smul_eq_mul]; push_cast; rfl

-- scalar gap away from chart pays only at this order/point
private lemma pit {r : ℝ}(h : 0<r)(hr : r<Chart.small G P) : ∃ c>0,∀ x:W G,x∉chamber G Unit r →
       c≤ S.kernel.penalty*G.price (x ()) := by
   let D := (chamber G Unit r)ᶜ
   by_cases hD : D.Nonempty; swap; · exact ⟨1,one_pos,fun x hv=>(hD ⟨x,hv⟩).elim⟩
   obtain ⟨x,hx,hV⟩ := (Chart.Ratio.chamber_open H hr.le |>.isClosed_compl.isCompact).exists_isMinOn (f:=fun x:W G=> S.kernel.penalty*G.price (x ())) hD (by fun_prop)
   refine ⟨_,mul_pos S.kernel.penalty_pos (lt_of_le_of_ne (G.price_range (x ())).1 (fun HV=>hx ?_)),hV⟩
   have he := G.chord_price (x ()); rw [← HV] at he
   have ht : ‖G.mat (x ())-1‖=0 := by unfold Gauge.chord at he; have hρ : 0<Real.sqrt G.repDim := Real.sqrt_pos.2 (Nat.cast_pos.mpr G.dimPos); by_contra hm; have hq := div_ne_zero hm hρ.ne'; exact pow_ne_zero 2 hq (he.trans (mul_zero _))
   intro i hi; cases i; exact ⟨0,mem_ball_self h, G.mat_lieExp_zero.trans (G.mat_injective ((by rw [G.mat_one]; exact (sub_eq_zero.mp (norm_eq_zero.mp ht)).symm)))⟩

lemma outer {r : ℝ}(h : 0<r)(hr : r<Chart.small G P) (n : ℕ) : Bill n fun t=>
    ((t:ℂ)^cardinal G)⁻¹ * Complex.ofReal (∫ x in (chamber G Unit r)ᶜ, life S t x ∂roll G) := by
   obtain ⟨c,hc,hC⟩:= pit S P H h hr
   obtain ⟨D,hD,hf⟩:= bounded_exp hc (n+cardinal G)
   refine ⟨D,hD,?_⟩
   filter_upwards [Tested.eventually_pos] with t ht
   let A := Real.exp (-c/t^2)
   have hp : ‖∫ x in (chamber G Unit r)ᶜ, life S t x ∂roll G‖≤ A := by
      refine le_trans (norm_integral_le_of_norm_le (Integrable.integrableOn (integrable_const A)) ?_) (le_trans (setIntegral_le_integral (integrable_const A) (Eventually.of_forall fun _=> (Real.exp_pos _).le)) (le_of_eq ?_))
      · filter_upwards [ae_restrict_mem (Chart.Ratio.chamber_open H (U:=Unit) hr.le|>.measurableSet.compl)] with x hx
        unfold life StepData.penaltyWeight; rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)];
        refine Real.exp_le_exp.mpr ?_
        calc
          _ ≤ -(t^2)⁻¹*c := by rw [mul_assoc]; exact mul_le_mul_of_nonpos_left (hC x hx) (by have := inv_pos.mpr (pow_pos ht 2); linarith)
          _ = _ := by ring
      simp
   rw [norm_mul,norm_inv,norm_pow,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs t,abs_of_pos ht]
   refine (mul_le_mul_of_nonneg_left hp (by positivity)).trans ?_
   let y := t⁻¹; have hy:0<y := by unfold y; positivity
   have Hq := hf y hy.le
   rw [← inv_pow]; apply le_of_mul_le_mul_left (a:=y^n) _ (by positivity)
   rw [show y^n * (D*t^n) = D by unfold y; rw [mul_left_comm,mul_comm D,←mul_pow, inv_mul_cancel₀ ht.ne']; ring]
   unfold A; rw [show -c/t^2 = -c*y^2 by unfold y; rw [inv_pow]; ring]
   calc
      _ = y^(n+cardinal G)*Real.exp (-c*y^2) := by unfold y;rw [pow_add,mul_assoc]
      _ ≤ _ := le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy.le (by linarith) _) (by positivity)) Hq

open PowerSeries

def paidSeries := C (Complex.ofReal (Therm.leading (Γ S G) (rate G) 0))*Therm.shuttle (Γ S G) (hinge S) (jac P) 0

theorem restored : Near (fun t => ((t:ℂ)^cardinal G)⁻¹ * ↑(S.penaltyZ (t^2)⁻¹ G)) (paidSeries S P) := by
   have hh : Measurable (hinge S (G:=G)) := by unfold hinge jetBase; fun_prop
   have hm : Measurable (jac P) := Complex.continuous_ofReal.measurable.comp ((Chart.Ratio.jacobian_meas H).comp measurable_snd)
   obtain ⟨r,hr,hG⟩ := Therm.transmission (direction S G) (rate G) hh (costs P H) hm
   let a:=min r (small G P/2); have hb : 0<a := lt_min hr (half_pos (Chart.Ratio.small_pos H))
   have hE : a<small G P := (min_le_right ..).trans_lt (half_lt_self (Chart.Ratio.small_pos H))
   have ht := (hG (fun t=>disc t a) ((Therm.Collars.body hb).raise (min_le_left r _))).2
   let U:=chamber G Unit a
   have hv : Near (fun t=> ((t:ℂ)^cardinal G)⁻¹ * Complex.ofReal (∫ x in U, life S t x ∂roll G)) _ := Near.same ht (Tested.eventually_pos.mono fun t h => (inner S P H h hb hE).symm)
   intro n
   convert! bill_add (hv n) (outer S P H hb hE (n+1)) using 1
   funext t; rw [Pi.sub_apply, Pi.add_apply,listing S G t, ← MeasureTheory.integral_add_compl (μ:=roll G) (s:=U) (Chart.Ratio.chamber_open H hE.le|>.measurableSet) ((line S t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
   simp only [Complex.ofReal_add,mul_add,Pi.sub_apply]; abel

lemma paid_base : coeff 0 (paidSeries S P)=Complex.ofReal (Therm.leading (Γ S G) (rate G) 0 * P.scale) := by
    rw [paidSeries,coeff_C_mul,Therm.shuttle,coeff_mk, Wick.fixed (Γ S G) (rate G) _ (Complex.ofReal P.scale)]; push_cast; rfl
    funext x; rw [Therm.pulsed, coeff_zero_eq_constantCoeff_apply,map_mul]
    simp only [← coeff_zero_eq_constantCoeff_apply,Asym.ex,PowerSeries.coeff_mk]; simp [ribbon_coeff, Radial.jet_zero,jac,Chart.jacobian,Chart.fee,H.anchored,H.scale.le]
end YM.RG02.Friction
