/- free_ray adapts the exponential damping estimate in right_half_plane_of_bounded_on_real from Mathlib/Analysis/Complex/PhragmenLindelof.lean for this project.
Authors: Yury Kudryashov. Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache License 2.0. See NOTICE. -/

import YM.Work.C10
import YM.Work.C13
import Mathlib.Analysis.Complex.PhragmenLindelof
/-!
# Upward lines of fixed base. Spectral support → NO price from complex translations

Do not change rates with compact or word, prove price using full right-half-plane growth
of arbitrary fixed physical W functions along all shielded rays, exp ε arbitrary small
by adding plateau cutoff immediately around the absolute-coordinate frequency support
(not a tube estimate from abstract boundary temperate powers billed in scaled currencies).
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Tunnel
open Set Filter Function Analysis Distribution Boundary Boundary.Surface Probe
open scoped Topology BigOperators ContDiff InnerProductSpace Classical NNReal
variable {n : ℕ}
lemma fields_upper {x y : Points n} {r:ℝ} (hy:y∈fields n) (hx:x∈shores n) (hr:0≤r) : y+r • x∈fields n:=by
  simp only [fields,shores,Set.mem_iInter, Set.mem_setOf_eq, Mink.inside,Mink.cone] at hx hy ⊢
  intro i j hij
  change ‖spatial ((y j+r • x j) - (y i+r • x i))‖ < _
  dsimp only [PiLp.add_apply,PiLp.smul_apply]
  have h : (y j+r • x j)-(y i+r • x i)=y j-y i + r • (x j-x i):=by rw [smul_sub]; abel
  rw [h,Mink.rest_add,Mink.rest_mul,Mink.clock_add,Mink.clock_mul]; apply lt_of_le_of_lt (norm_add_le ..); rw [norm_smul,Real.norm_of_nonneg hr]; exact add_lt_add_of_lt_of_le (hy i j hij) (mul_le_mul_of_nonneg_left (hx i j hij) hr)

def ride (p:Full n) (y:Points n)(z:ℂ) : Full n := p + z • glow 0 y
@[simp] lemma ride_zero (p:Full n) (y:Points n) : ride p y 0=p:=by simp [ride]
lemma ride_shade (p:Full n)(x:Points n)(z:ℂ) : shade (ride p x z)= shade p + z.re • x := by
  apply Points.flatten.injective; ext1 i
  simp [ride, shade, glow,Complex.mul_im,mul_comm]
lemma ride_in {p:Full n}(hp:p∈tube n){x:Points n}(hx:x∈shores n){z:ℂ}(hz:0≤z.re) : ride p x z∈tube n:=by
  change shade _∈fields n; rw [ride_shade]; exact fields_upper hp hx hz
@[fun_prop] lemma diff_ride (p:Full n)(x:Points n):Differentiable ℂ (ride p x):=by unfold ride; fun_prop
open Work.C13 in
lemma shift_ride {p:Full n}(x:Points n)(q:Points n)(z:ℂ): phase n (ride p x z) q= phase n p q - z * ↑(inner ℝ x q):=by
  unfold ride; simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]; rw [phase_parts (glow 0 x), re_glow,im_glow]; simp [sub_eq_add_neg]

lemma mild : HasTemperateGrowth Real.smoothTransition:=by
  refine ⟨Real.smoothTransition.contDiff,fun j=>?_⟩
  cases j with
  | zero => refine ⟨0,1,fun x=>?_⟩; simpa [Real.norm_of_nonneg (Real.smoothTransition.nonneg x)] using Real.smoothTransition.le_one x
  | succ j =>
    obtain ⟨x,-,hx⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (show (0:ℝ) ≤ 1 from zero_le_one)) ((Real.smoothTransition.contDiff (n:=(j+1:ℕ))).continuous_iteratedFDeriv (m:=j+1) (by simp)).norm.continuousOn --?
    refine ⟨0,‖iteratedFDeriv ℝ (j+1) Real.smoothTransition x‖,fun t=>?_⟩; rw [pow_zero,mul_one]
    by_cases ht:t<0
    · have h:Real.smoothTransition =ᶠ[𝓝 t] (fun _=>(0:ℝ)) := (gt_mem_nhds ht).mono fun w (h : w < 0) => Real.smoothTransition.zero_of_nonpos h.le -- mono needs explicit
      rw [(h.iteratedFDeriv ℝ _).eq_of_nhds,iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; exact norm_nonneg (iteratedFDeriv ℝ (j+1) Real.smoothTransition x) -- ?motive uvar
    by_cases hu:1<t
    · have h:Real.smoothTransition =ᶠ[𝓝 t] (fun _ => (1:ℝ)):= (lt_mem_nhds hu).mono fun w (h : 1 < w) => Real.smoothTransition.one_of_one_le h.le
      rw [(h.iteratedFDeriv ℝ _).eq_of_nhds, iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; exact norm_nonneg _
    exact hx ⟨le_of_not_gt ht,le_of_not_gt hu⟩

section Cut
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def throttle (x:E)(e:ℝ)(p:E) : ℂ:= ↑(Real.smoothTransition ((inner ℝ x p + 2*e) * e⁻¹))
@[fun_prop] lemma permitted (x:E)(e:ℝ) : HasTemperateGrowth (throttle x e) := by
  unfold throttle; have h:= mild; fun_prop
lemma swift {x p:E}{e:ℝ}(he:0<e)(hx:-e ≤ inner ℝ x p):throttle x e p=1:=by
  unfold throttle; rw [Real.smoothTransition.one_of_one_le,Complex.ofReal_one]; rw [← div_eq_mul_inv, one_le_div he]; linarith
lemma dark {x p:E}{e:ℝ}(he:0<e)(hx:inner ℝ x p≤ -(2*e)) : throttle x e p=0:=by unfold throttle; rw [Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)),Complex.ofReal_zero]
def power (x:E)(e:ℝ):Probe E →L[ℂ] Probe E:= SchwartzMap.smulLeftCLM ℂ (throttle x e)
@[simp] lemma power_apply (x:E)(e:ℝ)(v:Probe E)(p:E):power x e v p= throttle x e p * v p:=SchwartzMap.smulLeftCLM_apply_apply (permitted ..) ..
lemma power_support (x:E)(v:Probe E){e:ℝ}(he:0<e): tsupport ⇑(power x e v) ⊆ {p| -(2*e)≤ inner ℝ x p}:=closure_minimal (fun p hp=> le_of_not_gt (fun h=> hp (by rw [power_apply,dark he h.le,zero_mul]))) (isClosed_le continuous_const (by fun_prop))

def expStep (x:E)(z:ℂ) : E→L[ℝ]ℂ:=-z • (Complex.ofRealCLM.comp (innerSL ℝ x))
@[simp] lemma expStep_apply (x:E)(z:ℂ)(p:E):expStep x z p= -z * ↑(inner ℝ x p):=rfl
lemma expStep_bound (x:E)(z:ℂ) : ‖expStep x z‖ = ‖z‖ * ‖Complex.ofRealCLM.comp (innerSL ℝ x)‖ :=by unfold expStep; rw [norm_smul,norm_neg]
lemma power_rent (x:E){a:ℝ}(ha:0<a)(i:ℕ):∃ C:ℝ, 0≤C ∧ ∀ z:ℂ, ‖expStep x z‖^i ≤ C * Real.exp (a*‖z‖):=by
  let b:=‖Complex.ofRealCLM.comp (innerSL ℝ x)‖ ^ i
  have hb:0≤b:=by unfold b; positivity
  obtain ⟨C,hC,h⟩:= Work.C13.exists_polynomial_exp_bound 0 ha i
  refine ⟨C*b,mul_nonneg hC hb,fun z=>?_⟩; rw [expStep_bound,mul_pow]; change ‖z‖^i*b ≤ _
  have H:=h ‖z‖ (norm_nonneg _); rw [zero_sub, Real.exp_neg,← div_eq_mul_inv] at H
  calc
    ‖z‖^i*b ≤ (1+‖z‖)^i*b:=by gcongr; linarith
    _ ≤ (C*Real.exp (a*‖z‖))*b:=mul_le_mul_of_nonneg_right ((div_le_iff₀ (by positivity)).mp H) hb
    _ = _ :=by ring
lemma coast {a:ℝ}(ha:0<a)(x:E)(g:Probe E)(hs: tsupport ⇑g⊆ {p| -(2*a)≤ inner ℝ x p}) (k j:ℕ):
    ∃ C:ℝ, 0≤ C ∧ ∀ z:ℂ,0≤ z.re→ ∀ q:Probe E,
      (∀ p:E,q p=Complex.exp (expStep x z p)*g p) → size k j q ≤ C*Real.exp (3*a*‖z‖):=by
  choose R hR h using power_rent x ha
  have hb:0 ≤ ∑ i∈Finset.range (j+1),(j.choose i:ℝ)*R i *size k (j-i) g:=Finset.sum_nonneg fun i _=> by have hv:=hR i; unfold size; positivity
  refine ⟨_,hb, fun z hz q he=>?_⟩
  apply SchwartzMap.seminorm_le_bound ℂ _ _ _ (by positivity); intro y
  let F:= fun p=>Complex.exp (expStep x z p); have hF:ContDiff ℝ ∞ F := (expStep x z).contDiff.cexp
  rw [show (q:E→ℂ)= (fun p=>F p*g p) from funext he]
  by_cases hy:y∈tsupport g
  swap
  · have hh : tsupport (iteratedFDeriv ℝ j (fun y=> F y*g y)) ⊆ tsupport ⇑g := (tsupport_iteratedFDeriv_subset j).trans tsupport_mul_subset_right
    rw [image_eq_zero_of_notMem_tsupport (fun he=> hy (hh he)),norm_zero,mul_zero]
    positivity
  apply le_trans (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le hF (g.smooth ⊤) y (n:=j) (by exact_mod_cast le_top)) (by positivity)); rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_le_sum; intro i _
  have hx : ‖iteratedFDeriv ℝ i F y‖ ≤ R i * Real.exp (3*a*‖z‖):=by
    have ht: (expStep x z y).re ≤ 2*a*‖z‖:=by
      rw [expStep_apply, Complex.mul_re]; simp only [Complex.ofReal_im,mul_zero,sub_zero,Complex.neg_re,Complex.ofReal_re]
      calc
        _ ≤ -z.re * (-(2*a)):=mul_le_mul_of_nonpos_left (hs hy) (neg_nonpos.mpr hz)
        _ ≤ 2*a* ‖z‖:= by nlinarith [Complex.re_le_norm z]
    refine (Work.C13.norm_iteratedFDeriv_exp_linear_le _ _ _).trans ?_
    refine (mul_le_mul (h i z) (Real.exp_le_exp.mpr ht) (Real.exp_pos _).le (mul_nonneg (hR _) (by positivity))).trans_eq ?_
    rw [mul_assoc,← Real.exp_add]; ring_nf
  calc
     _ ≤ ‖y‖^k * ((j.choose i:ℝ)*(R i * Real.exp (3*a*‖z‖))* ‖iteratedFDeriv ℝ (j-i) g y‖) := by gcongr
     _ = ((j.choose i:ℝ)*R i * (‖y‖^k* ‖iteratedFDeriv ℝ (j-i) g y‖)) * Real.exp (3*a*‖z‖) := by ring
     _ ≤ _:= by have := hR i; gcongr; exact SchwartzMap.le_seminorm ℂ k (j-i) g y
end Cut

variable {G : Gauge} {L:Register G}{S:Table L}{W:Surface S}{D:∀ n:ℕ, Blanket n}
variable (X:W.Aurora D)(v:Fin n→S.Union)

lemma income (y:Points n)(hy:y∈shores n){p:Full n}(hp:p∈tube n) {a:ℝ}(ha:0<a) (h:dsupport (Distn.fourier (W.W n v)) ⊆ coneM n):
    ∃ C:ℝ, 0≤C ∧ ∀ z:ℂ,0≤z.re → ‖X.emit v (ride p y z)‖ ≤ C * Real.exp (3*a*‖z‖):= by
  let U:= fun z=> power y a (X.lens n (ride p y z))
  let f:= ((pref (Points n))⁻¹:ℂ) • Distn.fourier (W.W n v)
  let q:= (normSeminorm ℂ ℂ).comp (ContinuousLinearMap.toLinearMap f)
  have hq:Continuous q:= continuous_norm.comp (ContinuousLinearMap.continuous f)
  obtain ⟨s,c,-,hh⟩:=Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (Points n) ℂ) q hq
  choose C hC hB using coast ha y (U 0) (power_support y _ ha)
  let b(t:ℕ×ℕ):=C t.1 t.2
  have hc:0≤ ∑ x∈s,b x := Finset.sum_nonneg fun _ _=> hC ..
  refine ⟨(c:ℝ)*∑ x∈s,b x,by positivity,fun z hz=>?_⟩
  have hL:=ride_in hp hy hz
  have hU:f (U z)= X.emit v (ride p y z):=by
    change _ * Distn.fourier (W.W n v) (U z) = _ * Distn.fourier (W.W n v) _
    congr 1; apply sub_eq_zero.mp; rw [← map_sub]
    apply (Distn.due _ _ (closedM _)).1 h
    intro w hw hv
    have hi:=calc -a < 0:= neg_lt_zero.mpr ha
                  _ ≤ inner ℝ w y:= Work.C10.rim hv hy
    let A := {t:Points n|-a < inner ℝ t y}
    have hD : Disjoint A (Function.support (U z-X.lens n (ride p y z))) :=Set.disjoint_left.mpr (fun t ht ht'=> ht' ?_)
    · exact Set.disjoint_left.1 (hD.closure_right (isOpen_lt continuous_const (by fun_prop))) hi hw
    change power y a _ t- X.lens n (ride p y z) t=0
    rw [power_apply,swift ha (by rw [real_inner_comm]; exact le_of_lt ht),one_mul,sub_self]
  rw [← hU]
  apply le_trans (show ‖f (U z)‖ ≤ (c:ℝ) * s.sup (schwartzSeminormFamily ℂ (Points n) ℂ) (U z) from hh _)
  rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ c.coe_nonneg
  apply Seminorm.finset_sup_apply_le (by positivity); intro x hx
  apply le_trans (hB x.1 x.2 z hz _ ?_)
  · exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=b) (fun _ _ => hC ..) hx) (by positivity)
  intro w; change power y a _ w=_*power y a _ w
  rw [power_apply,power_apply,ride_zero, X.shape n p hp,X.shape n _ hL, Work.C13.lens_eq,Work.C13.lens_eq, shift_ride]
  rw [expStep_apply, neg_mul,sub_eq_add_neg,Complex.exp_add]; ring

open Asymptotics PhragmenLindelof Complex Bornology in
lemma free_ray (h:dsupport (Distn.fourier (W.W n v)) ⊆ coneM n) (hh:AnalyticOnNhd ℂ (X.emit v) (tube n)) {p:Full n}(hp:p∈tube n){x:Points n}(hx:x∈shores n){K:ℝ}
    (hk:∀ t:ℝ, ‖X.emit v (ride p x (t*I))‖≤K) (z:ℂ) (hz:0≤z.re): ‖X.emit v (ride p x z)‖≤K:=by
  let f (e:ℝ)(z:ℂ):= Complex.exp (-3*(e:ℂ)*z) * X.emit v (ride p x z)
  have hF(e:ℝ)(z:ℂ) : ‖f e z‖= Real.exp (-3*e*z.re)* ‖X.emit v (ride p x z)‖:=by simp [f,Complex.norm_exp,mul_re,mul_im]
  suffices ∀ᶠ e:ℝ in 𝓝[>]0,‖f e z‖ ≤ K by
    apply le_of_tendsto _ this
    simpa [Function.comp_def,f] using (((continuous_norm.comp (show Continuous (fun t:ℝ => f t z) from by unfold f;fun_prop)).tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi 0)))
  filter_upwards [self_mem_nhdsWithin] with e (he:0<e)
  have hd (w:ℂ)(hw:0≤w.re): DifferentiableAt ℂ (f e) w:=(by exact DifferentiableAt.mul (by fun_prop) ((hh _ (ride_in hp hx hw)).differentiableAt.comp _ (diff_ride p x w)))
  obtain ⟨C,hC,h'⟩:=income X v x hx hp he h
  apply right_half_plane_of_bounded_on_real _ _ _ _ hz
  · exact ⟨fun w hw=> (hd w (le_of_lt hw)).differentiableWithinAt, fun w hw=> (hd w (by rwa [closure_setOf_lt_re] at hw)).continuousAt.continuousWithinAt⟩
  · refine ⟨1,one_lt_two,3*e,IsBigO.of_bound C (eventually_inf_principal.mpr ?_)⟩
    apply Eventually.of_forall; intro w hw
    have hw0:0 ≤ w.re:=le_of_lt hw
    rw [hF,Real.rpow_one, Real.norm_of_nonneg (by positivity)]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (h' w hw0)
    apply Real.exp_le_one_iff.mpr; exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) he.le) hw0
  · refine ⟨C,?_⟩; change ∀ᶠ t:ℝ in atTop, ‖f e t‖ ≤ C
    filter_upwards [eventually_ge_atTop 0] with t ht
    refine (le_of_eq (hF ..)).trans ((mul_le_mul_of_nonneg_left (h' t ht) (by positivity)).trans_eq ?_)
    rw [Complex.ofReal_re, Complex.norm_of_nonneg ht, mul_left_comm,← Real.exp_add]; ring_nf
    rw [Real.exp_zero,mul_one] -- ?
  · intro t; simpa [hF] using hk t -- simp? rewrite target also

-- cap over entire real slices is unchanged when moving ANY amount upwards from an acceptable bound
lemma upper_tube (h:dsupport (Distn.fourier (W.W n v)) ⊆ coneM n) (hh:AnalyticOnNhd ℂ (X.emit v) (tube n)) {y:Points n}(hy:y∈fields n){x:Points n}(hx:x-y∈shores n){K:ℝ}
    (hk:∀ t:Points n, ‖X.emit v (glow t y)‖≤K) (z:Points n): ‖X.emit v (glow z x)‖≤K:=by
  let p:=glow z y
  have hp:p∈tube n:=by simp [p,tube,hy]
  have he:ride p (x-y) 1=glow z x:=by
    ext1 i; simp [ride,p,glow]; ring
  rw [← he]
  apply free_ray X v h hh hp hx _ _ (by simp)
  intro t; rw [← valley (ride ..),ride_shade]; simpa [p] using hk (reality (ride p (x-y) (t*Complex.I)))
end YM.GapsContact.Tunnel
