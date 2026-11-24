import YM.XSpace.Recess

/-!
# Size of unscaled Taylor contacts through input weight

It's enough to leave arbitrary power subunit. Here do not pay infrared rate for
sharp log; prove little o(spacing⁻¹) directly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Shade
open MeasureTheory Function Set Filter Future Lattice Scale Sail Further.FreeCovariance.KP Playpen Drama Lows Mu Chart2 Trace
open scoped Topology BigOperators ContDiff
variable {G:Gauge} {ι: Type} {L: Filter ι} {a:ι→ℝ} {k n d:ℕ}
variable (c:Cut)

def measure {V:Type*}[AddCommMonoid V][Module ℂ V](a:ℝ) (p:Cover→ V): V:= Finsupp.linearCombination ℂ p (outfit c a)
lemma quick_sum {V:Type*}[AddCommMonoid V][Module ℂ V] (a:ℝ)(p:Cover→V): measure c a p=∑ i∈ (outfit c a).support, pace c a i • p i:=by unfold measure; simp [Finsupp.linearCombination_apply, Finsupp.sum, outfit_eq]
lemma sum_eq (b:ℝ) (p:Cover→ℂ): measure c b p=∑' i:Cover, pace c b i * p i:=by
  rw [tsum_eq_sum (s:=(outfit c b).support)]; exact quick_sum ..; intro i hi; rw [← outfit_eq,Finsupp.notMem_support_iff.mp hi,zero_mul]
-- reusable core estimate
private lemma settle (f:ℝ)(b:ℝ)(hf:0<f)(hb:0<b){u:ℝ}(H:b≤2*f*u): f⁻¹^4*f*(u^4)⁻¹ ≤ f*(2/b)^4:=by
  suffices (f*u)^4≥(b/2)^4 by
    have hx:u>0:=by nlinarith
    rw [show (2/b)^4=((b/2)^4)⁻¹ by field_simp]; nth_rw 1 [mul_comm (f⁻¹^4), mul_assoc]; gcongr f*?_; rw [← inv_pow, ← mul_pow,← mul_inv]; rw [inv_pow]; exact inv_le_inv₀ (by positivity) (by positivity) |>.2 this
  gcongr; nlinarith
variable [L.IsCountablyGenerated] (S:Tendsto a L (𝓝 0))(he:∀ᶠ i in L,0<a i)
include S he
lemma lesser (p:Cover→ℂ)(C:ℝ)(hc:0≤C)(P:∀ x,‖p x‖ ≤ C*carry 4 (reach x)): Tendsto (fun i=> (a i:ℂ)*measure c (a i) p) L (𝓝 0):=by
  simp_rw [sum_eq, ← tsum_mul_left]; let F (i:ι) (x:Cover):= (a i:ℂ)*(pace c (a i) x*p x); let b:=c.rOut+1; have hZ : 0<b:= by unfold b; positivity [c.rOut_pos]
  have H(i:ι)(hi:0<a i)(x:Cover): ‖F i x‖ ≤ a i*(C*(area x^4)⁻¹):=by
    unfold F; rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hi.le]; nth_rw 1 [← one_mul (C*(area x^4)⁻¹)] -- maybe occ
    gcongr _ *(?_*?_); exacts [pace_le ..,carry_cost 4 x ▸ P x]
  have T:=flight F he ((near_minor (4*b+1)).const_mul (C*64)) (fun _=> 0) (close_pay C b F hc he (by
    filter_upwards [he,S.eventually (ge_mem_nhds zero_lt_one)] with i hi hh x hx; have hp: pace c (a i) x≠0:=fun hz=>hx (by simp [F,hz]); have he:=included x; constructor
    · have hh':=cent c _ _ hp; unfold b area; linarith
    calc _ ≤ _:=H i hi x
         _ = C*a i*(area x^4)⁻¹:=by ring
         _ ≤ _ := by gcongr C*a i* ?_; rw [← carry_cost, ← carry_cost]; exact carry_weight _ (by decide)
    )) (by
    filter_upwards [almost_all] with x hx
    apply tendsto_zero_iff_norm_tendsto_zero.mpr; let R:ℝ:=‖x‖/2; have hR:0<R:=half_pos (norm_pos_iff.mpr hx); let y i:=mark (a i) x; let B i:=actual (a i) (y i); let D:=C*(2/R)^4
    have hv:= (marks x S he).norm.eventually (le_mem_nhds (show R<‖x‖ by unfold R; linarith [norm_pos_iff.mpr hx]))
    refine squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg (steps (a i) (F i) x)) ?_ (show Tendsto (fun i=>a i*D) L (𝓝 0) by simpa using S.mul_const D)
    filter_upwards [hv,he] with i hi hh; have ht:= (size_actual hh (y i)).2; change R≤‖B i‖ at hi
    change ‖(a i:ℂ)⁻¹^4*F i (y i)‖ ≤ _; rw [norm_mul,norm_pow,norm_inv,Complex.norm_real,Real.norm_of_nonneg hh.le]
    apply le_trans (mul_le_mul_of_nonneg_left (H _ hh _) (by positivity : 0≤(a i)⁻¹^4)); calc
      _= C*((a i)⁻¹^4*a i*(area (y i)^4)⁻¹):=by ring
      _ ≤ _ :=by rw [show a i*D=C*(a i*(2/R)^4) by unfold D; ring]; gcongr C*?_; apply settle _ _ hh hR; exact hi.trans (ht.trans (by unfold area; gcongr; simp))
    )
  simp only [integral_zero] at T; exact T.2

-- pay raw size of counterterms without determining log growth by these estimates.
include he S in
lemma steam (v:Hat G d){P:Tile G}(H:Book G (d+4) P): Tendsto (fun i=>(a i:ℂ)* view v (trunc coin d (overture d (measure c (a i) P)))) L (𝓝 0):= by
  have he(k:ℕ)(hk:k≤d): Tendsto (fun i=> (a i:ℂ)* measure c (a i) (fun x=> view v (Lows.Cut coin k (overture d (P x))))) L (𝓝 0) :=by
    obtain ⟨C,hC,T⟩:= steam_row P H v k; apply lesser c S he _ C hC; intro x; apply (T x).trans; have hk': area x^k≤ area x^d:=pow_le_pow_right₀ (Drama.room x) hk; rw [mul_assoc C,carry_cost, carry_cost]; gcongr C*?_; calc
       _ ≤ area x^d * (area x^(d+4))⁻¹ := mul_le_mul_of_nonneg_right hk' (by positivity [included x])
       _ = _ := by rw [pow_add (area x)]; field_simp [ne_of_gt (included x)]
  have hh:= tendsto_finsetSum (Finset.range (d+1)) fun i hi=> he i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)); simp only [Finset.sum_const_zero] at hh; refine hh.congr fun i=>?_; unfold trunc; rw [LinearMap.sum_apply,map_sum,Finset.mul_sum]; refine Finset.sum_congr rfl fun j hj=> ?_; rw [quick_sum,quick_sum]; simp_rw [map_sum]; simp_rw [map_smul]
include he S in
theorem weight (P:Tile G) {d:ℕ}(H:Book G (d+4) P): By ℂ L (fun i=> (a i:ℂ) • (⟨trunc coin d (overture d (measure c (a i) P)), transported coin _ _⟩: Stage G d d)) 0:=by
  apply redeemBy (fun v=>readStage v d) no_change; intro v; simp_rw [map_smul,map_zero]; exact steam c S he v H
end YM.XSpace.Shade
