import YM.GradedFar.Minor
/-! # Inverse and bounded-frame transfer for initial relative orientations -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Billboard
open Function Filter Set
open scoped Topology BigOperators Classical
variable {X R F E:Type*} [SeminormedRing R] {l:Filter X}
lemma switch_price {f g:X→ R} (hf:Tendsto f l (𝓝 1))(h:∀ᶠ x in l,f x*g x=1): Tendsto g l (𝓝 1):=by
 -- includes for op ≤1 not known; purchase actual norm of 1
 have hc:= (tendsto_iff_norm_sub_tendsto_zero.mp hf).eventually_le_const (by norm_num: (0:ℝ) < 1/2)
 have hp:∀ᶠ x in l,‖g x-1‖≤‖f x-1‖*(2*‖(1:R)‖):= by
    filter_upwards [h,hc] with x h he; have hz: ‖g x-1‖ ≤ ‖f x-1‖*‖g x‖:=by
       have hx:1-g x=(f x-1)*g x:=by rw [sub_mul,h,one_mul]
       rw [norm_sub_rev,hx]; exact norm_mul_le ..
    have h': ‖g x‖ ≤ 2*‖(1:R)‖:= by have hp:= norm_sub_norm_le (g x) (1:R); linarith only [mul_le_mul_of_nonneg_right he (norm_nonneg (g x)),hz,hp]
    exact hz.trans (mul_le_mul_of_nonneg_left h' (norm_nonneg _))
 refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall (fun _=> norm_nonneg _)) hp ?_)
 simpa only [zero_mul] using ((tendsto_iff_norm_sub_tendsto_zero.mp hf).mul_const (2*‖(1:R)‖))
lemma twist_price {f g h:X→ R}{C C':ℝ} (hv:Tendsto f l (𝓝 1))(h0:∀ᶠ i in l,g i*h i=1) (hp:∀ᶠ i in l, ‖g i‖ ≤ C)(hk:∀ᶠ i in l, ‖h i‖ ≤ C') :
    Tendsto (fun i=>g i*f i*h i) l (𝓝 1):=by
 have hh:∀ᶠ i in l, ‖g i*f i*h i-1‖ ≤ C* ‖f i-1‖ * C':= by
   filter_upwards [h0,hp,hk] with i h0 hp hk; rw [show g i*f i*h i-1=g i*(f i-1)*h i from by rw [mul_sub,mul_one,sub_mul,h0]]; refine (norm_mul_le ..).trans (mul_le_mul
    ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))) hk (norm_nonneg _) ?_); exact mul_nonneg ((norm_nonneg _).trans hp) (norm_nonneg _)
 refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall (fun _=> norm_nonneg _)) hh ?_)
 simpa only [zero_mul,mul_zero] using (((tendsto_iff_norm_sub_tendsto_zero.mp hv).const_mul C).mul_const C')

variable [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
lemma plan_cpx {L:X→E→L[ℂ] F}{K:E→L[ℂ] F}(h:∀ b:E,Tendsto (fun i=> L i b) l (𝓝 (K b))): Tendsto L l (𝓝 K):=by
 let b:=Module.finBasis ℂ E; let c i:= ContinuousLinearMap.smulRightL ℂ E F (b.coord i).toContinuousLinearMap
 have he(f:E→L[ℂ]F): f=∑ i,c i (f (b i)):=by
   ext x; conv_lhs=> rw [← b.sum_repr x,map_sum];
   rw [_root_.sum_apply]; exact Finset.sum_congr rfl fun i _=> map_smul ..
 nth_rw 1 [he K]; exact Tendsto.congr' (Eventually.of_forall (fun i=>(he _).symm)) (tendsto_finsetSum Finset.univ (fun i _=> (c i).continuous.continuousAt.tendsto.comp (h (b i))))
end YM.Integration.GradedFar.Tariff.Billboard
