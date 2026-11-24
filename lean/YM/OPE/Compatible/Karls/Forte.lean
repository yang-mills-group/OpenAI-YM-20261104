import YM.OPE.Compatible.Karls.Mint
/-! # homogeneous crowns, going backwards. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function ContinuousLinearMap
open scoped Topology BigOperators Classical
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{m k i:ℕ}{q:ℝ}(p:E→L[ℝ] E)
local notation "X!"=> E→L[ℝ] E
open Filter Finset
structure Thick {E:Type}[NormedAddCommGroup E](r:ℝ)(f:ℕ→ E):Prop where
    Bill : ∃ t:ℝ,0 ≤ t∧ t < r ∧ ∃ c:ℝ, Hex t f c
-- interp norms
omit [NormedSpace ℝ E] in
lemma Hull {a r u x:ℝ}(hp:0 < a)(ht:0 < r)(hx:0<u)(hz:u<1)(he:a<x)(p:ℕ→ℕ→E)(hh:∃ c:ℝ,∀ i j:ℕ,‖p i j‖≤ c *a^j)(hq:∃ c:ℝ,∀ i j:ℕ,‖p i j‖≤ c*r^j*u^i): ∃ t b:ℝ, 0<t∧t<1∧0<b∧b<x∧ ∃ c:ℝ,0 ≤ c∧∀ i j:ℕ,‖p i j‖≤ c*b^j*t^i:=by
     let f(δ:ℝ):= a^(1-δ)*r^δ; have hF:f 0=a:=(by simp [f]); have hv: _root_.Continuous f:= Continuous.mul (Real.continuous_const_rpow (ne_of_gt hp)|>.comp (continuous_const.sub continuous_id)) (Real.continuous_const_rpow (ne_of_gt ht)); have hY:= hv.continuousAt (x:=0); rw [Metric.continuousAt_iff] at hY; obtain ⟨ε,hε,Hε⟩:= hY (x-a) (sub_pos.mpr he); obtain ⟨w,hw,h'⟩:= exists_between (lt_min zero_lt_one hε); have hw':w<1:=lt_of_lt_of_le h' (min_le_left ..); have h'w:x> f w:=by
          have he:=Hε (show dist w 0 < ε from by rw [Real.dist_eq,sub_zero,abs_of_pos hw]; exact lt_of_lt_of_le h' (min_le_right ..)); rw [Real.dist_eq,hF,abs_lt] at he; linarith only [he.2]
     obtain ⟨c,H⟩:=hh; obtain ⟨d,D⟩:=hq; have hc := (H 0 0); rw [pow_zero,mul_one] at hc; have hc:= (norm_nonneg _).trans hc; have hd:= D 0 0; rw [pow_zero,pow_zero,mul_one,mul_one] at hd; have hd':=(norm_nonneg _).trans hd
     let g:=c^(1-w)*d^w; refine ⟨u^w, f w,(by positivity),Real.rpow_lt_one hx.le hz hw,(by unfold f;positivity),h'w,g,(by unfold g; positivity),fun i j=>?_ ⟩;
     let v:=‖p i j‖; have ha: v=v^(1-w)*v^w:=by
        by_cases h:v=0; · rw [h,Real.zero_rpow (sub_pos.mpr hw'|>.ne'),zero_mul]
        have hz:0 < v:=lt_of_le_of_ne (norm_nonneg _) (Ne.symm h); rw [←Real.rpow_add hz,sub_add_cancel, Real.rpow_one]
     have hi (a c:ℝ)(i:ℕ)(hp:0 ≤ a): (a^i)^c=(a^c)^i:=by rw [←Real.rpow_natCast,←Real.rpow_natCast,←Real.rpow_mul hp,mul_comm (i:ℝ),Real.rpow_mul hp]
     change v≤_; rw [ha]; apply le_trans (mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) (H i j) (by linarith)) (Real.rpow_le_rpow (norm_nonneg _) (D i j) hw.le) (by positivity :0 ≤ v^w) (by positivity)); apply le_of_eq; rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]; unfold g f; rw [mul_pow,hi a _ _ hp.le,hi r _ _ ht.le,hi u _ _ hx.le]; ring
omit [NormedSpace ℝ E] in
lemma fogSum (f:ℕ→ℕ→E){a c r:ℝ}(hp:0≤a)(hn:a<r)(h:∀ i j,‖f i j‖≤ c*a^j*a^i): Hex r (fun i=>∑ j∈Finset.range i,f j (i-1-j)) (c/(r-a)):=by
    let g(i:ℕ):=∑ j∈Finset.range i,(c*a^j*a^(i-1-j)); have H(i:ℕ):g (i+1)=a*g i+c*a^i:=by
         unfold g;rw [sum_range_succ,Finset.mul_sum]; -- use decrement arithmetic
         have he: i+1-1-i=0:=(by omega); rw [he,pow_zero,mul_one]; apply congrArg (·+_); refine sum_congr rfl fun x hx=>?_ ; rw [show i+1-1-x=i-1-x+1 from by have ht:=Finset.mem_range.mp hx; omega,pow_succ]; ring
    have hx :∀ i,g i ≤ c/(r-a)*r^i:=by
         have hc:= h 0 0; rw [pow_zero,mul_one,mul_one] at hc; have hc:0≤c:=(norm_nonneg _).trans hc; have ht:0 < r-a:=sub_pos.mpr hn; have he:r>0:=hp.trans_lt hn
         intro i; induction i with
         | zero=> rw [show g 0=0 from Finset.sum_range_zero _,pow_zero,mul_one]; positivity
         | succ i ih=> rw [H,pow_succ]; have hv := pow_le_pow_left₀ hp hn.le i; apply le_trans (add_le_add (mul_le_mul_of_nonneg_left ih hp) (mul_le_mul_of_nonneg_left hv hc)); apply le_of_eq; field_simp; ring
    intro i; exact (norm_sum_le ..|>.trans ((Finset.sum_le_sum fun j _=> le_trans (h j _) (le_of_eq (mul_right_comm c _ _))).trans (hx i))) -- pattern j i order
end YM.OPE.Hark
