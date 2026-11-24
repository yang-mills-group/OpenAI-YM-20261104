import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6AllFaces
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionRosterLogWindow
import Mathlib.Analysis.Complex.ExponentialBounds

/-! On the same original positive patch, keep the actual geometric action
and compulsory gas, and replace just its bounded regular tilt by a finite
thermal series in both the numerator and the quiet. Uniformly at every
polynomial degree, the approximate quiet stays positive. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.F6Regular
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson OPE.Therm Marked.Inherited RoseCut
open YM.Integration.FVA1Physical.Replica
open scoped Classical BigOperators
open private positive_log_price from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionRosterLogWindow

def tiltTaylor (n:ℕ)(s:ℝ):ℝ:=∑i∈range (n+1),s^i/(i.factorial:ℝ)

private theorem scalar_ratio (n:ℕ)(s ω:ℝ)(small:ω≤1/4)(bound:|s|≤ω):
    let K:=Real.exp s*tiltTaylor n (-s)
    0<K ∧ |Real.log K|≤4*ω^(n+1) ∧ |K-1|≤2*ω^(n+1):=by
  intro K
  have wn:0≤ω:=(abs_nonneg s).trans bound
  have tay:|Real.exp (-s)-tiltTaylor n (-s)|≤|-s|^(n+1)*Real.exp |-s|:=by
    rw [show |Real.exp (-s)-tiltTaylor n (-s)|=‖((Real.exp (-s)-tiltTaylor n (-s):ℝ):ℂ)‖ by rw [Complex.norm_real];rfl]
    simp only [tiltTaylor,Complex.ofReal_sub,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_exp,Complex.ofReal_pow]
    simpa only [Complex.norm_real,Real.norm_eq_abs] using! Complex.norm_exp_sub_sum_le_norm_mul_exp ((-s:ℝ):ℂ) (n+1)
  have ex:Real.exp (s+|s|)≤2:=by
    rw [←Real.exp_log (by norm_num : 0<(2:ℝ)),Real.exp_le_exp]
    linarith only [le_abs_self s,bound,small,Real.log_two_gt_d9]
  have z:|K-1|≤2*ω^(n+1):=by
    have eq:K-1=Real.exp s*(tiltTaylor n (-s)-Real.exp (-s)):=by dsimp only [K];rw [mul_sub,←Real.exp_add,add_neg_cancel,Real.exp_zero]
    rw [eq,abs_mul,abs_of_pos (Real.exp_pos _),abs_sub_comm]
    refine (mul_le_mul_of_nonneg_left tay (Real.exp_pos _).le).trans ?_
    simp only [abs_neg];rw [mul_left_comm,←Real.exp_add]
    exact (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) bound _) ex (Real.exp_pos _).le (pow_nonneg wn _)).trans_eq (mul_comm ..)
  have sq:ω^(n+1)≤ω:=by rw [pow_succ];exact mul_le_of_le_one_left wn (pow_le_one₀ wn (small.trans (by norm_num)))
  have low:= (abs_le.mp z).1
  have pos:0<K:=by linarith only [low,sq,small]
  have log:=positive_log_price (a:=K) (b:=1) pos zero_lt_one (m:=1) zero_lt_one z
    (by linarith only [small,sq]) (le_max_right _ _)
  refine ⟨pos,?_,z⟩;simpa only [Real.log_one,sub_zero,div_one,show 2*(2*ω^(n+1))=4*ω^(n+1) by ring] using log

/-- All seven genuinely normalized conditional readings can use the same
degree-n physical Taylor vacuum. The source caps and exterior are fixed;
the polynomial quiet is retained, instead of being normalized at zero. -/
theorem seven_thermal_polynomial {X:Type*}[MeasurableSpace X](μ:Measure X)[IsProbabilityMeasure μ]
    (u d:X→ℝ)(ue:Envelope u)(pos:∀x,0<u x)(de:Envelope d)(ω:ℝ)(wn:0≤ω)(small:ω≤1/4)(bound:∀x,|d x|≤ω)
    (n:ℕ)(h:Fin 3 → X→ℂ)(eh:∀i,Envelope (h i))(M:Fin 3→ℝ)(mn:∀i,0≤M i)(pay:∀i x,‖h i x‖≤M i):
    let K:=fun x=>Real.exp (d x)*tiltTaylor n (-d x);let v:=fun x=>u x*K x
    let F:=physicalProperRows h;let A:=fun i=>FrozenRead.meanOn μ u (F i);let B:=fun i=>FrozenRead.meanOn μ v (F i)
    (0<∫x,v x ∂μ) ∧ ‖properThree A-properThree B‖≤26*M 0*M 1*M 2*(4*ω^(n+1)):=by
  intro K v F A B
  have ratio(x):=scalar_ratio n (d x) ω small (bound x)
  have kp(x):0<K x:=(ratio x).1
  have poly:Continuous (tiltTaylor n):=by unfold tiltTaylor;fun_prop
  have slope:Continuous (fun t:ℝ=>Real.exp t*tiltTaylor n (-t)):=Real.continuous_exp.mul (poly.comp continuous_neg)
  have ke:Envelope K:=by
    let m:=sSup ((fun x:ℝ=>‖Real.exp x*tiltTaylor n (-x)‖) '' (Set.Icc (-ω) ω))
    have bounded:=isCompact_Icc.bddAbove_image (K:=Set.Icc (-ω) ω) slope.norm.continuousOn
    refine ⟨slope.measurable.comp de.meas,m,fun x=>le_csSup bounded ?_⟩
    exact ⟨d x,abs_le.mp (bound x),rfl⟩
  have ve:Envelope v:=ue.mul ke
  have vp(x):0<v x:=mul_pos (pos x) (kp x)
  have mass {W:X→ℝ}(e:Envelope W)(p:∀x,0<W x):0<∫x,W x ∂μ:=by
    apply (integral_pos_iff_support_of_nonneg (fun x=>(p x).le) (e.integrable μ)).2
    rw [show Function.support W=Set.univ from Set.eq_univ_of_forall (fun x=>(p x).ne')];simp
  let r:=fun x=>-Real.log (K x)
  let t:=4*ω^(n+1)
  have exc:pairExcess r t=∅:=by
    apply Set.eq_empty_iff_forall_notMem.mpr;rintro ⟨x,y⟩
    change ¬t<cap (r x-r y);apply not_lt_of_ge
    apply (min_le_right (1:ℝ) _).trans;apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have p:|r x-r y|≤|r x|+|r y|:=abs_sub .. 
    have x0:|r x|≤t:=by simpa only [r,abs_neg] using (ratio x).2.1
    have y0:|r y|≤t:=by simpa only [r,abs_neg] using (ratio y).2.1
    linarith only [p,x0,y0]
  have same(x):Real.log (u x)-Real.log (v x)=r x+0:=by dsimp only [r,v];rw [Real.log_mul (pos x).ne' (kp x).ne'];ring
  refine ⟨mass ve vp,?_⟩
  have ans:=pair_excess_seven μ (k:=fun _=>1) (r:=r) measurable_const ue.meas ve.meas (fun _=>zero_le_one) pos vp ke.meas.log.neg 0 same t (by dsimp only [t];positivity)
    h eh M mn pay
  simpa only [one_mul,exc,Measure.restrict_empty,integral_zero_measure,zero_div,add_zero] using
    (ans (by simpa only [one_mul] using ue.integrable μ) (by simpa only [one_mul] using ve.integrable μ)
      (by simpa only [one_mul] using mass ue pos) (by simpa only [one_mul] using mass ve vp))

end YM.Integration.FVA1Physical.Exchange.F6Regular
