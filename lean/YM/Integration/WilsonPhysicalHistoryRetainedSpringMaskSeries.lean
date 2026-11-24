import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskFoot
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskSum

/-! At a fixed physical seat the full countable signed previous row pays
for its own lifted supports under the positive Wilson marginal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter MeasureTheory Lattice RG Wilson OPE.Therm IterationFour PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side}

private theorem capped_mask {f : Config G n→ℝ} (X : Support n) (θ : ℝ) {c : ℝ}
    (cap : ∀U,‖f U‖≤c) (V : Config G n) :
    ‖masked θ X f V‖≤c ∧ ‖masked θ X f V-f V‖≤c := by
  have cn : 0≤c := (norm_nonneg _).trans (cap V)
  by_cases done : Healthy θ X V
  · simp only [masked_eq _ _ _ _ done,sub_self,norm_zero];exact ⟨cap V,cn⟩
  · simp only [masked_ne _ _ _ _ done,norm_zero,zero_sub,norm_neg];exact ⟨cn,cap V⟩

theorem spring_mask_series (R : Run G) (simple : G.Simple) (heat : Poetry R.family.path.levels)
    (q : ℕ) : ∀ᶠ j : ℕ in atTop,∀N,j≤N→∀per h (A : ℕ→Atom G h) (σ C M : ℝ),0<σ→0≤M→
      SumBudget (fun i=>(A i).budget σ) C→∀(s : Signed) (b x : Site (R.family.side j per))
      (X : ℕ→Support (R.family.side j per)) (extra : ℕ) (f : ℕ → Config G (R.family.side j per)→ℝ),
      (∀i,(X i).card≤((A i).footprint x).card+extra)→
      (∀i,Measurable (f i))→(∀i U,‖f i U‖≤(A i).magnitude*2^h*M)→
      let θ:=(R.family.path.rep N per j).p.threshold
      let u (U : Config G (R.family.side j per)):=∑'i,masked θ (X i) (f i) (pull s b U)
      let v (U : Config G (R.family.side j per)):=∑'i,f i (pull s b U)
      let fee:=(625*(Fintype.card PlaqAxes:ℝ))*R.family.path.levels.clock.forcedAllowance j^q
      Measurable (u-v) ∧ (∀U,‖u U-v U‖≤C*(2^h*M)) ∧
        (∫U,‖u U-v U‖ ∂scene R.family.path N per j)≤
          C*(2^h*(1+2*h+extra+σ⁻¹)*M*fee) := by
  filter_upwards [spring_mask_faces R simple heat q] with j paper N live per h A σ C M hs hm paid s b x X extra f shape mf cap θ u v fee
  let μ:=scene R.family.path N per j
  letI : IsProbabilityMeasure μ:=probability R.makes.wilson live
  let raw (i : ℕ) (U : Config G (R.family.side j per)) := f i (pull s b U)
  let mask (i : ℕ) (U : Config G (R.family.side j per)) := masked θ (X i) (f i) (pull s b U)
  let err (i : ℕ) (U : Config G (R.family.side j per)):= mask i U-raw i U
  have mr (i) : Measurable (raw i) := (mf i).comp (continuous_pull s b).measurable
  have mm (i) : Measurable (mask i) := (masked_measurable _ _ _ (mf i)).comp (continuous_pull s b).measurable
  have fe : 0≤fee := mul_nonneg (by positivity) (pow_nonneg (Real.exp_pos _).le _)
  have pa (i) : (A i).magnitude*2^h*M≤(A i).budget σ*(2^h*M) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right ((A i).lower_budget σ hs) (mul_nonneg (by positivity) hm)
  have fund (i) : (∫U,‖err i U‖ ∂μ)≤(A i).budget σ*(2^h*(1+2*h+extra+σ⁻¹)*M*fee) := by
    have bill := paper N live per (X i) s b (f i) _ (mf i) (cap i)
    apply bill.trans
    have price := masked_atom_salary (A i) x (X i) (shape i) hs
    calc
      _ = ((A i).magnitude*2^h*(X i).card)*(M*fee):=by ring
      _ ≤ ((A i).budget σ*(2^h*(1+2*h+extra+σ⁻¹)))*(M*fee):=mul_le_mul_of_nonneg_right price (mul_nonneg hm fe)
      _ = _:=by ring
  let capE:=fun i U=>(capped_mask (X i) θ (cap i) (pull s b U)).2.trans (pa i)
  have budget:=mask_sum_price μ err paid (mul_nonneg (by positivity) hm)
    (mul_nonneg (mul_nonneg (by positivity) hm) fe) (fun i=>(mm i).sub (mr i)) capE fund
  have major:=paid.2.1.mul_right (2^h*M)
  have sumE (U) : u U-v U=∑'i,err i U := by
    have a : Summable fun i=>mask i U := Summable.of_norm_bounded major
      fun i=>(capped_mask (X i) θ (cap i) (pull s b U)).1.trans (pa i)
    have b' : Summable fun i=>raw i U := Summable.of_norm_bounded major fun i=>(cap i _).trans (pa i)
    exact (a.tsum_sub b').symm
  exact ⟨(Measurable.tsum mm).sub (Measurable.tsum mr),fun U=>by rw [sumE];exact budget.2.1 U,
    by simp_rw [sumE];exact budget.2.2⟩

end YM.Integration.OriginalMarkedRunAction
