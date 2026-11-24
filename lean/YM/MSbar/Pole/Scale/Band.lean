import YM.MSbar.Pole.Scale.Area

/-! # Dimensional dilation law. Strip variable measured in subtraction units. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Filter Set MeasureTheory Ambient Momentum Age Ray
open scoped Topology ContDiff BigOperators Classical Interval
variable {I : Type} [Fintype I]

namespace Mellin
variable (A : Finset I) {F G : ℂ→ Cloud I} {R:ℝ} (h : Meridian (zone R) F)

/-- `roll` only uses the scaled momentum variables. -/
def roll (A : Finset I) (d : Age) (r:ℝ) (F:ℂ→Cloud I) (z:ℂ) : Cloud I:= fun n x=> (r:ℂ)^d.alpha z * F z n (move A r x)
include h
variable {n:ℕ} {z:ℂ} (hz:z∈zone R) (x:External I n)
local notation "swing" => fun (i:ℕ) (t:ℝ)=> spill^[i] (augments A _ F) z (t,x)
include hz
lemma expand (i:ℕ)(t:ℝ) : F z n (move A t x)=(∑ j∈ Finset.range i, (t:ℂ)^j*pbody A F j z n x)+ (t:ℂ)^i * swing i t := by
  induction i with
  | zero=> simp [augments]
  | succ k ih=>
    have hu := splitAt (terms Metric.isOpen_ball (puts h _ (B:=A)) k) hz t x
    change F z n (move A t x)= _ + _ * _
    rw [ih,Finset.sum_range_succ]; unfold pbody
    dsimp only; rw [iterate_succ_apply',hu]; ring

-- root piece antiderivative in the actual integration sector.
variable (d : Age)
def pay (A : Finset I) (d : Age) (F : ℂ→ Cloud I) {n:ℕ} (x : External I n) (z:ℂ) (r : ℝ) :=
    spill^[d.safety] (augments A n F) z (r,x)*(r:ℂ)^(d.alpha z+d.safety-1)

lemma law {r : ℝ} (hr:0<r):
    roll A d r (step A d F) z n x=
    (∫ t in (0:ℝ)..r,pay A d F x z t)+∑ j∈Finset.range d.safety,(r:ℂ)^(d.increment j z) * (eta A d F j z n x) := by
  let e := d.safety; let α := d.alpha z
  have hp k t : spill^[k] (augments A n F) z (t,move A r x)= (r:ℂ)^k * swing k (r*t):= by
    simpa using (carry A h n k (move A r x) x hz 1 r (by intro t; rw [one_mul,nesting A,mul_comm]) t)
  have hr' : (r:ℂ) ≠ 0:= by exact_mod_cast hr.ne'
  unfold roll; rw [area, mul_add]; congr 1
  · simp_rw [hp];
    have hh := intervalIntegral.smul_integral_comp_mul_left (pay A d F x z) (a:=(0:ℝ)) (b:=1) r
    rw [mul_one,mul_zero,intervalIntegral.integral_of_le (show (0:ℝ)≤1 from zero_le_one),Complex.real_smul] at hh
    rw [← hh,← integral_const_mul,← integral_const_mul]; refine setIntegral_congr_fun measurableSet_Ioc (fun t ht=> ?_)
    let a :ℂ:= r; let b:ℂ:= t; let K := swing e (r*t)
    change a^α*(a^e*K*b^(α-1+e))=a*(K*((↑(r*t):ℂ)^(α+e-1)))
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hr.le ht.1.le,Complex.cpow_sub _ _ hr', Complex.cpow_add _ _ hr',Complex.cpow_natCast,Complex.cpow_one]
    rw [sub_add_eq_add_sub]; change a^α*(a^e*K*b^(α+e-1))=a*(K*(a^α*a^e/a*b^(α+e-1)))
    have ha : a≠0:=hr'; field_simp
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i hi=> ?_
  unfold eta increment pbody; rw [hp, mul_zero, Complex.cpow_add _ _ hr',Complex.cpow_natCast]; ring

lemma differential {r:ℝ} (hr:0<r) (hα : 2≤(d.alpha z).re+d.safety) (hh : ∀ j<d.safety,d.increment j z ≠0 ∨ pbody A F j z n x=0) :
    HasDerivAt (fun s : ℝ=>roll A d s (step A d F) z n x) ((r:ℂ)^((d.alpha z)-1)*F z n (move A r x)) r := by
  let v:=d.safety; let α:=d.alpha z; let P:=pay A d F x z
  have hp : Continuous P := by
    unfold P pay; apply Continuous.mul _ (Complex.continuous_ofReal_cpow_const (by simp; linarith))
    let h := terms Metric.isOpen_ball (puts h n (B:=A)) d.safety
    exact continuous_iff_continuousAt.mpr fun t=> (h.stream.smooth (z,t,x) ⟨hz,mem_univ _⟩).continuousAt.comp (x:=t) (f:=fun t:ℝ=>(z,t,x)) (by fun_prop)
  have he := intervalIntegral.integral_hasDerivAt_right (hp.intervalIntegrable (0:ℝ) r) (hp.stronglyMeasurableAtFilter _ _) hp.continuousAt
  let C (j:ℕ)(s:ℝ):= (s:ℂ)^(d.increment j z) * eta A d F j z n x
  let D(j:ℕ):=(r:ℂ)^(α-1+j)* pbody A F j z n x
  have hK j (hj:j∈Finset.range v):HasDerivAt (C j) (D j) r := by
    rcases hh j (Finset.mem_range.mp hj) with hm|hm
    · refine ((hasDerivAt_ofReal_cpow_const hr.ne' hm).mul_const (eta A d F j z n x)).congr_deriv ?_
      unfold eta D; rw [show α-1+j=d.increment j z -1 by rw [increment,sub_add_eq_add_sub] ]; field_simp
    rw [show C j = fun _=>0 by ext1; simp [C,eta,hm],show D j=0 by simp [D,hm] ]; exact hasDerivAt_const ..
  have hj := he.add (HasDerivAt.fun_sum hK)
  refine (hj.congr_deriv ?_).congr_of_eventuallyEq ?_
  · -- derivative value expansion
    rw [expand A h hz x d.safety r]; let y:ℂ:=r; have hy:(r:ℂ)≠0:=by exact_mod_cast hr.ne'
    change pay A d F x z r + ∑ j∈_,D j=_*(_+_); rw [mul_add,Finset.mul_sum,add_comm]; congr 1
    · refine Finset.sum_congr rfl fun i hi=> ?_; unfold D; rw [Complex.cpow_add _ _ hy,Complex.cpow_natCast]; ring
    unfold pay; rw [← sub_add_eq_add_sub,Complex.cpow_add _ _ hy,Complex.cpow_natCast]; ring
  exact mem_of_superset (Ioi_mem_nhds hr) (fun s hs => law A h hz x d hs)
end Mellin
end YM.MSbar.Pole
