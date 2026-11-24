import YM.RG02.Limit.Modes
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Separate the actual vacuum scalar (positive, may also carry a leading power
of t) before taking formal logarithms, even at finite volume. Here identify its
positive scale factored value normalized to 1. Do not exponentiate a
projection after integration as if no other terms occurred. All estimates
here at fixed pointwise as for `Aims`; only pay for finite sums. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Asym
open PertExtension.Series.Tested PertExtension.Series Filter Finset Topology PowerSeries
open Marker Extra.Trajectories Marks Grade Function Asymptotics
open scoped BigOperators Classical
variable {V : Type} [Fintype V] [DecidableEq V] (R : Census V)

def ex (f : PowerSeries ℂ) := PowerSeries.mk fun i =>
    ∑ j∈range (i+1),(j.factorial:ℂ)⁻¹ * coeff i (f^j)

/-- Scalar log over complexification; used on the real-positive branch. -/
def lg (f : PowerSeries ℂ) := PowerSeries.mk fun i =>
    ∑ j∈range i, ((-1:ℂ)^j/(j+1:ℂ))*coeff i ((f-1)^(j+1))

lemma seq_pow {x : PowerSeries ℂ}(h : coeff 0 x=0)(k : ℕ)(i : ℕ)(hi : i<k) : coeff i (x^k)=0 := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    rw [pow_succ, coeff_mul]
    exact sum_eq_zero fun j hj => by
      obtain ht|ht := eq_zero_or_pos j.2
      · rw [ht,h,mul_zero]
      rw [ih _ (by have := mem_antidiagonal.mp hj; omega),zero_mul]

lemma exponential_seq {x : PowerSeries ℂ}(h : coeff 0 x=0)(k : ℕ)(j : ℕ)(hj : k≤j) :
    coeff k (ex x)=coeff k (∑ i∈range (j+1),C ((i.factorial:ℂ)⁻¹)* x^i) := by
   rw [ex,PowerSeries.coeff_mk,map_sum]
   simp_rw [PowerSeries.coeff_C_mul]
   exact sum_subset (range_mono (by omega)) fun i _ hi => by
     simp only [mem_range,not_lt] at hi; rw [seq_pow h _ _ (by omega),mul_zero]

lemma log_seq {x : PowerSeries ℂ}(h : coeff 0 x=1)(k : ℕ)(j : ℕ)(hj : k≤j) :
    coeff k (lg x)=coeff k (∑ i∈range j,C ((-1:ℂ)^i/(i+1:ℂ))*(x-1)^(i+1)) := by
   rw [lg,PowerSeries.coeff_mk,map_sum]
   simp_rw [PowerSeries.coeff_C_mul]
   exact sum_subset (range_mono hj) fun i _ hi => by
     simp only [mem_range,not_lt] at hi
     rw [seq_pow (by simp only [map_sub,h, PowerSeries.coeff_one, if_true, sub_self]) _ _ (by omega),mul_zero]

lemma full_scalar_exp {x : PowerSeries ℂ}(hx : coeff 0 x=0) : scalar R (ex x)=Grade.exponential (scalar R x) := by
   ext1 i
   have hj := exponential_seq hx i (i+Fintype.card V) (by omega)
   rw [Grade.exponential,PowerSeries.coeff_mk, scalar,coeff_map,hj,map_sum,map_sum,map_sum]
   refine sum_congr rfl (fun i _=>?_)
   rw [PowerSeries.coeff_C_mul, map_mul, ← map_pow, PowerSeries.coeff_smul, PowerSeries.coeff_map,Poly.product_bead]

lemma full_scalar_log {x : PowerSeries ℂ}(hx : coeff 0 x=1) : scalar R (lg x) = Grade.logarithm (scalar R x) := by
   ext1 i
   have hj := log_seq hx i (i+Fintype.card V) (by omega)
   rw [Grade.logarithm,PowerSeries.coeff_mk,scalar,coeff_map,hj,map_sum,map_sum,map_sum]
   refine sum_congr rfl fun j _ => ?_
   rw [PowerSeries.coeff_C_mul, map_mul, Poly.product_bead,PowerSeries.coeff_smul,
     show PowerSeries.map (Poly.bead R) x-1=PowerSeries.map (Poly.bead R) (x-1) by rw [map_sub,map_one], ← map_pow, coeff_map]

-- prove for singular integrals via Taylor error estimates AFTER the
-- aggregation has positive nonzero constant vacuum.
section budget
variable {f : PowerSeries ℂ}

lemma small_input (x : ℝ→ℂ)(H : Near x f)(h : coeff 0 f=0) : Bill 1 x := by
   convert! H 0 using 1
   funext p; simp [h,peval,Zone.eval]
lemma exponential_ray {x : ℝ→ℂ}(hx : Near x f)(H : coeff 0 f=0) : Near (Complex.exp ∘ x) (ex f) := by
   intro n
   let v : ℕ→ℂ := fun i => (i.factorial:ℂ)⁻¹
   let R := ∑ i∈range (n+1), C (v i)* f^i
   let P := ∑ i∈range (n+1), v i • x^i
   have hp : Near P R := Near.sums_at _ fun i _ => Near.scaled (Near.stand hx _) _
   have ht : Bill (n+1) (Complex.exp ∘ x-P) := by
      obtain ⟨A,hA,K⟩:= small_input x hx H
      obtain ⟨D,hD,h⟩ := (Complex.exp_sub_sum_range_isBigO_pow (n+1)).exists_pos
      have he : Tendsto x Tested.germ (𝓝 0) := H ▸ Aspiration.tendsto_first hx
      refine ⟨D*A^(n+1),by positivity,?_⟩
      filter_upwards [K,he.eventually h.bound] with t ht hw
      have hu : P t= ∑ i∈range (n+1), (x t)^i/(i.factorial:ℂ) := by
         unfold P; rw [Finset.sum_apply]; exact sum_congr rfl fun i _=> by dsimp only [Pi.smul_apply,Pi.pow_apply,v]; simp only [div_eq_mul_inv,smul_eq_mul,mul_comm]
      change ‖Complex.exp (x t)-P t‖≤ _
      change ‖Complex.exp (x t)-_‖ ≤ D*‖(x t)^(n+1)‖ at hw
      rw [hu]; refine hw.trans ?_
      rw [norm_pow, mul_assoc, ← mul_pow]; gcongr; simpa using ht
   have Hq : peval (fun i => coeff i (ex f)) n=peval (fun i=>coeff i R) n := funext fun t => by
      apply sum_congr rfl; intro i hi; dsimp only
      rw [exponential_seq H i n (Nat.le_of_lt_succ (mem_range.mp hi))]
   convert! bill_add ht (hp n) using 1; rw [sub_add_sub_cancel,Hq]

private lemma log_bound (n : ℕ)(x : ℝ)(h : |x-1|≤1/2) :
    |Real.log x- ∑ i∈range n, ((-1:ℝ)^i/(i+1:ℝ))*(x-1)^(i+1)| ≤ 2 * |x-1|^(n+1) := by
   have ht : |1-x|≤1/2:= by rw [abs_sub_comm]; exact h
   have H := Real.abs_log_sub_add_sum_range_le (x:=1-x) (by linarith) n
   have he : ∀ i:ℕ,(1-x)^(i+1)/(i+1:ℝ) = - (((-1:ℝ)^i/(i+1:ℝ))*(x-1)^(i+1)) := fun i => by rw [show 1-x=(-1)*(x-1) by ring, mul_pow, pow_succ (-1:ℝ)]; ring
   simp only [he, Finset.sum_neg_distrib, sub_sub_cancel] at H
   rw [sub_eq_neg_add]; refine H.trans ?_; rw [abs_sub_comm x]
   refine (div_le_iff₀ (by linarith)).mpr ?_
   nlinarith [mul_nonneg (pow_nonneg (abs_nonneg (1-x)) (n+1)) (show 0≤ 1/2-|1-x| by linarith)]

theorem real_positive_log {x : ℝ→ℝ}(hx : Near (fun t => (x t:ℂ)) f)(H : coeff 0 f=1) :
    Near (fun t=> Complex.ofReal (Real.log (x t))) (lg f) := by
   intro n
   let z := fun t => (x t:ℂ)
   let v (i:ℕ) := (-1:ℂ)^i/(i+1:ℂ)
   let Q := ∑ i∈ range n, C (v i)*(f-1)^(i+1)
   let p := ∑ i∈ range n, (v i) • (z-1)^(i+1)
   let L := fun t => Complex.ofReal (Real.log (x t))
   have hu : Near (z-1) (f-1) := by
      have hi:= Near.lower hx (Near.fixed (1:ℂ)); rw [map_one] at hi; exact hi
   have hq : Near p Q := Near.sums_at _ fun i _ => Near.scaled (Near.stand hu _) _
   have hj : peval (fun i=>coeff i (lg f)) n = peval (fun i => coeff i Q) n := funext fun t => by
      apply sum_congr rfl; intro i hi; dsimp only; rw [log_seq H i n (Nat.le_of_lt_succ (mem_range.mp hi))]
   have hh : Bill (n+1) (L-p) := by
      have hz : coeff 0 (f-1) = 0 := by simp only [map_sub,H,PowerSeries.coeff_one,if_true,sub_self]
      obtain ⟨C,hC,h⟩ := small_input _ hu hz
      have he := (hu.tendsto_first); change Tendsto _ _ (𝓝 (coeff 0 _)) at he; rw [hz] at he
      refine ⟨2*C^(n+1),by positivity,?_⟩
      filter_upwards [h,he.eventually (Metric.ball_mem_nhds 0 (ε:=1/2) (by norm_num))] with t ht hx'
      have hs : ‖(z-1) t‖= |x t-1| := by change ‖(x t:ℂ)-1‖=_; rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      have hE : |x t-1| ≤ C*t:= by rw [←hs]; exact ht.trans_eq (by rw [pow_one])
      have ha : |x t-1| ≤ 1/2 := by rw [←hs]; exact (mem_ball_zero_iff.mp hx').le
      let S := ∑ i∈ range n,((-1:ℝ)^i/(i+1:ℝ))*(x t-1)^(i+1)
      have hH : (L-p) t= ↑(Real.log (x t)-S) := by
         unfold L p S; simp only [Complex.ofReal_sub, Complex.ofReal_sum,Complex.ofReal_pow,Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast,
           Complex.ofReal_add,Complex.ofReal_one, Complex.ofReal_neg, v,Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.pow_apply,Pi.one_apply,z]
      rw [hH,Complex.norm_real,Real.norm_eq_abs]
      refine (log_bound n (x t) ha).trans ?_; rw [mul_assoc, ← mul_pow]; gcongr
   convert! bill_add hh (hq n) using 1; rw [sub_add_sub_cancel,hj]
end budget
end YM.RG02.Asym
