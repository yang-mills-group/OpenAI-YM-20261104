import YM.MSbar.Pulse.Keg
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery
open Function Filter MeasureTheory Cacao PowerSeries Finset
open scoped Topology Classical BigOperators
local notation "G"=> PowerSeries ℝ
local notation "µ"=>PowerSeries.coeff
variable {g h: PowerSeries ℝ}{κ ι :Type*}{α ε p K :ℝ}{n m : ℕ}
lemma Belt_z (n:ℕ) : Belt n (1:G)=1:=by unfold Belt; rw [sum_range_succ']; simp [coeff_one]
lemma Belt_add (n:ℕ)(f g:G): Belt n (f+g) ≤ Belt n f+Belt n g:=by unfold Belt; rw [← sum_add_distrib]; exact sum_le_sum fun i _=> by rw [map_add]; exact abs_add_le ..
lemma Belt_smul (n:ℕ)(r:ℝ)(f:G): Belt n (r•f) = |r| *Belt n f:=by unfold Belt; rw [mul_sum]; apply sum_congr rfl; intro i _; rw [PowerSeries.coeff_smul,smul_eq_mul,abs_mul]
lemma Belt_tone (n:ℕ)(f:G)(i:ℕ): Belt n (f^i) ≤ Belt n f ^i:=by induction i with
    | zero =>rw [pow_zero,pow_zero,Belt_z]
    | succ i ih=> rw [pow_succ,pow_succ]; exact (Belt_product ..).trans (mul_le_mul_of_nonneg_right ih (Belt_pos ..))
lemma taste_power (f:G)(n k:ℕ)(hx:0≤α)(ht:α≤1): |taste n (f^k) α-(taste n f α)^k| ≤ (k:ℝ)*α^(n+1)*(Belt n f)^k:=by
   induction k with
   | zero=> unfold taste; simp_rw [pow_zero]; rw [sum_range_succ']; simp [coeff_one]
   | succ k ih=>
       let x:= taste n f α; let y:= taste n (f^k) α; let s:= taste n (f^(k+1)) α; let A:=α^(n+1); let p:=Belt n f; have ha:0≤ A:=pow_nonneg hx _; have hp:= Belt_pos n f
       have hu : |s-y*x|≤ A*p^(k+1):=by
           unfold s; rw [pow_succ]; exact (taste_mul n _ hx ht ..).trans (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (Belt_tone ..) hp).trans_eq (pow_succ _ _).symm) ha)
       change |s-x^ _|≤ _; rw [pow_succ x,show _ - _*x=(s-y*x)+(y-x^k)*x from (by ring)]
       refine (abs_add_le ..).trans ((add_le_add hu ((abs_mul ..).trans_le (mul_le_mul ih (taste_pays hx ht f) (abs_nonneg x) ((abs_nonneg _).trans ih)))).trans_eq ?_); unfold p A; push_cast; ring
lemma exp_leash (x:ℝ)(n:ℕ) : |Real.exp x -∑ i∈ Finset.range n, x^i / i.factorial| ≤ |x| ^n *Real.exp |x| :=by
    have he:=Complex.norm_exp_sub_sum_le_norm_mul_exp (x:ℂ) n; have ht : Complex.exp (x:ℂ)-∑ i∈ Finset.range n, (x:ℂ)^i/i.factorial = (↑(Real.exp x- ∑ i∈ Finset.range n, x^i / i.factorial):ℂ) :=by push_cast <;> rfl
    rw [ht] at he; simpa only [Complex.norm_real, Real.norm_eq_abs] using he
-- kernel cap at n.. log response.Bodies
noncomputable def bag (n:ℕ)(F:ℝ):= ∑ i∈range (n+1), (i.factorial:ℝ)⁻¹ * F^i
def bores (n:ℕ)(t w b:ℝ):=(t*w)^(n+1)*Real.exp b + ∑ i∈range (n+1), ((i:ℝ)*t^(n+1)*w^i)/(i.factorial:ℝ)
lemma Belt_sumP (n:ℕ)(f:κ→G)(s: Finset κ): Belt n (∑ i∈s,f i) ≤∑ i∈s,Belt n (f i):=by induction s using Finset.induction_on with
   | empty=> simp [Belt]
   | insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; exact (Belt_add ..).trans (add_le_add le_rfl ih)
lemma lavish (f:G)(h:Kind f)(n:ℕ)(hh:Belt n f ≤ K): Belt n (Spring f) ≤ bag n K:=by
   have hp : Belt n (Spring f)=Belt n (Aroma f n):=by unfold Belt; apply sum_congr rfl; intro j hi; rw [issues h (Nat.lt_succ_iff.mp (mem_range.mp hi))]
   rw [hp]; unfold Aroma bag; exact (Belt_sumP ..).trans (sum_le_sum fun i _=> by rw [Belt_smul,abs_of_nonneg (by positivity:0 ≤ (i.factorial:ℝ)⁻¹)]; exact mul_le_mul_of_nonneg_left ((Belt_tone ..).trans (pow_le_pow_left₀ (Belt_pos ..) hh _)) (by positivity))
lemma sauceUp (F:G)(h : Kind F)(t b:ℝ)(hx:0 ≤ t)(ht:t ≤ 1)(hb:Belt n F≤ K)(hT:t*K≤b): |taste n (Spring F) t-Real.exp (taste n F t)| ≤ bores n t K b:=by
   let x:=taste n F t; let f:=Belt n F; have he: |x|≤t*K :=by have hh:= (sauce F n hx ht).trans (mul_le_mul_of_nonneg_left hb hx); rw [h,sub_zero] at hh; exact hh
   let y:= ∑ i∈range (n+1), x^i/i.factorial; have hy : |y-Real.exp x|≤(t*K)^(n+1)*Real.exp b:=by rw [abs_sub_comm]; exact (exp_leash x _).trans (mul_le_mul (pow_le_pow_left₀ (abs_nonneg x) he _) (Real.exp_monotone (he.trans hT)) (Real.exp_pos _|>.le) (pow_nonneg (le_trans (abs_nonneg x) he) _))
   let z:=taste n (Spring F) t; let u:=∑ i∈range (n+1), ((i:ℝ)*t^(n+1)*K^i)/(i.factorial:ℝ)
   have ht : z=∑ i∈ range (n+1),taste n (F^i) t / (i.factorial:ℝ):=by
        unfold z; rw [show taste n (Spring F) t=taste n (Aroma F n) t from ?_]; swap; · unfold taste; exact sum_congr rfl (fun i hi=> by rw [issues h (Nat.lt_succ_iff.mp (mem_range.mp hi))])
        unfold Aroma taste; simp_rw [map_sum,mul_sum];rw [sum_comm]; refine sum_congr rfl fun i _=>?_ ; rw [Finset.sum_div]; exact sum_congr rfl fun j _=> by rw [coeff_smul,smul_eq_mul,div_eq_mul_inv]; ring
   have hz:|z-y|≤u:=by
        unfold u y; rw [ht,← sum_sub_distrib]; refine (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _=>?_); rw [← sub_div,abs_div, abs_of_nonneg (by positivity:0≤ (i.factorial:ℝ))]; refine div_le_div_of_nonneg_right ?_ (by positivity); exact (taste_power F n i hx ‹t≤1›).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Belt_pos ..) hb i) (by positivity))
   change |z-Real.exp x|≤ _; rw [show z-Real.exp x=(z-y)+(y-Real.exp x) by abel]; exact (abs_add_le ..).trans ((add_le_add hz hy).trans_eq (add_comm ..))
end YM.MSbar.Bakery
