import YM.Integration.FVA1Physical.Wilson.CoarseRows
import YM.MSbar.Bronze.Seat

/-! Change the coupling and the field scale of a normalized mixed observable.
Every homogeneous degree in the observable is retained. The kinetic (unmarked)
radial truncation is recovered when the incoming bank has the action grading. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG
open MSbar MSbar.Cacao MSbar.Bakery MSbar.Wave MSbar.Rolling.Price MSbar.Whisk MSbar.Rolling MSbar.Bakery.Portal
open scoped Classical Topology BigOperators
variable {σ ι:Type} [Fintype σ]

def sourceFare (cap:ℕ) (b:PowerSeries ℝ) (T:PowerSeries (Pot σ)) (i j:ℕ) : Pot σ :=
  ∑ d ∈ range (cap+1), PowerSeries.coeff j (b^d*b⁻¹^i) • homogeneousComponent d (PowerSeries.coeff i T)

def sourceClock (cap:ℕ) (b:PowerSeries ℝ) (T:PowerSeries (Pot σ)) : PowerSeries (Pot σ) :=
  PowerSeries.mk fun n=> ∑ i ∈ range (n+1), sourceFare cap b T i (n-i)

omit [Fintype σ] in
theorem sourceClock_cap (b:PowerSeries ℝ) (T:PowerSeries (Pot σ)) (p m d:ℕ)
    (hh:∀ i ≤ p, (PowerSeries.coeff i T).totalDegree ≤ m) (hm:m ≤ d) :
    Lap p (sourceClock m b T) (sourceClock d b T) := by
  intro i hi
  simp only [sourceClock,PowerSeries.coeff_mk]
  apply sum_congr rfl
  intro j hj
  apply sum_subset (range_mono (Nat.succ_le_succ hm))
  intro n _ outside
  have bound: (PowerSeries.coeff j T).totalDegree < n := lt_of_le_of_lt
    (hh j ((Nat.lt_succ_iff.mp (mem_range.mp hj)).trans hi)) (by simpa only [mem_range,Nat.lt_succ_iff,not_le] using outside)
  rw [homogeneousComponent_eq_zero _ _ bound,smul_zero]

omit [Fintype σ] in
theorem sourceClock_kinetic (b:PowerSeries ℝ) (T:PowerSeries (Pot σ)) (p m:ℕ) (hm : p + 2 ≤ m)
    (act:Expanse T 1 p) : Lap p (ticket b T) (sourceClock m b T) := by
  intro i hi
  simp only [ticket,sourceClock,PowerSeries.coeff_mk]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ i :=Nat.lt_succ_iff.mp (mem_range.mp hj)
  apply sum_subset (range_mono (show j+2+1 ≤ m+1 by omega))
  intro k _ hk
  have deg: (PowerSeries.coeff j T).totalDegree ≤ j+2:=by simpa only [one_mul] using act.profile j (hj'.trans hi)
  have hk':j+2<k:=by simpa only [mem_range,Nat.lt_succ_iff,not_le] using hk
  rw [homogeneousComponent_eq_zero _ _ (deg.trans_lt hk'),smul_zero]

omit [Fintype σ] in
private theorem clock_read (b:PowerSeries ℝ) (T:PowerSeries (Pot σ)) (m n:ℕ) (x:View σ) (t:ℝ) :
    taste n (picture x (sourceClock m b T)) t = ∑ i∈range (n+1),t^i*(∑ d∈range (m+1),
      taste (n-i) (b^d*b⁻¹^i) t*MvPolynomial.eval x (homogeneousComponent d (PowerSeries.coeff i T))) := by
  let g(i j:ℕ):= ∑ d∈range (m+1), PowerSeries.coeff j (b^d*(b⁻¹^i)) *
    MvPolynomial.eval x (homogeneousComponent d (PowerSeries.coeff i T))
  let F(i j):=t^(i+j:ℕ)*g i j
  have hx(a):t^a*PowerSeries.coeff a (picture x (sourceClock m b T))=∑ i∈ range (a+1),F i (a-i):=by
    unfold picture sourceClock
    rw [PowerSeries.coeff_map,PowerSeries.coeff_mk,map_sum,mul_sum]
    apply sum_congr rfl
    intro i hi
    have hi:=mem_range.mp hi
    unfold sourceFare F g
    rw [show i+(a-i)=a by omega]
    simp only [_root_.map_sum,← C_mul',_root_.map_mul,eval_C]
  unfold taste
  simp_rw [hx]
  rw [aims]
  apply sum_congr rfl
  intro i _
  unfold F g
  simp_rw [pow_add,mul_assoc,←Finset.mul_sum]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _=>?_
  rw [Finset.sum_mul]
  exact sum_congr rfl fun a _=>by ring

/-- Substitution by the actual coupling ratio, with the full order-(p+1)
remainder on every allowed family of coarse fields. -/
theorem sourceClock_price {K:ℝ→ι→Prop} (p m:ℕ) (T:PowerSeries (Pot σ))
    (h:∀ i ≤ p,(PowerSeries.coeff i T).totalDegree ≤ m) (x:ℝ→ι→View σ) (hx:Price K 0 x)
    {b:PowerSeries ℝ} {F:ℝ→ℝ} (hf:PowerSeries.coeff 0 b=1) (hF:Approx F b p) :
    Price K (p+1) (fun t i=>taste p (picture (F t • x t i) T) (t/F t) -
      taste p (picture (x t i) (sourceClock m b T)) t) := by
  let W(j d):=homogeneousComponent d (PowerSeries.coeff j T)
  let g(j:ℕ)(d:ℕ)(t):=F t^d*(F t)⁻¹^j
  let χ(j:ℕ)(d:ℕ)(t):=taste (p-j) (b^d*b⁻¹^j) t
  let δ(j d:ℕ)(t):=g j d t-χ j d t
  let B(j d:ℕ)(t)(i:ι):=t^j*δ j d t*MvPolynomial.eval (x t i) (W j d)
  refine (Price.bag (X:=K) (range (p+1)) (fun j t i=>∑ d∈range (m+1), B j d t i)
    (fun j hj=>Price.bag _ (fun d=>B j d) (fun d _=>?_))).egress (Eventually.of_forall fun t i _=>?_)
  · have hj':j ≤ p:=Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hB:Price K (p-j+1) (fun t i=>δ j d t):=Price.inherits
      ((Approx.mul (Approx.powA hF d) (Approx.powA (Approx.invA hF hf) j)).budget (Nat.sub_le p j))
      (z:=fun t i=>()) (Eventually.of_forall fun _ _ _=>trivial)
    rw [show p+1=j+(p-j+1) from by omega]
    exact Price.product (q:=0) ((xrise K j).product hB) (volley x hx _)
  rw [clock_read]
  unfold taste
  rw [← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  rw [picture,PowerSeries.coeff_map]
  have he : ∑ d ∈range (m+1),W j d=PowerSeries.coeff j T := buys m _ (h j (Nat.lt_succ_iff.mp (mem_range.mp hj)))
  nth_rw 1 [←he]
  rw [map_sum,mul_sum,mul_sum,← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  unfold B δ g χ
  have hx:MvPolynomial.eval (F t • x t i) (W j d)=_:=hene (F t) (F t) _ _ _
  rw [hx]
  unfold taste W
  rw [div_eq_mul_inv]
  ring

end YM.Integration.FVA1Physical.Wilson
