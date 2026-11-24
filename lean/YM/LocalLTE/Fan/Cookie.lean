import YM.LocalLTE.Fan.Sharks
/-! multiplicative finite pieces against exponential. point actual. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan.Bakers
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel
variable {v z r W w s t y η γ B a μ: ℝ} {j n m N : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
section
variable {ι : Type*}
lemma financial (c f:Side)(r:ℕ→ℕ)(i:Veil c f): levy r i ≤ mini:= by
  rcases i with i|i; · change chip _+slack≤_; unfold slack chip mini; linarith [Nat.cast_nonneg (α:=ℝ) (r i)]
  exact le_rfl
def ask (x:ℝ) (n:ℕ) := (Nat.factorial (n+1):ℝ)⁻¹ * x^(n+1)
def afloat (n:ℕ)(x:ℝ):= ∑ i:Fin n, ask x i
lemma arrives (x:ℝ)(n:ℕ)(h: |x|≤1) : |Real.exp x-1-afloat n x| ≤ Real.exp 1 * (|x|^(n+1)):= by
  have he: |Real.exp x-(∑ m∈ range (n+1), x^m/(m.factorial:ℕ))| ≤ ‖x‖^(n+1)*Real.exp ‖x‖ := by
    rw [show (|Real.exp x-(∑ m∈ range (n+1), x^m/(m.factorial:ℕ))|:ℝ) = ‖((Real.exp x-(∑ m∈ range (n+1), x^m/(m.factorial:ℕ)):ℝ):ℂ)‖ by rw [Complex.norm_real]; rfl]
    simp only [Complex.ofReal_sub,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_exp, Complex.ofReal_pow]; simpa only [Complex.norm_real] using! Complex.norm_exp_sub_sum_le_norm_mul_exp (x:ℂ) (n+1)
  unfold afloat; rw [← Fin.sum_univ_eq_sum_range (fun m:ℕ=> (x:ℝ)^m/(m.factorial:ℕ)), Fin.sum_univ_succ] at he
  simp only [Fin.val_zero,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one, Fin.val_succ] at he
  simp_rw [ask,← div_eq_inv_mul,sub_sub]; exact he.trans (by rw [mul_comm]; apply mul_le_mul_of_nonneg_right (Real.exp_monotone h) (pow_nonneg (abs_nonneg _) _))
lemma price (h:0≤B)(v:Finset ι) (A D P:ι→ℝ)(hp:∀ i∈v,0≤P i)(ha:∀ i∈v, |A i|≤P i) (he:∀ i∈v, |D i|≤ P i) (hh:∀ i∈v,|A i-D i|≤ B*P i):
   |(∏ i∈v,A i)-(∏ i∈v,D i)|≤(v.card:ℝ)*B*(∏ i∈v,P i):=by
  induction v using Finset.induction_on with
  | empty=> simp
  | insert i v hi ih =>
    let X :ℝ:=∏ j∈v,A j; let Y:ℝ:=∏ j∈v,D j; let H:ℝ:=∏ j∈v,P j; have hx:= mem_insert_self i v
    have hb j (hj:j∈v) :0 ≤ P j:=hp j (mem_insert_of_mem hj)
    have hP:0 ≤H:= prod_nonneg hb
    have hs:|X-Y|≤(v.card:ℝ)*B*H:= ih hb (fun j hj=>ha j (mem_insert_of_mem hj)) (fun j hj=> he j (mem_insert_of_mem hj)) (fun j hj=> hh j (mem_insert_of_mem hj))
    have hy: |Y| ≤ H :=by unfold Y; rw [abs_prod]; exact prod_le_prod (fun i _=> abs_nonneg _) (fun i hi=> he _ (mem_insert_of_mem hi))
    rw [prod_insert hi, prod_insert hi, prod_insert hi,card_insert_of_notMem hi]
    change |A i*X-D i*Y|≤ _; rw [show A i*X-D i*Y=A i*(X-Y)+(A i-D i)*Y by ring]
    apply le_trans (abs_add_le ..); rw [abs_mul,abs_mul]
    exact (add_le_add (mul_le_mul (ha i hx) hs (abs_nonneg _) (hp _ hx)) (mul_le_mul (hh i hx) hy (abs_nonneg _) (mul_nonneg h (hp _ hx)))).trans_eq (by unfold H; push_cast; ring)
lemma rays {D : Finset ι} (p w:ι→ℝ)(h:∀ i∈D,0≤w i)(h₀:∀ i∈D,w i≤1) (hp:∀ i∈D,|p i|≤ w i*r)(hr:0<r)(hv:r≤1) (n:ℕ):
    let a:=2+Real.exp 1; let P:=∏ i∈D,w i; let Y:=a^D.card; let g i:=Real.exp (p i)-1; let f i:= afloat n (p i)
    |(∏ i∈D,g i)| ≤ Y*P ∧ |(∏ i∈D,f i)|≤ Y*P ∧ |(∏ i∈D,g i)-(∏ i∈D,f i)| ≤ Y*P*((D.card:ℝ)*r^n) :=by
  intro a P Y g f; have ha:2≤a:=le_add_of_nonneg_right (Real.exp_pos _).le; have he:0≤a:=le_trans (by norm_num) ha
  have hx i (hi:i∈D):|p i| ≤ w i:= (hp i hi).trans (mul_le_of_le_one_right (h i hi) hv)
  have hg i (hi:i∈D) :|g i| ≤ 2*w i:= (Real.abs_exp_sub_one_le ((hx i hi).trans (h₀ i hi))).trans (mul_le_mul_of_nonneg_left (hx i hi) zero_le_two)
  have hy i (hi:i∈D) : |g i-f i|≤ Real.exp 1* (w i*r^n):= by
    refine (arrives (p i) n ((hx i hi).trans (h₀ i hi))).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    rw [pow_succ']; exact mul_le_mul (hx i hi) (pow_le_pow_left₀ (abs_nonneg _) ((hp i hi).trans (mul_le_of_le_one_left hr.le (h₀ i hi))) _) (pow_nonneg (abs_nonneg _) _) (h i hi)
  let Z i:=a*w i; have hF i (hi:i∈D):|f i|≤ Z i:= by
    calc
     _ ≤ |g i| + |g i-f i|:= by rw [abs_sub_comm (g i) (f i)]; exact norm_le_insert' (f i) (g i)
     _ ≤ _ := by
       apply le_trans (add_le_add (hg i hi) (hy i hi)); unfold Z a; rw [add_mul]; exact add_le_add_right (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (h i hi) (pow_le_one₀ hr.le hv)) (Real.exp_pos _).le) _
  have hz i (hi:i∈D):0≤ Z i:= mul_nonneg he (h i hi); have hh i (hi:i∈D):|g i|≤Z i:= (hg i hi).trans (mul_le_mul_of_nonneg_right ha (h i hi)); have hZ : (∏ i∈D,Z i) = Y*P:= by unfold Z; rw [prod_mul_distrib,prod_const]
  refine ⟨(by rw [abs_prod]; exact (prod_le_prod (fun _ _=> abs_nonneg _) hh).trans_eq hZ),(by rw [abs_prod]; exact (prod_le_prod (fun _ _=> abs_nonneg _) hF).trans_eq hZ),?_⟩
  apply (price (pow_nonneg hr.le n) D g f Z hz hh hF (fun i hi=>?_)).trans_eq ?_
  · rw [hZ,mul_comm]
  unfold Z; apply le_trans (hy i hi); rw [show r^n*(a*w i) = a*(w i*r^n) by ring]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (mul_nonneg (h i hi) (pow_nonneg hr.le _))
end
end YM.LocalLTE.Fan.Bakers
