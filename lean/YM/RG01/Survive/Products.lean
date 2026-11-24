import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Armada

/-! # Finite expansion algebra for the unforced log packets

Allow an exact residual/exceptional leaf in the product alphabet (consumer
assigns it grade p+1), so the full product equality never disposes of a
Taylor error and the same derivative charges cover disconnected tensor
partners. Uses genuine derivatives; costs can be used at arbitrarily many
held variables by fixing `j` then choosing prices. The downstream sum over
connected log clusters will add support weights/arities separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Survive.Products
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6
open ConnectedActivityE6.Blaze Brush
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (g : ι → κ → E→ℝ) (f:ι→E→ℝ) (u:ι→κ→ℝ) (F:ι→ℝ) (R:ℝ) (n:ι→κ→ℕ)

/-- Polynomial column for an assignment of a grade to each slot. Includes already
all physical coupling and directional weights in g; no multinomial coefficient
because the slots in the product prescription are ordered kernels. -/
def atGrades (q:ι→κ) (x:E):ℝ := ∏ i,g i (q i) x
def atPrices (j:ℕ) (q:ι→κ):ℝ:= ∏ i,(2^j*u i (q i))
def order (q:ι→κ) := ∑ i,n i (q i)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem literal (q:E)(hp:∀ i, f i q=∑ j,g i j q) : (∏ i,f i q)=∑ s,atGrades g s q:= by
  simp_rw [hp]; exact Fintype.prod_sum (f:=fun i v=>g i v q)

variable {x:E}{j:ℕ}
omit [Fintype κ] in
lemma earns (h:∀ i v,Brush j (u i v) 1 (g i v) x) (q:ι→κ) :
    Brush j (atPrices u j q) 1 (atGrades g q) x := by
  have he:= Brush.all_prod univ (fun i=> g i (q i)) (fun i=>u i (q i)) (fun _=>1) (fun i _=>h i _)
  apply he.trim.climb _ le_rfl
  unfold atPrices; simp only [Finset.prod_mul_distrib,prod_const, card_univ,sum_const,nsmul_eq_mul,mul_one]
  rw [mul_comm ((2^j:ℝ)^Fintype.card ι)]
  gcongr
  · exact prod_nonneg fun i _=>(h i _).nonneg
  rw [← pow_mul,Nat.mul_comm,pow_mul]
  gcongr --
  rw [add_comm]
  exact_mod_cast Nat.lt_two_pow_self (n:=Fintype.card ι)

lemma booked (j:ℕ) (hR:0≤R) (hu:∀ i v, 0≤u i v)
    (h:∀ i, (∑ v, u i v*R^n i v) ≤ F i) :
    (∑ q:ι→κ,atPrices u j q*R^order n q) ≤ ∏ i,(2^j*F i) := by
  unfold order atPrices
  simp_rw [← Finset.prod_pow_eq_pow_sum,← prod_mul_distrib]
  rw [← Fintype.prod_sum (f:=fun i v=>2^j*u i v * R^n i v)]
  apply Finset.prod_le_prod
  · intro i _; exact sum_nonneg fun v _=> by have he:=hu i v; positivity
  intro i _; simp_rw [mul_assoc, ← mul_sum]; exact mul_le_mul_of_nonneg_left (h i) (by positivity)

variable (take : (ι→κ)→Prop)
def filtered (x:E):ℝ:= (univ.filter take).sum fun q=>atGrades g q x
lemma retains (h:∀ i v,Brush j (u i v) 1 (g i v) x) (q:ℕ) (ha:∀ s, take s→q≤order n s)
    (hR:1 ≤ R)(hf:∀ i,(∑ v,u i v *R^n i v)≤ F i) :
    Brush j ((R^q)⁻¹*(∏ i,(2^j*F i))) 1 (filtered g take) x:= by
  let S:=univ.filter take; let C:=atPrices u j
  have hp:= Brush.spree S (atGrades g) C zero_le_one (fun i _=> earns g u h i)
  have hu (i v):= (h i v).nonneg
  have he := booked u F R n j (zero_le_one.trans hR) hu hf
  apply ((show Brush j _ 1 (filtered g take) x from hp).climb _ le_rfl)
  let r:=R^q; have hr:0<r:=by unfold r; positivity
  change (∑ i∈S,C i) ≤ r⁻¹* _; rw [mul_comm,←div_eq_mul_inv,le_div_iff₀ hr,Finset.sum_mul]
  apply le_trans _ he
  have hC i:0≤C i:=by unfold C atPrices; exact Finset.prod_nonneg fun j _=> by have he:=hu j (i j); positivity
  exact le_trans (Finset.sum_le_sum (fun i hi=> mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (ha _ (mem_filter.mp hi).2)) (hC i)))
    (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => mul_nonneg (hC i) (pow_nonneg (by positivity) _))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma apart (x:E): (∑ s,atGrades g s x)=filtered g (fun s=>¬take s) x+filtered g take x:= by
  unfold filtered
  classical
  rw [add_comm]
  convert! (Finset.sum_filter_add_sum_filter_not ..).symm using 1

end YM.RG01.Survive.Products
