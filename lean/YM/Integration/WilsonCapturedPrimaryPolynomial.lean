import YM.Integration.WilsonCapturedPrimarySamples

/-! Compare the independent polynomial to the true Taylor polynomial on the
same real directions. Only the fixed-order rough derivatives of the true
reading enter; an arbitrarily large common flat value cancels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPolynomial
open Finset Polynomial Set WilsonFirstReceivedRadialStencil
open scoped Classical ContDiff

def weight (D k : ℕ) : ℝ := ∑ j∈range (D+1),
  ‖(Lagrange.basis (range (D+1)) (fun i : ℕ => (node D i : ℂ)) j).coeff k‖

def price (D k : ℕ) : ℝ := k.factorial * weight D k

theorem price_nonneg (D k : ℕ) : 0 ≤ price D k := by unfold price weight; positivity

private theorem coefficient (D k : ℕ) (f : Polynomial ℂ) (h : f.natDegree ≤ D)
    {e : ℝ} (points : ∀ j ≤ D, ‖f.eval (node D j:ℂ)‖ ≤ e) :
    ‖f.coeff k‖ ≤ e*weight D k := by
  let s := range (D+1)
  let v (i : ℕ) : ℂ := node D i
  have inj : InjOn v s := by
    intro i _ j _ h'
    have hij : node D i = node D j := Complex.ofReal_injective h'
    exact_mod_cast (div_left_inj' (by positivity : (D+1:ℕ)≠(0:ℝ))).mp hij
  have deg : f.degree < (s.card : WithBot ℕ) := f.degree_le_natDegree.trans_lt (by
    simp only [s,card_range]; exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le h))
  conv_lhs => rw [Lagrange.eq_interpolate (s:=s) (v:=v) (f:=f) inj deg,
    Lagrange.interpolate_apply,finsetSum_coeff]
  refine (norm_sum_le _ _).trans ?_
  rw [weight,Finset.mul_sum]
  apply sum_le_sum
  intro i hi
  rw [coeff_C_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right (points i (Nat.le_of_lt_succ (mem_range.mp hi))) (norm_nonneg _)

private def rescale (D : ℕ) (t : ℝ) (f : Polynomial ℂ) : Polynomial ℂ :=
  ∑ i∈range (D+1), monomial i ((t:ℂ)^i * f.coeff i)

private theorem scaled_eval {D : ℕ} (t : ℝ) (f : Polynomial ℂ) (h : f.natDegree ≤ D) (u : ℝ) :
    (rescale D t f).eval (u:ℂ) = f.eval ((t*u:ℝ):ℂ) := by
  rw [rescale,eval_finsetSum,eval_eq_sum_range' (Nat.lt_succ_of_le h)]
  apply sum_congr rfl
  intro i _
  simp only [eval_monomial,Complex.ofReal_mul,mul_pow]
  ring

theorem recover (f : ℝ → ℂ) (y : Polynomial ℂ) (D k : ℕ) (hD : y.natDegree ≤ D) (hk : k ≤ D)
    {t E M : ℝ} (ht : 0<t) (hm : 0≤M)
    (smooth : ∀ u∈Icc 0 t, ContDiffAt ℝ (k+1) f u)
    (rough : ∀ u∈Icc 0 t, ‖iteratedDeriv (k+1) f u‖ ≤ M)
    (values : ∀ j ≤ D, ‖f (t*node D j) - y.eval ((t*node D j:ℝ):ℂ)‖ ≤ E) :
    ‖iteratedDeriv k f 0 - (k.factorial:ℂ)*y.coeff k‖ ≤ price D k*(E/t^k+M*t) := by
  let a (i : ℕ) : ℂ := (i.factorial:ℂ)⁻¹*(t:ℂ)^i*iteratedDeriv i f 0
  let T : Polynomial ℂ := ∑ i∈range (k+1), monomial i (a i)
  let Y := rescale D t y
  have hT : T.natDegree ≤ k := natDegree_sum_le_of_forall_le _ _ fun i hi =>
    (natDegree_monomial_le ..).trans (Nat.le_of_lt_succ (mem_range.mp hi))
  have hY : Y.natDegree ≤ D := natDegree_sum_le_of_forall_le _ _ fun i hi =>
    (natDegree_monomial_le ..).trans (Nat.le_of_lt_succ (mem_range.mp hi))
  have fine j (hj : j ≤ D) : ‖(T-Y).eval (node D j:ℂ)‖ ≤ E+M*t^(k+1) := by
    let x := t*node D j
    obtain ⟨hj₀,hj₁⟩ := node_mem hj
    have hx : x∈Icc 0 t := ⟨mul_nonneg ht.le hj₀,
      (mul_le_mul_of_nonneg_left hj₁ ht.le).trans_eq (mul_one _)⟩
    have hw i (hi : i≤k+1) u (hu : u∈Icc 0 t) :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht)
        ((smooth u hu).of_le (Nat.cast_le.mpr hi)) hu
    have tay := taylor_mean_remainder_bound (n:=k) (x:=x) ht.le
      (fun u hu => (smooth u hu).contDiffWithinAt) hx
      (fun u hu => by rw [hw (k+1) le_rfl u hu]; exact rough u hu)
    have eqn : taylorWithinEval f k (Icc 0 t) 0 x = T.eval (node D j:ℂ) := by
      rw [taylor_within_apply]
      unfold T
      simp only [eval_finsetSum,eval_monomial]
      apply sum_congr rfl
      intro i hi
      rw [hw i (le_of_lt (mem_range.mp hi)) 0 (left_mem_Icc.mpr ht.le)]
      simp [a,x,Complex.real_smul,mul_pow]
      ring
    rw [eqn,sub_zero,norm_sub_rev] at tay
    have fac : (1:ℝ) ≤ k.factorial := by exact_mod_cast k.factorial_pos
    have tc := tay.trans ((div_le_self (mul_nonneg hm (pow_nonneg hx.1 _)) fac).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hx.2 _) hm))
    rw [eval_sub,scaled_eval _ y hD]
    have tri := dist_triangle (T.eval (node D j:ℂ)) (f x) (y.eval (x:ℂ))
    simp only [dist_eq_norm] at tri
    exact tri.trans ((add_le_add tc (values j hj)).trans_eq (add_comm ..))
  have obs := coefficient D k (T-Y) ((natDegree_sub_le ..).trans (max_le (hT.trans hk) hY)) fine
  have htK : T.coeff k = a k := by simp [T,finsetSum_coeff,coeff_monomial]
  have hyK : Y.coeff k = (t:ℂ)^k*y.coeff k := by
    simp [Y,rescale,finsetSum_coeff,coeff_monomial,Nat.lt_succ_of_le hk]
  have hf : (0:ℝ)<k.factorial := by exact_mod_cast k.factorial_pos
  have hc : (T-Y).coeff k = (k.factorial:ℂ)⁻¹*(t:ℂ)^k*
      (iteratedDeriv k f 0-(k.factorial:ℂ)*y.coeff k) := by
    rw [coeff_sub,htK,hyK]
    have nk : (k.factorial:ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    unfold a; field_simp [nk]
  rw [hc,norm_mul,norm_mul,norm_inv,norm_pow,Complex.norm_natCast,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos ht] at obs
  have bound : ‖iteratedDeriv k f 0-(k.factorial:ℂ)*y.coeff k‖*t^k ≤
      k.factorial*((E+M*t^(k+1))*weight D k) := by
    calc
      _ = (k.factorial:ℝ)*((k.factorial:ℝ)⁻¹*t^k*‖iteratedDeriv k f 0-
          (k.factorial:ℂ)*y.coeff k‖) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left obs hf.le
  apply (le_div_iff₀ (pow_pos ht k)).2 at bound
  calc
    _ ≤ _ := bound
    _ = _ := by unfold price; rw [pow_succ]; field_simp

end YM.Integration.WilsonCapturedPrimaryPolynomial
