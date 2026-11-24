import YM.QuadraticLocal.Lamps
/-! # Descending wallet for the same physical polynomial carrying errors
  Always retain the physical λ normalizations exactly. For finite k-root load
  and no ability to enlarge radii after any one step, track step polynomial
  shrink factor. Restoring to the original costs at MOST the product to the
  total capacity of a single word, not power-cardinality of the entire set of
  tiles. This applies to a full already assembled residual presentation; no new
  continuity/summation assumptions to recover each family, derivatives of mixed
  exponent overlaps still priced before estimates.

  Native `Budget` on `QuadraticLocal.Lamps` and `Kiosk`. Purchase K strong, then apply ANY
  power-of-g restoration via compulsion. Can meet any requested finite number of radii tiers
  before provisioning. Disjointness and product restrictions used implicitly via `Census.choices`.
  Doesn't prove rough all-arity from fixed k budgets; shrink side is ready for that case as well.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Stoop
open Function Filter Finset Wilson Lattice Ac RG Marker
open Push.Corrected Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type*} [DecidableEq V]{R:Census V}{G:Gauge}{P:BudgetPoint}{n:Side}{o:V→Site n}
variable {B k:ℕ} {ι α:Type*} (t : V→ℝ) {t' : V→ℝ} {q s p r W:ℝ}
variable (A:Lamps α ι G P o R)
def radius (r:ℝ):V→ℝ := fun i=> t i / r
omit [DecidableEq V] in
private lemma positiveRadius (ht:∀ i,0<t i)(hr:1≤r)(i:V): 0< radius t r i:=div_pos (ht _) (zero_lt_one.trans_le hr)
private lemma coin (r:ℝ) (i:R.Mode): Poly.toll (radius t r) i = (r^(i.val.card))⁻¹ * Poly.toll t i:=by unfold radius Poly.toll; simp_rw [div_eq_inv_mul,prod_mul_distrib,prod_const,inv_pow]
lemma shrink (v:R.Mode) (hv:v≠R.quiet)(ht:∀ i,0<t i)(hr:1≤r): Poly.toll (radius t r) v≤ r⁻¹ * Poly.toll t v:=by
    rw [coin t]; apply mul_le_mul_of_nonneg_right _ (Poly.worth ht _).le; apply inv_anti₀ (zero_lt_one.trans_le hr);
    nth_rw 1 [← pow_one r]; exact pow_le_pow_right₀ hr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr fun h=>hv (Subtype.ext h)))
private lemma scales {f g:ι→ℝ} (C:ι→Support n)(h:Hit C B f p W) (hg:∀ i,0≤g i) (he:∀ i,g i ≤ r*f i)(hr:0≤ r): Hit C B g p (r*W):=by
    intro x; apply budget_mono (budget_scale hr (h x)); intro i; split; exact mul_nonneg (hg _) (Real.exp_nonneg _); exact le_rfl
    intro i; split; next=> rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (he i) (Real.exp_nonneg _)
    next=> rw [mul_zero]
lemma tighten (ht:∀ i,0<t i)(hr:1≤r)(h:A.Paid t B p q): A.Paid (radius t r) B p (r⁻¹*q):=by
    obtain ⟨f,hf,hF,hP⟩:=h.budget; refine ⟨f,hf,hF,scales _ hP (fun i=>mul_nonneg (Poly.worth (positiveRadius t ht hr) _).le (hf i)) (fun i=>?_) (inv_nonneg.mpr (zero_le_one.trans hr))⟩; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (shrink t _ (A.live i) ht hr) (hf i)
variable (hk:∀ i:R.Mode,i.val.card ≤ k)
include hk in
lemma recovered (ht:∀ i,0<t i)(hr:1≤r)(i:R.Mode): Poly.toll t i≤ r^k*Poly.toll (radius t r) i:= by
   have hm: 0< r:= zero_lt_one.trans_le hr; nth_rw 1 [(show Poly.toll t i=r^i.val.card * Poly.toll (radius t r) i from (by rw [coin t, ← mul_assoc,mul_inv_cancel₀ (pow_pos hm _).ne', one_mul]))]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr (hk i)) (Poly.worth (positiveRadius _ ht hr) _).le
include hk
lemma retake (ht:∀ i,0<t i)(hr:1≤r)(h:A.Paid (radius t r) B p q): A.Paid t B p (r^k*q):=by obtain ⟨f,hf,hF,hP⟩:= h.budget; refine ⟨f,hf,hF,scales _ hP (fun i=>mul_nonneg (Poly.worth ht _).le (hf i)) (fun i=>?_) (pow_nonneg (by linarith only [hr]) _)⟩; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (recovered t hk ht hr _) (hf i)
variable {X:Activities G n} (H:Hard α P X.forced X.K o R)
omit hk in
lemma leaves (ht:∀ i,0<t i)(hr:1≤r)(h:H.Paid t B p q): H.Paid (radius t r) B p q:=by
    have he (x:Poly R): Poly.price (radius t r) x ≤ Poly.price t x:=Finset.sum_le_sum fun i _=> mul_le_mul_of_nonneg_right (by
      by_cases hx:i=R.quiet; subst i; simp only [Poly.quiet_toll,le_refl]; exact (shrink t i hx ht hr).trans (mul_le_of_le_one_left (Poly.worth ht _).le (inv_le_one_of_one_le₀ hr))) (norm_nonneg _)
    obtain ⟨f,hf,h⟩:= h.wages; refine ⟨f,hf,fun i=>budget_mono (h i) ?_ ?_⟩
    · intro j; split; exact mul_nonneg (Poly.nonnegative (positiveRadius _ ht hr) _) (Real.exp_nonneg _); rfl
    intro j; split; exact mul_le_mul_of_nonneg_right (he _) (Real.exp_nonneg _); rfl
lemma budget (ht:∀ i,0<t i)(hr:1≤r)(h:H.Paid (radius t r) B p q): H.Paid t B p (r^k*q):=by
    obtain ⟨f,hf,h⟩:= h.wages; refine ⟨f,hf,scales _ h (fun _=> Poly.nonnegative ht _) (fun i=>?_) (pow_nonneg (zero_le_one.trans hr) _)⟩; unfold Poly.price; rw [mul_sum]; refine sum_le_sum (fun j _=> ?_); rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (recovered _ hk ht hr j) (norm_nonneg _)
end YM.QuadraticLocal.Stoop
