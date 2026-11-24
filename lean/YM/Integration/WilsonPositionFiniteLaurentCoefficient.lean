import YM.PertExtension.PTBills

/-! A single finite Laurent revaluation precedes extraction of the normalized
ordinary coefficient.  Each submitted field may have its own native pole. -/
noncomputable section
open Filter Finset PowerSeries
open YM.PertExtension.Series.Tested
open scoped BigOperators
namespace YM.Integration.WilsonPositionFiniteLaurentCoefficient

private lemma lifted {f : ℝ → ℝ} {a : ℕ → ℝ} (H : Aspiration f a) (c : ℝ) (d : ℕ) :
    Aspiration (fun u => c * u^d * f u)
      (fun k => if d ≤ k then c * a (k-d) else 0) := by
  have lead := Aspiration.single c d
  have left := lead.prod H
  have actual : (fun t : ℝ => t^d • c) * f = fun u => c * u^d * f u := by
    funext u
    simp only [Pi.mul_apply, smul_eq_mul]
    ring
  rw [actual] at left
  have mono : PowerSeries.mk (fun j => if j=d then c else 0) =
      C c * X^d := by
    ext j
    rw [coeff_mk, coeff_C_mul, coeff_X_pow]
    split_ifs <;> simp
  have coeffs : conv (fun j => if j=d then c else 0) a =
      (fun k => if d ≤ k then c * a (k-d) else 0) := by
    funext k
    unfold conv term
    rw [mono, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    split_ifs <;> simp
  rw [coeffs] at left
  exact left

private lemma congr_pos {f g : ℝ → ℝ} {a : ℕ → ℝ}
    (H : Aspiration f a) (eqn : ∀ t, 0<t → f t=g t) : Aspiration g a := by
  intro k
  obtain ⟨C,hC,bound⟩ := H k
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_pos, bound] with t ht h
  simpa only [Pi.sub_apply, ← eqn t ht] using h

/-- The coefficient is read at the native shifted order of each unnormalized
Wilson word.  The identity of the real finite integrals is used prior to any
limit in the physical regulators. -/
theorem identify {I : Type*} [Fintype I] (d : I → ℕ) (c : I → ℝ)
    (f : ℝ → ℝ) (a : ℕ → ℝ) (w : I → ℝ → ℝ) (v : I → ℕ → ℝ)
    (hf : Aspiration f a) (hw : ∀ j, Aspiration (w j) (v j))
    (same : ∀ u, 0<u → f u = ∑ j, c j * (u⁻¹)^(d j) * w j u) (k : ℕ) :
    a k = ∑ j, c j * v j (d j+k) := by
  let D := ∑ j, d j
  have top (j : I) : d j ≤ D := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)
  let actual := fun u => u^D * f u
  let A := fun h => if D ≤ h then a (h-D) else 0
  have H₁ : Aspiration actual A := by simpa [actual,A] using lifted hf 1 D
  let ws := fun j (u : ℝ) => c j * u^(D-d j) * w j u
  let vs := fun j h => if D-d j ≤ h then c j * v j (h-(D-d j)) else 0
  have H₂ := Aspiration.sum (Finset.univ : Finset I) ws vs (fun j _ => lifted (hw j) (c j) (D-d j))
  have eqn (u : ℝ) (hu : 0<u) : (∑ j, ws j) u = actual u := by
    simp only [actual, same u hu, Finset.mul_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    have ex : u^D = u^(D-d j) * u^(d j) := by rw [←pow_add,Nat.sub_add_cancel (top j)]
    simp only [ws, ex, inv_pow]
    field_simp
  have agree := congrFun (H₁.unique (congr_pos H₂ eqn)) (D+k)
  simpa [A,vs,Finset.sum_apply, show ∀ j, D≤D+k+d j from fun j => by omega, show ∀ j, D+k-(D-d j)=d j+k from
    fun j => by have := top j; omega] using agree
end YM.Integration.WilsonPositionFiniteLaurentCoefficient
