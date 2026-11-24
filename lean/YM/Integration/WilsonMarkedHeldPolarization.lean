import YM.Planned.ATOM_REGULAR_ESTIMATE.CrossEffect
import YM.AllOrder.Fire.PriceR

/-! A previously priced full field on the scalar-one slice pays the entire
mixed coupling/field tensor, including pure-field directions at scalar zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedHeldPolarization
open Function Filter Finset Tensor AllOrder.Fire
open scoped Topology Classical

variable {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {d:ℕ}
variable (A:T (ℝ×X) ℝ d) {C:ℝ} {F:X→ℝ} (paid:Prices d C F)
  (physical:∀ z,diagonal A ((1:ℝ),z)=F z)

include paid physical in
theorem point (t:ℝ) (z:X): |diagonal A (t,z)|≤C*(|t|+‖z‖)^d :=by
  have visit (s:ℝ) (hs:s≠0):
      |diagonal A (s,z)|≤C*(|s|+‖z‖)^d:=by
    have align : s • ((1:ℝ),s⁻¹ • z)=(s,z):=by simp [Prod.smul_mk,smul_smul,hs]
    rw [←align,Tensor.homogeneous,physical,smul_eq_mul,abs_mul,abs_pow]
    have drag: |s| * (1+‖s⁻¹ • z‖)=|s|+‖z‖:=by
      rw [norm_smul,Real.norm_eq_abs,abs_inv,mul_add,mul_one,←mul_assoc,mul_inv_cancel₀ (abs_ne_zero.mpr hs),one_mul]
    calc |s|^d*|F (s⁻¹ • z)| ≤ |s|^d*(C*(1+‖s⁻¹ • z‖)^d):=
           mul_le_mul_of_nonneg_left (paid.2.2 _) (pow_nonneg (abs_nonneg _) _)
         _ = C*(|s|+‖z‖)^d:=by rw [←drag,mul_pow];ring
  by_cases nz:t≠0
  · exact visit t nz
  have zero:t=0:=not_ne_iff.mp nz
  subst t
  let l:=𝓝[>] (0:ℝ)
  have lhs:Continuous (fun s:ℝ=>|diagonal A (s,z)|):=
    (A.cont.comp (continuous_pi fun _=>continuous_id.prodMk continuous_const)).abs
  have rhs:Continuous (fun s:ℝ=>C*(|s|+‖z‖)^d):=by fun_prop
  apply le_of_tendsto_of_tendsto (b:=l)
    ((lhs.tendsto 0).mono_left nhdsWithin_le_nhds) ((rhs.tendsto 0).mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact visit s (ne_of_gt hs)

include paid physical in
theorem complete (sym:Sym A) : ‖A‖ ≤ Planned.AtomRegular.polarCost d*(C*2^d) :=by
  apply Planned.AtomRegular.op_polar sym (mul_nonneg paid.1 (by positivity))
  intro v hv
  have both:|v.1|+‖v.2‖≤2:=by
    have a:‖v.1‖≤1:=(le_max_left _ _).trans hv
    have b:‖v.2‖≤1:=(le_max_right _ _).trans hv
    rw [Real.norm_eq_abs] at a;linarith
  exact (point A paid physical v.1 v.2).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (add_nonneg (abs_nonneg _) (norm_nonneg _)) both _) paid.1)

end YM.Integration.WilsonMarkedHeldPolarization
end
