import YM.FormalOPE.RG10.Horizon.Carry
/-! # Shrinking with volume compensation; applied at any nonzero length ratio.
Scope: purely formal station geometry, retains smooth real test and separated columns.
Does not assemble a shell mask. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Arrangements
open Position Grade Maxwell Labels MeasureTheory Topology Metric Function WithLp
open scoped Topology BigOperators ContDiff Classical
open Next.UVStress
variable {m n : ℕ} (s t:ℝ)
  (U:Fore m)(V: Rear n)
local notation "▵" s:max => Next.UVStress.dilate (Real.exp_pos s)
local notation "L" v:max => Real.exp v
private abbrev tone (t:ℝ) := Real.exp (-t)
local notation "l" => tone s
private def ar (x:Points m) := (l^(4*m))⁻¹ * U.core (l⁻¹ • x)
private lemma compressed : tsupport (ar s U) ⊆ (fun x:Points m=> l⁻¹ • x) ⁻¹' tsupport U.core :=
 closure_minimal (fun _ hx=> subset_closure (right_ne_zero_of_mul hx)) (IsClosed.preimage (by fun_prop) (isClosed_tsupport _))

def compress : Fore m where
 core:= ⟨ar s U,contDiff_const.mul (U.core.contDiff.comp (show ContDiff ℝ _ (fun x:Points m=> l⁻¹ • x) by fun_prop)),(U.core.hasCompactSupport.comp_smul (inv_ne_zero (Real.exp_pos (-s)).ne')).mul_left, fun x hx=> (Next.UVStress.enlarged (by exact inv_pos.mpr (Real.exp_pos (-s))) x).2 (U.core.tsupport_subset (compressed _ _ hx))⟩
 budget:= l*U.budget
 sized x hx i:=by
   have hh:=Real.exp_pos (-s); have hl:= U.sized (l⁻¹ • x) (compressed _ _ hx) i;
   change ‖l⁻¹ • x i‖ ≤ _ at hl; rwa [norm_smul,Real.norm_of_nonneg (by exact (inv_pos.mpr hh).le), inv_mul_le_iff₀ hh] at hl

lemma capacity : U.budget < Real.exp t* V.gap ↔ (compress s U).budget < L (t-s) *V.gap := by
 rw [show L (t-s) = tone s *L t from by unfold tone; rw [sub_eq_add_neg,Real.exp_add,mul_comm],mul_assoc]; exact (mul_lt_mul_iff_right₀ (Real.exp_pos (-s))).symm

lemma dilations (T:Test n): (▵ (-s)) ((▵ t) T)= (▵ (t-s)) T:= by
 ext1 x; change (↑((l ^ (4*n))⁻¹):ℂ)*((↑((Real.exp t^(4*n))⁻¹):ℂ)*T ((L t)⁻¹ • (l⁻¹ • x)))=(↑(((L (t-s))^(4*n))⁻¹):ℂ)*T ((L (t-s))⁻¹ • x)
 rw [← mul_assoc,← Complex.ofReal_mul,mul_comm ((l ^ (4*n))⁻¹), show Real.exp (t-s)= l * (L t) from by unfold tone; rw [sub_eq_add_neg,Real.exp_add,mul_comm], ← mul_smul ((L t)⁻¹), mul_inv_rev, mul_pow, mul_inv_rev];

private lemma shrinking (p: Points (m+n))(x:E4): draft (compress s U) V (t-s) (p,x)=(l ^ (4*(m+n)))⁻¹ * draft U V t (l⁻¹ • p,x) := by
 obtain ⟨⟨p,q⟩,rfl⟩:=(@align m n).surjective p; let T:=L t
 have hh : L (t-s)= l*T:= by unfold tone T; rw [sub_eq_add_neg,Real.exp_add,mul_comm]
 unfold draft; dsimp only; rw [ContinuousLinearEquiv.symm_apply_apply, map_smul (@align m n).symm,ContinuousLinearEquiv.symm_apply_apply,hh]
 change ((l^(4*m))⁻¹*U.core (l⁻¹ • (p-(l*T) • slide x)))*V.center x*V.ext ((l*T)⁻¹ • q)*((l*T)^(4*n))⁻¹=(l^(4*(m+n)))⁻¹*(U.core (l⁻¹ • p-T • slide x)*V.center x*V.ext (T⁻¹ • (l⁻¹ • q))*(T^(4*n))⁻¹)
 rw [smul_sub,mul_smul l, inv_smul_smul₀ (Real.exp_pos (-s)).ne',← mul_smul (T⁻¹), mul_inv_rev, Nat.mul_add,pow_add,mul_pow]; simp only [mul_inv_rev]; ring

theorem contracted (hv: U.budget < L t * V.gap) : (▵ (-s)) (test U V t hv) = test (compress s U) V (t-s) ((capacity s t U V).mp hv) := by
 ext1 x; change (↑((l^(4*(m+n)))⁻¹):ℂ) * (↑(pool _ _ _ _):ℂ)=(↑(pool (compress _ _) _ _ x):ℂ)
 unfold pool; simp_rw [shrinking,integral_const_mul,Complex.ofReal_mul]

end YM.FormalOPE.RG10.Arrangements
