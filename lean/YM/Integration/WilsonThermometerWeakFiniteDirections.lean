import Mathlib.LinearAlgebra.Vandermonde
import YM.Integration.WilsonThermometerWeakSpatialTaylor

/-! A finite one-dimensional set of paid displacement tests extracts just
the first derivative of the full Taylor polynomial. It costs one inverse
displacement even when the required accuracy and Taylor order are large. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakFiniteDirections
open Function Set WilsonThermometerWeakSpatialTaylor
open scoped Classical BigOperators ContDiff
variable {E Y:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup Y][NormedSpace ℝ Y]
def node {M:ℕ}(i:Fin (M+2)):ℝ:=(i.val+1:ℕ)

theorem weights (M:ℕ):∃w:Fin (M+2)→ℝ,∀k<M+2,
    ∑i,w i*node i^k=if k=1 then 1 else 0:=by
  let V:=Matrix.vandermonde (node (M:=M))
  have good:IsUnit V.det:=by
    apply isUnit_iff_ne_zero.mpr
    intro zero
    obtain ⟨i,j,same,diff⟩:=Matrix.det_vandermonde_eq_zero_iff.mp zero
    apply diff
    apply Fin.ext
    dsimp [node] at same
    exact_mod_cast Nat.add_right_cancel (show i.val+1=j.val+1 by exact_mod_cast same)
  let t:Fin (M+2):=⟨1,by omega⟩
  refine ⟨fun i=>V⁻¹ t i,?_⟩
  intro k hk
  have mult:=congrArg (fun m:Matrix (Fin (M+2)) _ ℝ=>m t ⟨k,hk⟩) (Matrix.nonsing_inv_mul V good)
  simp only [Matrix.mul_apply,V,Matrix.vandermonde_apply,Matrix.one_apply] at mult
  simpa only [t,Fin.ext_iff,eq_comm (a:=1)] using mult

theorem selected (M:ℕ)(w:Fin (M+2)→ℝ)
    (select:∀k<M+2,∑i,w i*node i^k=if k=1 then 1 else 0)
    (F:E→Y)(x v:E)(h:ℝ):
    ∑i,w i • polynomial F x (h*node i) (M+1) v = h • fderiv ℝ F x v:=by
  unfold polynomial
  simp_rw [Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  have each (k:ℕ)(hk:k∈Finset.range (M+1+1)):
      ∑i:Fin (M+2),(w i*((k.factorial:ℝ)⁻¹*(h*node i)^k)) • (iteratedFDeriv ℝ k F x (fun _=>v))=
      if k=1 then h • fderiv ℝ F x v else 0:=by
    rw [←Finset.sum_smul]
    have val:∑i,w i*((k.factorial:ℝ)⁻¹*(h*node i)^k)=
        (k.factorial:ℝ)⁻¹*h^k*(∑i,w i*node i^k):=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow];ring
    rw [val,select k (Finset.mem_range.mp hk)]
    by_cases one:k=1
    · subst k; simp [iteratedFDeriv_one_apply]
    · simp [one]
  rw [Finset.sum_congr rfl each]
  simp

theorem bound (M:ℕ)(w:Fin (M+2)→ℝ)
    (select:∀k<M+2,∑i,w i*node i^k=if k=1 then 1 else 0)
    (F:E→Y){U:Set E}(openU:IsOpen U)(smooth:ContDiffOn ℝ ∞ F U){x v:E}(unit:‖v‖=1)
    {h:ℝ}(pos:0<h){B cost:ℝ}(bn:0≤B)
    (safe:∀t∈Icc (0:ℝ) (h*(M+2)),x+t • v∈U)
    (curve:∀t∈Icc (0:ℝ) (h*(M+2)),‖iteratedFDeriv ℝ (M+2) F (x+t • v)‖≤B)
    (prices:∀i:Fin (M+2),‖F (x+(h*node i) • v)‖≤cost):
    h*‖fderiv ℝ F x v‖ ≤ (∑i,|w i|)*(cost+B*(h*(M+2))^(M+2)):=by
  have one (i:Fin (M+2)):0<node i:=by dsimp [node];positivity
  have cap (i:Fin (M+2)):node i≤(M:ℝ)+2:=by
    dsimp [node]
    exact_mod_cast (show i.val+1≤M+2 from i.isLt)
  have point (i:Fin (M+2)):‖polynomial F x (h*node i) (M+1) v‖≤cost+B*(h*(M+2))^(M+2):=by
    have hp:0<h*node i:=mul_pos pos (one i)
    have upper:h*node i≤h*(M+2):=mul_le_mul_of_nonneg_left (cap i) pos.le
    have move {t:ℝ}(ht:t∈Icc (0:ℝ) (h*node i)):t∈Icc (0:ℝ) (h*(M+2)):=⟨ht.1,ht.2.trans upper⟩
    have tr:=remainder F openU smooth (M+1) hp (fun t ht=>safe t (move ht)) (fun t ht=>curve t (move ht))
    rw [unit,one_pow,mul_one] at tr
    have factorial:1≤((M+1).factorial:ℝ):=by exact_mod_cast Nat.factorial_pos (M+1)
    have gross:‖F (x+(h*node i) • v)-polynomial F x (h*node i) (M+1) v‖≤ B*(h*(M+2))^(M+2):=
      (tr.trans (div_le_self (mul_nonneg bn (pow_nonneg hp.le _)) factorial)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le upper _) bn)
    exact (norm_le_norm_add_norm_sub _ _).trans (add_le_add (prices i) (by simpa only [norm_sub_rev] using gross))
  calc h*‖fderiv ℝ F x v‖=‖h • fderiv ℝ F x v‖:=by rw [norm_smul,Real.norm_eq_abs,abs_of_pos pos]
       _=‖∑i,w i • polynomial F x (h*node i) (M+1) v‖:=congrArg norm (selected M w select F x v h).symm
       _≤∑i,‖w i • polynomial F x (h*node i) (M+1) v‖:=norm_sum_le ..
       _≤∑i:Fin (M+2),|w i| * (cost+B*(h*(M+2))^(M+2)):=by
         apply Finset.sum_le_sum
         intro i _
         rw [norm_smul,Real.norm_eq_abs]
         exact mul_le_mul_of_nonneg_left (point i) (abs_nonneg _)
       _=_:=by rw [Finset.sum_mul]
end YM.Integration.WilsonThermometerWeakFiniteDirections
end
