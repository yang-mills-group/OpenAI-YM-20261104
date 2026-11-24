import YM.RG11Proof.Rigidity.Melt
import YM.Next.MAXWELL.Leading

/-!
# Actual short pole at the split. Do *not* evaluate at imaginary points or
assume polarized tensors are arbitrary across quotient slots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Tensor Analysis Maxwell Maxwell.Free Extra.FD.SphereTest Filter Set Function
open scoped BigOperators Topology ContDiff

/-- Includes the opposite and diagonal components (row identity thus has a
factor two off the diagonal and row-norm zero on the diagonal). -/
abbrev Foil := Axis × Axis

def sail (x : E4) (a b : Foil) := wedge (houseM x) a.1 a.2 b.1 b.2

def rotor (x : E4) (a b : Foil) := qRad x * sail x a b

lemma rotor_good (a b : Foil) : ContDiff ℝ ω (fun x => rotor x a b) := by
  let P := fun x : E4 =>
    qRad x * (kr a.1 b.1 * kr a.2 b.2 - kr a.1 b.2 * kr a.2 b.1)
    - 2*x a.1 * (x b.1*kr a.2 b.2-x b.2*kr a.2 b.1)
    - 2*x a.2 * (x b.2*kr a.1 b.1-x b.1*kr a.1 b.2)
  have he : (fun x => rotor x a b)=P := by
    funext x
    by_cases hz : x = 0
    · subst x; simp [rotor,qRad,P]
    unfold rotor sail P wedge houseM qRad
    have hx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    simp only [Matrix.of_apply]
    field_simp; ring
  have hc (i : Axis) : ContDiff ℝ ω (fun x : E4 => x i) := (compAxis i).contDiff
  have hq : ContDiff ℝ ω qRad := contDiff_norm_sq ℝ
  rw [he]; unfold P
  fun_prop (disch := assumption)

lemma full_row (x : E4) (a : Foil) (he : a.1 ≠ a.2) : ∑ b : Foil, (rotor x a b)^2 = 2*qRad x^2 := by
  let q := qRad x
  let m := houseM x
  have ht (b c) : ∑ i : Axis, m b i * m c i = if b=c then 1 else 0 := by
    have hh (c i) : m c i=m i c := (congr_fun (congr_fun (house_star x) i) c)
    conv_lhs => arg 2; intro i; rw [hh c i]
    rw [← Matrix.mul_apply, show m*m=1 from house_square x,Matrix.one_apply]
  have hs : ∑ i : Axis, ∑ j : Axis, (m a.1 i * m a.2 j - m a.1 j * m a.2 i)^2=2 := by
    let u i:=m a.1 i; let v i:=m a.2 i
    have hu (i) : ∑ j : Axis, (u i*v j-u j*v i)^2=u i*u i+v i*v i := by
      have hm (j) : (u i*v j-u j*v i)^2=u i*u i*(v j*v j) + v i*v i*(u j*u j) - 2*(u i*v i)*(u j*v j) := by ring
      simp_rw [hm,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
      unfold u v; simp [ht,he]
    change ∑ i : Axis, ∑ j : Axis,(u i*v j-u j*v i)^2=2
    simp_rw [hu,Finset.sum_add_distrib]
    unfold u v; rw [ht a.1,ht a.2]; simp; norm_num
  rw [Fintype.sum_prod_type]
  change ∑ i : Axis,∑ j : Axis,(q * (m a.1 i*m a.2 j-m a.1 j*m a.2 i))^2= _
  simp_rw [mul_pow, ← Finset.mul_sum,hs]; exact mul_comm ..

variable {G : Gauge}
local notation "ξ" => (4*normal:ℝ)

lemma foilPrice (a b : Foil) (s t c : G.ColorIndex) {x : E4} (hx : x≠0) :
    legKernel (flavor 0 s (cell a.1 a.2)) (flavor 0 t (cell b.1 b.2)) x =
      if s=t then ξ*(qRad x)⁻¹^3 * rotor x a b else 0 := by
  rw [any_ink c _ _ _ _ hx]; split_ifs
  · rw [one_mul,cell_test _ _ _ c hx]
    have hh : cell a.1 a.2 (solutionTurn (house x) (blade b.1 b.2 (1:ℝ))) = sail x a b := by
      change ((solutionTurn (house x) (blade b.1 b.2 (1:ℝ))).val a.1 a.2) _=_
      rw [blade_rot]; exact mul_one _
    unfold rotor; rw [hh]; unfold qRad
    have hq : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    field_simp
  exact zero_mul _

lemma noFoil (a : Axis) : (cell a a) = 0 := by
  ext x; have ht := cell_change x a a; change _=(0:ℝ); linarith

lemma crush_pos : 0 < ξ := by apply mul_pos (by norm_num); exact normal_pos

end YM.RG11.Rigidity
