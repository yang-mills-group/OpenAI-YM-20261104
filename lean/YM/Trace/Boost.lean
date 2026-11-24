import YM.Mink.Boost
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace
open Mink Set Filter Function Complex Real
open scoped Matrix.Norms.Frobenius InnerProductSpace Topology

/-- Carry a future covector (using an element on the same proper Lorentz group and radian
Euclidean frequency coordinates) to a rest direction. -/
lemma future_rest (x : E4) (hx : x ∈ inside) : ∃ g : Lorentz,
    g.act x = (Real.sqrt (m x)) • basis timeAxis := by
  suffices h : ∃ g : Lorentz, ∃ r > (0:ℝ), g.act x = r • basis timeAxis by
    obtain ⟨g,r,hr,h⟩ := h
    have he := g.keeps x
    rw [h] at he
    refine ⟨g,?_⟩; rw [← he,h]; simp [m,sub_eq_add_neg,Real.sqrt_sq hr.le]
  by_cases h : spatial x = 0
  · refine ⟨1,time x, (strict_self .. |>.mp hx).1,?_⟩
    apply ext_by
    · rw [Lorentz.act_one,Mink.rest_mul,Mink.roll_space,smul_zero,h]
    simp
  let k := ‖spatial x‖
  have hk : 0<k := norm_pos_iff.mpr h
  have ht : 0<time x := (strict_self .. |>.mp hx).1
  let e : Ray := ⟨k⁻¹ • spatial x, by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hk)]; exact inv_mul_cancel₀ hk.ne' ⟩
  let p := Real.artanh (-(k / time x))
  have hp : Real.sinh p * time x = -Real.cosh p * k := by
    have hd : k / time x ∈ Ioc 0 1 := ⟨div_pos hk ht, le_of_lt ((div_lt_one ht).mpr hx)⟩
    have hh : -(k / time x) ∈ Ioo (-1:ℝ) 1 := ⟨by rw [neg_lt_neg_iff]; exact (div_lt_one ht).2 hx,by linarith [hd.1]⟩
    have hp := Real.tanh_artanh hh
    change Real.tanh p = _ at hp
    rw [Real.tanh_eq_sinh_div_cosh] at hp
    field_simp [(Real.cosh_pos _).ne',ht.ne'] at hp
    simpa only [neg_mul_eq_mul_neg, mul_comm] using! hp
  have hE : spatial x=k • e.val := by dsimp only [e]; rw [smul_smul,mul_inv_cancel₀ hk.ne',one_smul]
  have hU : e.along x=k := by
    rw [Ray.along]; dsimp only [e]; rw [real_inner_smul_right,real_inner_self_eq_norm_sq]
    change _*k^2=k; field_simp
  let g := (e.boost p)
  have hg := strict_self _|>.mp (g.stays _|>.mpr hx)
  refine ⟨g,time (g.act x),hg.1,ext_by ?_ ?_⟩
  · dsimp only [g]; rw [Ray.boost_at,Mink.rest_mul,Mink.roll_space,smul_zero,Ray.newSpace,hU,hp,hE]
    rw [show _ + (Real.cosh p - 1) * k = -k from by ring, neg_smul,add_neg_cancel]
  simp
end YM.Trace
