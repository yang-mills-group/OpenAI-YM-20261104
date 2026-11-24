import YM.Pert.Kinetic.Curl
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson Exterior RG Precision
open Work.F03
open scoped Topology BigOperators Classical ContDiff
variable {n : Side} {G : Gauge} {c : G.Color} (hc : ‖c‖=1) (hn : 4 ≤ n.val) (i j : Axis)
include hc hn
omit hc hn in lemma jump_squares (x m: ℝ) : (Real.cos (x+m)-Real.cos x)^2+(Real.sin (x+m)-Real.sin x)^2=4*Real.sin (m/2)^2 := by
   rw [Real.sin_add,Real.cos_add]
   have e1:=Real.sin_sq_add_cos_sq x; have e2:=Real.sin_sq_add_cos_sq m
   have e3:=Real.cos_two_mul (m/2); rw [mul_div_cancel₀ m (by norm_num: (2:ℝ)≠0)] at e3
   nlinarith only [(Real.sin_sq_add_cos_sq (m/2)),e3,e1,mul_eq_zero_of_left (sub_eq_zero.mpr e1) ((Real.sin m)^2+(Real.cos m-1)^2),e2] -- fix cos double uses cos sq
lemma energy (z : PlaqAxes) (x : Site n) :
    ∑ b : Bool,‖faceCurl (x,z) (lift1 (wave c b i j))‖^2 = 4*Real.sin (Full.mesh n/2)^2*(wedge i j z)^2 := by
   simp only [curl_wave c hc _ hn, norm_smul,hc,mul_one, Real.norm_eq_abs]
   let μ:=Full.mesh n*(lift x j:ℝ)
   have h(b:Bool): |wedge i j z * bump b j x|^2 = (wedge i j z)^2*(trig b (μ+Full.mesh n)-trig b μ)^2 := by rw [sq_abs,mul_pow];rfl
   change ∑ b:Bool, |wedge i j z * bump b j x|^2 = _
   rw [Fintype.sum_bool,h _,h _]
   dsimp [trig]
   rw [← mul_add,add_comm ((Real.sin (μ + Full.mesh n) - Real.sin μ)^2),jump_squares, mul_comm ((wedge i j z)^2)]
omit hc hn in private lemma wedge_single (hij : i < j) : ∑ z:PlaqAxes,wedge i j z ^ 2=1 := by
   rw [Finset.sum_eq_single_of_mem (⟨(i,j),hij⟩ : PlaqAxes) (Finset.mem_univ ..)]
   · simp [wedge,(show ¬(i=j ∧ _) from fun h=>hij.ne h.1)]
   intro z hz hi; have hZ := z.property; change z.1.1 < z.1.2 at hZ
   unfold wedge
   split_ifs with he he2
   · grind
   · exact False.elim (not_lt_of_ge hij.le (he.2 ▸ he.1 ▸ hZ))
   · exact False.elim (hi (Subtype.ext (by grind)))
   norm_num
lemma all_energy (hij : i ≠ j) : (∑ x:Face (Per n), ∑ b : Bool, ‖faceCurl x (lift1 (wave c b i j))‖^2) =
      (Fintype.card (Site n) : ℝ)*(4*Real.sin (Full.mesh n/2)^2) := by
   rw [Fintype.sum_prod_type]
   simp only [energy hc hn, ←Finset.mul_sum]
   have h : ∑ z:PlaqAxes,wedge i j z^2=1:= by
      rcases lt_or_gt_of_ne hij with hi|hi
      · exact wedge_single i j hi
      have he(z):wedge i j z^2=wedge j i z^2:=by unfold wedge;split_ifs <;> norm_num <;> grind -- fix
      simp_rw [he,wedge_single j i hi]
   simp [h,mul_comm]

end YM.Pert.Kinetic
