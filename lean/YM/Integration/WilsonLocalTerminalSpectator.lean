import YM.Integration.WilsonLocalTerminalWeights

/-! Multiplying the actual local density and its Taylor approximation by
the same fixed signed spectator prices the error in the original measure. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalTerminalSpectator
open WilsonLocalConditionalResidue WilsonLocalTerminalWeights
variable {G:Gauge}

theorem absolute {x y D:ℝ} (h:close x y D) : |x-y|≤(Real.exp D-1)*x := by
  obtain ⟨hx,hy,signed,_,upper⟩:=h
  have buy:0≤D:=(abs_nonneg _).trans signed
  have dual:=relative hy hx (show |Real.log y-Real.log x|≤D from (abs_sub_comm _ _).trans_le signed)
  by_cases xy:x≤y
  · rw [abs_of_nonpos (sub_nonpos.mpr xy)];linarith only [dual.2]
  · have yx:=le_of_not_ge xy
    rw [abs_of_nonneg (sub_nonneg.mpr yx)]
    calc
      x-y≤(Real.exp D-1)*y := by linarith only [upper]
      _≤_ := mul_le_mul_of_nonneg_left yx (sub_nonneg.mpr (Real.one_le_exp buy))

theorem unscaled {x y a D:ℝ} (hy:0<y) (h:close (x/y) a D) : |x-y*a|≤(Real.exp D-1)*x := by
  calc
    _=y*|x/y-a| := by rw [show x-y*a=y*(x/y-a) by field_simp,abs_mul,abs_of_pos hy]
    _≤y*((Real.exp D-1)*(x/y)) := mul_le_mul_of_nonneg_left (absolute h) hy.le
    _=_ := by field_simp

theorem signed {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y a D:ℝ} (hy:0<y) (h:close (x/y) a D) (marked:E) :
    ‖x•marked-(y*a)•marked‖ ≤ (Real.exp D-1)*‖x•marked‖ := by
  have hx:0<x:=(div_pos_iff_of_pos_right hy).mp h.1
  rw [←sub_smul,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hx,←mul_assoc]
  exact mul_le_mul_of_nonneg_right (unscaled hy h) (norm_nonneg _)

end YM.Integration.WilsonLocalTerminalSpectator
