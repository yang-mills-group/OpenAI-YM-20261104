import YM.Integration.WilsonIndependentCollarTeacherPrint

/-! A finite connected part pays its binder once at its own front.
Three or fewer names use the whole native output of the appointed compiler. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarRootedWidth
open Lattice Wilson RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonIndependentCollarPrintIncome

def rooted (n:ℕ)(u:ℝ):ℝ:=if n≤3 then u else u/(n+1)

theorem original {G:Gauge}(s:Widths G)(I:Gear G)(σ:ℝ)(pos:0<σ)(issued:I.s=2*σ)
    (p k n:ℕ):
    let out:=issue s p k I
    let t:=rooted n out.strip
    0<t ∧ t≤out.strip ∧ 8*t*n≤3*σ ∧ t⁻¹≤(n+1)*out.strip⁻¹:=by
  intro out t
  have eligible:out.strip≤σ/8:=by
    apply out.narrow.trans
    apply (min_le_right ..).trans
    apply (min_le_left ..).trans
    rw [issued];linarith
  have cash:0≤out.strip⁻¹:=(inv_pos.mpr out.openStrip).le
  by_cases small:n≤3
  · have eq:t=out.strip:=if_pos small
    rw [eq]
    have card:(n:ℝ)≤3:=by exact_mod_cast small
    refine ⟨out.openStrip,le_rfl,?_,le_mul_of_one_le_left cash (by linarith only [Nat.cast_nonneg (α:=ℝ) n])⟩
    calc _ ≤ (8*out.strip)*3:=mul_le_mul_of_nonneg_left card (by linarith [out.openStrip])
         _ ≤ _:=by linarith only [eligible]
  · have denom:(0:ℝ)<n+1:=by positivity
    have eq:t=out.strip/(n+1):=if_neg small
    rw [eq]
    have actual:0<out.strip/(n+1):=div_pos out.openStrip denom
    have smaller:out.strip/(n+1)≤out.strip:=div_le_self out.openStrip.le (by linarith only [Nat.cast_nonneg (α:=ℝ) n])
    refine ⟨actual,smaller,?_,?_⟩
    · calc _ ≤ 8*(out.strip/(n+1))*(n+1):=mul_le_mul_of_nonneg_left (by linarith) (by linarith only [actual])
           _ = 8*out.strip:=by field_simp
           _ ≤ 3*σ:=by linarith only [eligible,pos]
    · rw [inv_div,div_eq_mul_inv]

end YM.Integration.WilsonIndependentCollarRootedWidth
end
