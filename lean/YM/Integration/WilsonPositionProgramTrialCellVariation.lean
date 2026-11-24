import YM.Integration.WilsonPositionProgramTrialCollarDeposit

/-! Total variation of the actual independent center-smearing at compactly
tested sites, uniform in both the mesh and its inversion period. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialCellVariation
open Set Finset MeasureTheory Metric XSpace XSpace.Rose XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open scoped Classical ENNReal

private def phase (z:ℂ):ℂ:=star z/(‖z‖:ℂ)

private theorem circle (z:ℂ):‖phase z‖≤1:=by
  rw [phase,norm_div,norm_star,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
  by_cases key:z=0
  · simp [key]
  · rw [div_self (norm_ne_zero_iff.mpr key)]

private theorem positive (z:ℂ):z*phase z=(‖z‖:ℂ):=by
  by_cases key:z=0
  · simp [key,phase]
  rw [phase,←mul_div_assoc,Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  push_cast
  apply (div_eq_iff (by exact_mod_cast (norm_ne_zero_iff.mpr key))).mpr
  ring

variable {n:ℕ} (M:Mesh) (φ:Test n)

def mass:ℝ:=M.spacing^(4*n)*∑u:M.Tuple,‖M.smear (M.back u) φ‖

theorem original {D b:ℝ} (small:M.spacing≤1) (nn:0≤b)
    (room:∀x∈tsupport φ,‖x‖≤D) (bound:∀x,‖φ x‖≤b):
    mass M φ≤b*volume.real (closedBall (0:Points n) (D+4*n)):=by
  let Y(t:Sample n):ℂ:=phase (M.smear t.layout φ)
  have read:Deposit M Y φ=(mass M φ:ℂ):=by
    unfold Deposit mass
    push_cast
    simp only [Y,positive]
  have cash:=WilsonPositionProgramTrialConnectedSalary.compact M φ Y small nn zero_le_one room bound
    (fun _ _ _ _=>circle _)
  have paid : 0 ≤ mass M φ:=mul_nonneg (pow_nonneg M.positive.le _) (sum_nonneg fun _ _=>norm_nonneg _)
  rwa [mul_one,read,Complex.norm_real,Real.norm_of_nonneg paid] at cash

theorem gross {D b:ℝ} (small:M.spacing≤1) (nn:0≤b)
    (room:∀x∈tsupport φ,‖x‖≤D) (bound:∀x,‖φ x‖≤b) :
    ‖(M.spacing:ℂ)^(4*n)‖ₑ*∑u:M.Tuple,‖M.smear (M.back u) φ‖ₑ≤
      ENNReal.ofReal (b*volume.real (closedBall (0:Points n) (D+4*n))):=by
  have h:=ENNReal.ofReal_le_ofReal (original M φ small nn room bound)
  simp only [mass,ENNReal.ofReal_mul (pow_nonneg M.positive.le _),
    ENNReal.ofReal_sum_of_nonneg (fun _ _=>norm_nonneg _),ofReal_norm] at h
  simpa only [←ofReal_norm,norm_pow,Complex.norm_real,Real.norm_of_nonneg M.positive.le] using h

end YM.Integration.WilsonPositionProgramTrialCellVariation
end
