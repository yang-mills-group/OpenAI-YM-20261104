import YM.Integration.WilsonOriginalPublicTrialPhaseRenew
import YM.Integration.WilsonOriginalPublicTrialPhaseArrears

/-! Weights chosen before placing the replicated source on the physical torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseRay
open Lattice Wilson RG Source Labels Extra.Histories MergeProof MergeProof.Accent
open WilsonOriginalPublicTrialPhaseRace WilsonOriginalPublicTrialPhaseArrears
open scoped BigOperators
variable {G:Gauge}

def unit:ℝ:=2*(3+WilsonOriginalPublicTrialPhaseArrears.factor)
theorem unit_pos:0<unit:=by unfold unit;linarith [factor_pos]

def weight (S:Schedule)(r:ℝ)(c i:ℕ):ℝ:=(unit*wage S r c i)⁻¹

theorem weight_pos (S:Schedule){r:ℝ}(hr:0<r)(c i:ℕ):0<weight S r c i:=by
  unfold weight wage
  exact inv_pos.mpr (mul_pos unit_pos (mul_pos (Real.rpow_pos_of_pos (div_pos (S.a_pos _) (S.a_pos _)) _) hr))

theorem paid (S:Schedule){r:ℝ}(hr:0<r)(c i:ℕ){z:ℂ}
    (inc:‖z‖≤WilsonOriginalPublicTrialPhaseArrears.factor*wage S r c (i+1)):
    2*weight S r c (i+1)*
      ((2+Doors.rate (S.block i))*wage S r c (i+1)+‖z‖)≤1:=by
  have pos:0<wage S r c (i+1):=mul_pos
    (Real.rpow_pos_of_pos (div_pos (S.a_pos _) (S.a_pos _)) _) hr
  have bd:Doors.rate (S.block i)≤1:=(Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<3)
    (by exact_mod_cast S.block_large i) (by norm_num : (-(2/5):ℝ)≤0)).trans small.le
  unfold weight
  calc
    _ ≤ 2*(unit*wage S r c (i+1))⁻¹ *((3+WilsonOriginalPublicTrialPhaseArrears.factor)*wage S r c (i+1)) :=by
      apply mul_le_mul_of_nonneg_left _ (by have := unit_pos; positivity)
      calc
        _ ≤ 3*wage S r c (i+1)+WilsonOriginalPublicTrialPhaseArrears.factor*wage S r c (i+1) :=
          add_le_add (mul_le_mul_of_nonneg_right (show 2+Doors.rate (S.block i)≤3 by linarith) pos.le) inc
        _ = _ := by ring
    _ = 1 := by
      field_simp [unit_pos.ne',pos.ne'];unfold unit;ring

def guard (S:Schedule)(i:ℕ)(δ:ℝ):ℕ:=
  max 8 ⌈128*Real.log (Doors.rate (S.block i)*δ)⁻¹⌉₊

theorem wide (S:Schedule)(i:ℕ)(δ:ℝ):8≤guard S i δ:=le_max_left ..

theorem rent (S:Schedule){r:ℝ}(hr:0<r)(c i:ℕ){δ:ℝ}(hδ:0<δ):
    weight S r c i≤(δ*weight S r c (i+1))*MergeProof.Accent.mintK (guard S i δ):=by
  have rate:0<Doors.rate (S.block i):= Real.rpow_pos_of_pos (by exact_mod_cast (S.block i).property) _
  have pr:0<wage S r c (i+1):=mul_pos
    (Real.rpow_pos_of_pos (div_pos (S.a_pos _) (S.a_pos _)) _) hr
  have pay:(Doors.rate (S.block i)*δ)⁻¹≤MergeProof.Accent.mintK (guard S i δ):=by
    unfold MergeProof.Accent.mintK
    rw [←Real.exp_log (inv_pos.mpr (mul_pos rate hδ))]
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<128)).2
    rw [mul_comm]
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 8 ⌈128*Real.log (Doors.rate (S.block i)*δ)⁻¹⌉₊)
  unfold weight
  rw [step S r c i]
  calc
    _ = (δ*(unit*wage S r c (i+1))⁻¹)*(Doors.rate (S.block i)*δ)⁻¹ := by
      field_simp [unit_pos.ne',pr.ne',rate.ne',hδ.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left pay (by have := unit_pos; positivity)

end YM.Integration.WilsonOriginalPublicTrialPhaseRay
end
