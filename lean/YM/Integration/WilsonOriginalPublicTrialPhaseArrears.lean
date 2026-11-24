import YM.Integration.WilsonOriginalPublicTrialPhaseRace

/-! The previously accumulated scalar costs a bounded multiple of the current remainder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseArrears
open Lattice Wilson Source Labels Extra.Histories
open WilsonOriginalPublicTrialPhaseRace
open scoped BigOperators

def drift:ℝ:=(3:ℝ)^(-(2/5:ℝ))
def factor:ℝ:=1/(1-drift)

theorem small:drift<1:=Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
theorem factor_pos:0<factor:=one_div_pos.mpr (sub_pos.mpr small)
theorem renew:(factor+1)*drift≤factor:=by
  have h:=small
  unfold factor
  apply (le_div_iff₀ (sub_pos.mpr h)).2
  field_simp [ne_of_gt (sub_pos.mpr h)]
  nlinarith [show 0≤(1-drift)^2 by positivity]

def incurred (v:ℕ→ℂ):ℕ→ℂ
  | 0=>0
  | i+1=>incurred v i-v i

theorem next (v:ℕ→ℂ)(i:ℕ):incurred v (i+1)+v i=incurred v i:=sub_add_cancel ..

theorem original (S:Schedule)(u h:ℕ)(r:ℝ)(hr:0≤r)(v:ℕ→ℂ)
    (price:∀i,i<h→‖v i‖≤wage S r (u+h) (u+i)):
    ∀i,i≤h→ ‖incurred v i‖≤factor*wage S r (u+h) (u+i):=by
  have pos (i):0≤wage S r (u+h) (u+i):=
    mul_nonneg (Real.rpow_nonneg (div_nonneg (S.a_pos _).le (S.a_pos _).le) _) hr
  intro i hi
  induction i with
  | zero=>
    rw [incurred,norm_zero]
    exact mul_nonneg factor_pos.le (pos 0)
  | succ i ih=>
    have e:i<h:=by omega
    have rate:Doors.rate (S.block (u+i))≤drift:=
      Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<3)
        (by exact_mod_cast S.block_large (u+i)) (by norm_num)
    calc ‖incurred v (i+1)‖ ≤ ‖incurred v i‖+‖v i‖ := norm_sub_le .. 
      _ ≤ (factor+1)*wage S r (u+h) (u+i) := by
        simpa only [add_mul,one_mul] using add_le_add (ih e.le) (price i e)
      _ ≤ factor*wage S r (u+h) (u+(i+1)) := by
        rw [step S r (u+h) (u+i),←mul_assoc]
        exact mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left rate (by linarith [factor_pos])).trans renew) (pos (i+1))

end YM.Integration.WilsonOriginalPublicTrialPhaseArrears
end
