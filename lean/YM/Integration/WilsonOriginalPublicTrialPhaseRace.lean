import YM.Integration.WilsonOriginalPublicTrialPhaseAccumulated

/-! Engineering and a finite trajectory with its actual parent assigned at every date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseRace
open Lattice Wilson Source Labels Extra.Histories
open scoped BigOperators
variable (S:Schedule)

def wage (r:ℝ)(c i:ℕ):ℝ:=(S.a c/S.a i)^(2/5:ℝ)*r

theorem terminal (r:ℝ)(c:ℕ):wage S r c c=r:=by
  simp [wage,ne_of_gt (S.a_pos _)]

theorem step (r:ℝ)(c i:ℕ):
    wage S r c i=Doors.rate (S.block i)*wage S r c (i+1):=by
  have g:0<((S.block i).val:ℝ):=by exact_mod_cast (S.block i).property
  have h:(S.a c/S.a (i+1))=((S.block i).val:ℝ)*(S.a c/S.a i):=by
    rw [S.a_step]
    field_simp
  have e:(((S.block i).val:ℝ)^(-(2/5:ℝ)))*(((S.block i).val:ℝ)^(2/5:ℝ))=1:=by
    rw [← Real.rpow_add g,neg_add_cancel,Real.rpow_zero]
  rw [wage,wage,Doors.rate,h,Real.mul_rpow g.le (div_nonneg (S.a_pos _).le (S.a_pos _).le)]
  calc (S.a c / S.a i) ^ (2 / 5 : ℝ) * r
        = 1*((S.a c / S.a i) ^ (2 / 5 : ℝ) * r) := (one_mul _).symm
      _ = _ := by rw [← e]; ring

def back {T:ℕ→Type*}(n:ℕ)(top:T n)(next:∀i,i<n→T (i+1)→T i)(i:ℕ)(hi:i≤n):T i:=
  if h:i=n then h.symm ▸ top else next i (lt_of_le_of_ne hi h)
    (back n top next (i+1) (by omega))
termination_by n-i
decreasing_by omega

theorem back_head {T:ℕ→Type*}(n:ℕ)(top:T n)(next:∀i,i<n→T (i+1)→T i):
    back n top next n le_rfl=top:=by
  rw [back]
  simp

theorem back_step {T:ℕ→Type*}(n:ℕ)(top:T n)(next:∀i,i<n→T (i+1)→T i)(i:ℕ)(hi:i<n):
    back n top next i hi.le=next i hi (back n top next (i+1) hi):=by
  rw [back]
  simp [hi.ne]

end YM.Integration.WilsonOriginalPublicTrialPhaseRace
end
