import YM.Integration.WilsonMeasuredCompanionEntry
import YM.Integration.WilsonMeasuredCompanionFace

/-! The complete selected slot is refunded once. The remaining wage factors belong to the actual peers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredCompanionWage
open Finset Marker QuadraticLocal WilsonMeasuredCompanionFace
open scoped BigOperators Classical
variable {V:Type}[DecidableEq V]{J:Census V}

def elected (v:V)(w:V→ℝ)(M δ:ℝ):V→ℝ:=wage v w (2*(M+δ))⁻¹

def companions (v:V)(w:V→ℝ)(s:J.Mode):ℝ:=∏j∈s.val.erase v,w j

theorem admitted (v:V)(w:V→ℝ)(wp:∀j,0<w j){M δ:ℝ}(M0:0≤M)(δ0:0<δ):
    (∀j,0<elected v w M δ j) ∧ elected v w M δ v*M≤1/2:=by
  have pos:0<2*(M+δ):=by positivity
  refine ⟨fun j=>?_,?_⟩
  · by_cases h:j=v
    · rw [h,show elected v w M δ v=(2*(M+δ))⁻¹ by simp [elected,wage]]
      exact inv_pos.mpr pos
    · simpa [elected,wage,h] using wp j
  · rw [show elected v w M δ v=(2*(M+δ))⁻¹ by simp [elected,wage]]
    rw [←div_eq_inv_mul]
    apply (div_le_iff₀ pos).2
    linarith

theorem restored (v:V)(w:V→ℝ)(wp:∀j,0<w j)(s:J.Mode)(inside:v∈s.val)
    {M δ F:ℝ}(M0:0≤M)(δ0:0<δ)(F0:0<F):
    let W:=elected v w M δ
    W v/Poly.toll W s=1/companions v w s ∧
    1/Poly.toll (Stoop.radius W F) s=F^s.val.card*(2*(M+δ))/companions v w s:=by
  let W:=elected v w M δ
  have val:W v=(2*(M+δ))⁻¹:=by simp [W,elected,wage]
  have pos:0<2*(M+δ):=by positivity
  have cp:0<companions v w s:=Finset.prod_pos fun j _=>wp j
  have total:Poly.toll W s=companions v w s*(2*(M+δ))⁻¹:=by
    rw [Poly.toll,← Finset.prod_erase_mul s.val W inside,val]
    congr 1
    exact Finset.prod_congr rfl fun j hj=>by simp [W,elected,wage,(Finset.mem_erase.mp hj).1]
  have scaled:Poly.toll (Stoop.radius W F) s=Poly.toll W s/F^s.val.card:=by
    simp [Poly.toll,Stoop.radius,Finset.prod_div_distrib]
  change W v/_=_ ∧ _=_
  rw [val,scaled,total]
  constructor <;> field_simp

end YM.Integration.WilsonMeasuredCompanionWage
end
