import YM.Integration.WilsonThermometerRegisteredCenteredSelfBound

/-! A single pair of inverse tables reads the true compact connected polynomial at all
finite positions and on every admitted receiving pupil. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredFixedInvoice
open Finset Marker Extra.Trajectories Primitives.GCC.Anchor Comparison.RG02 WilsonFiniteOrdinaryInverse
open WilsonThermometerCenteredAlgebra WilsonThermometerCenteredScalar WilsonThermometerRegisteredCenteredInvoice
open scoped BigOperators Classical
local notation "J" => Stock.census (Fin 3)

def credit (F:Poly J):Poly J:=(12⁻¹:ℂ) • (properInvoice F 1-1)
def tested (F:Poly J):Poly J:=inverseMass (1+credit F)

open private proper_unit from YM.Integration.WilsonThermometerRegisteredCenteredInvoice

theorem paid (F:Poly J):inverseMass (tested F)=1+credit F:=by
  apply WilsonThermometerRegisteredSingletonCenter.twice
  have blank:(1:Poly J).part (J).quiet=1:=by rw [Poly.one_part,if_pos rfl]
  change (1:Poly J).part (J).quiet+(credit F).part (J).quiet=1
  rw [credit,Poly.part_smul]
  change _+_ * ((properInvoice F 1).part (J).quiet-(1:Poly J).part (J).quiet)=1
  rw [proper_unit F 1 blank,blank,sub_self,mul_zero,add_zero]

theorem affordable (F:Poly J) (w:Fin 3→ℝ) (pos:∀v,0<w v) (cap:∀v,w v≤1) (means:∀v:Fin 3,‖read F {v}‖≤1):
    Poly.price w (inverseMass (1:Poly J))≤fee J ∧ Poly.price w (inverseMass (tested F))≤fee J:=by
  have d:restoration w F 1≤12:=by
    apply (WilsonThermometerRegisteredCenteredSelfWeight.price w pos F (S:=1) _).trans_eq (by norm_num)
    intro v;exact (mul_le_mul_of_nonneg_right (cap v) (norm_nonneg _)).trans (by simpa only [one_mul] using means v)
  have quiet:=WilsonThermometerRegisteredFaceTable.room_two
  have short:Poly.price w (properInvoice F 1-1)≤5:=by unfold restoration at d;linarith
  have dose:Poly.price w (credit F)≤5/12:=by
    rw [credit,Poly.adapted,norm_inv,show ‖(12:ℂ)‖=(12:ℝ) by norm_num]
    linarith
  have budget:=Poly.addition pos (1:Poly J) (credit F)
  rw [Poly.one_price] at budget
  rw [WilsonThermometerRegisteredFaceTable.unit,Poly.one_price,paid]
  exact ⟨by linarith,by linarith⟩

theorem reading (F X:Poly J):
    (X*properInvoice F 1).part full=12*(total X (tested F)).part full-11*(total X 1).part full:=by
  rw [total,total,paid,WilsonThermometerRegisteredFaceTable.unit,mul_one,mul_add,mul_one,credit,mul_smul_comm,
    mul_sub,mul_one,Poly.part_plus,Poly.part_smul]
  change _=12*(X.part full+12⁻¹*((X*properInvoice F 1).part full-X.part full))-11*X.part full
  ring

end YM.Integration.WilsonThermometerRegisteredCenteredFixedInvoice
