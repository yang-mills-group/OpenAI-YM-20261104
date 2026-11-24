import YM.Integration.WilsonThermometerRegisteredMeasuredIncome
import YM.Integration.WilsonThermometerRegisteredFaceTable

/-! A single compensated three-field ordinary reading for the connected difference. Only three independently measurable singleton means determine the extra test. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredSingletonCenter
open Finset Marker Extra.Trajectories Primitives.GCC.Anchor Comparison.RG02
open WilsonThermometerCenteredAlgebra WilsonThermometerCenteredScalar
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

def shift (F Q:Poly J) (v:Fin 3):ℂ:=read F {v}-read Q {v}

open private products from YM.Integration.WilsonThermometerCenteredScalar

private theorem singleton_product (F Q:Poly J) (v:Fin 3):
    read (F*Q) {v}=read F ∅*read Q {v}+read F {v}*read Q ∅:=by
  have listed:({v}:Finset (Fin 3)).powerset={∅,{v}}:=by fin_cases v <;> decide
  rw [products,listed]
  simp

theorem singleton (F Q:Poly J) (fu:F.part (J).quiet=1) (qu:Q.part (J).quiet=1) (v:Fin 3):
    read (total F Q) {v}=shift F Q v:=by
  have eq:=congrArg (fun U:Poly J=>read U {v}) (restore F Q qu)
  have left:read (total F Q) ∅=1:=normed F Q fu qu
  have right:read Q ∅=1:=qu
  rw [singleton_product,left,right,one_mul,mul_one] at eq
  unfold shift;linear_combination eq

def correction (e:Fin 3→ℂ):Poly J:=1-Poly.send (face {0}) (e 0)-Poly.send (face {1}) (e 1)-
  Poly.send (face {2}) (e 2)+Poly.send (face {1,2}) (2*e 1*e 2)

private theorem picked (P:Poly J) (s:(J).Mode) (live:s≠(J).quiet) (a:ℂ):
    (P*Poly.send s a).part full=a*P.part (complement s):=by
  have eq:=WilsonThermometerRegisteredFaceTable.ordinary P s live a
  simpa only [total,WilsonThermometerRegisteredFaceTable.inverse s live,WilsonThermometerRegisteredFaceTable.unit,
    mul_add,mul_one,Poly.part_plus,add_sub_cancel_left] using eq

theorem quiet (e:Fin 3→ℂ):(correction e).part (J).quiet=1:=by
  change (1:ℂ)-(Poly.send (face {0}) (e 0)).part (J).quiet-(Poly.send (face {1}) (e 1)).part (J).quiet-
    (Poly.send (face {2}) (e 2)).part (J).quiet+(Poly.send (face {1,2}) (2*e 1*e 2)).part (J).quiet=1
  simp only [Poly.part_send,if_neg (show (J).quiet≠face {0} by decide),if_neg (show (J).quiet≠face {1} by decide),
    if_neg (show (J).quiet≠face {2} by decide),if_neg (show (J).quiet≠face {1,2} by decide),sub_zero,add_zero]

theorem inverse_unit (T:Poly J) (unit:T.part (J).quiet=1):(inverseMass T).part (J).quiet=1:=by
  have hit:=congrArg (fun U:Poly J=>U.part (J).quiet) (right_inverse unit)
  simpa only [Poly.quiet_mul,unit,one_mul,Poly.one_part,if_pos rfl,if_true] using hit

theorem twice (T:Poly J) (unit:T.part (J).quiet=1):inverseMass (inverseMass T)=T:=by
  calc
    _=(T*inverseMass T)*inverseMass (inverseMass T):=by rw [right_inverse unit,one_mul]
    _=T:=by rw [mul_assoc,right_inverse (inverse_unit T unit),mul_one]

def invoice (F Q:Poly J):Poly J:=inverseMass Q*correction (shift F Q)
def submitted (F Q:Poly J):Poly J:=inverseMass (invoice F Q)

theorem invoice_unit (F Q:Poly J) (qu:Q.part (J).quiet=1):(invoice F Q).part (J).quiet=1:=by
  rw [invoice,Poly.quiet_mul,inverse_unit Q qu,quiet,one_mul]

theorem restored (F Q:Poly J) (qu:Q.part (J).quiet=1):inverseMass (submitted F Q)=invoice F Q:=
  twice _ (invoice_unit F Q qu)

theorem cell (F Q:Poly J) (fu:F.part (J).quiet=1) (qu:Q.part (J).quiet=1):
    read (Extra.Trajectories.connected F) univ-read (Extra.Trajectories.connected Q) univ=
      (total F (submitted F Q)).part full:=by
  let P:=total F Q
  let e:=shift F Q
  have expanded:P*correction e=P-P*Poly.send (face {0}) (e 0)-P*Poly.send (face {1}) (e 1)-
      P*Poly.send (face {2}) (e 2)+P*Poly.send (face {1,2}) (2*e 1*e 2):=by unfold correction;ring
  have returned:total F (submitted F Q)=P*correction e:=by rw [total,restored F Q qu,invoice,←mul_assoc];rfl
  rw [WilsonThermometerFiniteConnectedRemainder.cell F Q fu qu,returned,expanded]
  change read P univ-(read P {0,1}*read P {2}+read P {0,2}*read P {1}+read P {1,2}*read P {0})+
       2*(read P {0}*read P {1}*read P {2})=
    read P univ-(P*Poly.send (face {0}) (e 0)).part full-(P*Poly.send (face {1}) (e 1)).part full-
       (P*Poly.send (face {2}) (e 2)).part full+(P*Poly.send (face {1,2}) (2*e 1*e 2)).part full
  rw [picked P (face {0}) (by decide), picked P (face {1}) (by decide), picked P (face {2}) (by decide),
    picked P (face {1,2}) (by decide)]
  rw [show complement (face {0})=face {1,2} by decide,show complement (face {1})=face {0,2} by decide,
    show complement (face {2})=face {0,1} by decide, show complement (face {1,2})=face {0} by decide]
  change read P univ-(read P {0,1}*read P {2}+read P {0,2}*read P {1}+read P {1,2}*read P {0})+
       2*(read P {0}*read P {1}*read P {2})=read P univ-e 0*read P {1,2}-e 1*read P {0,2}-
       e 2*read P {0,1}+2*e 1*e 2*read P {0}
  have h (v:Fin 3):read P {v}=e v:=singleton F Q fu qu v
  rw [h 0,h 1,h 2];ring

end YM.Integration.WilsonThermometerRegisteredSingletonCenter
