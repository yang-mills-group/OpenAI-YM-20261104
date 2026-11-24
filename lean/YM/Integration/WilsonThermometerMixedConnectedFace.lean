import YM.Integration.WilsonThermometerMixedWeightedTap
import YM.Integration.WilsonThermometerCenteredRose

/- Once the singleton moments on the original older law are fixed, the connected
   change is a linear hearing of its complete and three paired ordinary moments. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedConnectedFace
open Finset Marker QuadraticLocal WilsonGeometricSignedCapture WilsonThermometerCenteredAlgebra
open WilsonThermometerCenteredScalar WilsonThermometerMixedAmplitude
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

def term (a:ℂ)(s:(J).Mode): (J).Mode→ℂ:=fun t=>if t=s then a else 0
def slate (a:Fin 3→ℂ): (J).Mode→ℂ:=
  term 1 full+term (-a 2) (face {0,1})+term (-a 1) (face {0,2})+term (-a 0) (face {1,2})

private theorem linear (a b:(J).Mode→ℂ)(F:Poly (J)):take (a+b) F=take a F+take b F:=by
  simp only [take,Pi.add_apply,add_mul,sum_add_distrib]

private theorem selected (a:ℂ)(s:(J).Mode)(F:Poly (J)): take (term a s) F=a*F.part s:=by
  classical
  simp [take,term,ite_mul]

theorem heard (a:Fin 3→ℂ)(F:Poly (J)):take (slate a) F=read F univ-
    (read F {0,1}*a 2+read F {0,2}*a 1+read F {1,2}*a 0):=by
  simp only [slate,linear,selected]
  change 1*F.part full+_+_+_=F.part full-(F.part _*a 2+F.part _*a 1+F.part _*a 0)
  ring

theorem preserved {q:ℂ}{A Y F:Poly (J)}(line:Line q A Y F)(i:Fin 3):read Y {i}=read A {i}:=by
  have zero:=line.marked (face {i}) (by simp [face])
  change (F.part (face {i})-A.part (face {i}))=0 at zero
  have eqn:=congrArg (fun p:Poly (J)=>p.part (face {i})) line.value
  change Y.part _=A.part _+q*(F.part _-A.part _) at eqn
  rw [zero,mul_zero,add_zero] at eqn
  exact eqn

theorem original (A Y:Poly (J))(a0:A.part (J).quiet=1)(y0:Y.part (J).quiet=1)
    (same:∀i:Fin 3,read Y {i}=read A {i}):
    (Extra.Trajectories.connected Y).part full-(Extra.Trajectories.connected A).part full=
    take (slate (fun i=>read Y {i})) Y-take (slate (fun i=>read Y {i})) A:=by
  rw [WilsonThermometerCenteredRose.named Y y0,WilsonThermometerCenteredRose.named A a0,heard,heard]
  simp only [WilsonPositionThermometerConnected.value,←same]
  ring

private theorem price_term (w:Fin 3→ℝ)(a:ℂ)(s:(J).Mode):
    weightBill (term a s) w=‖a‖/Poly.toll w s:=by
  classical
  simp [weightBill,term,apply_ite,ite_div]

private theorem price_add (w:Fin 3→ℝ)(wp:∀i,0<w i)(a b:(J).Mode→ℂ):
    weightBill (a+b) w≤weightBill a w+weightBill b w:=by
  unfold weightBill
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro j _
  rw [←add_div]
  exact div_le_div_of_nonneg_right (norm_add_le ..) (Poly.worth wp j).le

theorem price (w:Fin 3→ℝ)(wp:∀i,0<w i)(a:Fin 3→ℂ):weightBill (slate a) w ≤
    1/Poly.toll w full+‖a 2‖/Poly.toll w (face {0,1})+
      ‖a 1‖/Poly.toll w (face {0,2})+‖a 0‖/Poly.toll w (face {1,2}):=by
  let a₀:=term 1 full
  let a₁:=term (-a 2) (face {0,1})
  let a₂:=term (-a 1) (face {0,2})
  let a₃:=term (-a 0) (face {1,2})
  calc
    weightBill (slate a) w ≤ weightBill (a₀+a₁+a₂) w+weightBill a₃ w:=price_add w wp (a₀+a₁+a₂) a₃
    _ ≤ weightBill (a₀+a₁) w+weightBill a₂ w+weightBill a₃ w:=add_le_add (price_add w wp (a₀+a₁) a₂) le_rfl
    _ ≤ weightBill a₀ w+weightBill a₁ w+weightBill a₂ w+weightBill a₃ w:=
      add_le_add (add_le_add (price_add w wp a₀ a₁) le_rfl) le_rfl
    _ = _:=by simp only [a₀,a₁,a₂,a₃,price_term,norm_neg,norm_one]

end YM.Integration.WilsonThermometerMixedConnectedFace
end
