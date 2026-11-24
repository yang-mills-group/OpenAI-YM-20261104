import YM.Integration.WilsonThermometerCenteredAlgebra

/-! The physical ordinary pair and its separate counterterm as a unary submission. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredPairContrast
open Finset Marker QuadraticLocal Extra.Trajectories WilsonThermometerCenteredAlgebra
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

def face (c:Fin 3):(J).Mode:=complement ((J).fire c)
def withdrawal (c:Fin 3):Poly J:=Poly.send ((J).fire c) 1-Poly.send (face c) 1

private theorem extract (F:Poly J) (t:(J).Mode) :
    (F*Poly.send t 1).part full=F.part (complement t):=by
  classical
  have meets : ∀ i j:(J).Mode,Poly.merges i j full ↔ j=complement i:=by decide
  have swap : ∀ s u:(J).Mode,complement s=u ↔ s=complement u:=by decide
  rw [Poly.part_mul]
  simp only [meets,sum_ite_eq',mem_univ,if_true,Poly.part_send,mul_ite,mul_one,mul_zero,swap,
    sum_ite_eq']

theorem ordinary (F:Poly J) (c:Fin 3) :
    (F*withdrawal c).part full=F.part (face c)-F.part ((J).fire c):=by
  have inv:∀s:(J).Mode,complement (complement s)=s:=by decide
  rw [withdrawal,mul_sub,part_sub,extract,extract,face,inv]
end YM.Integration.WilsonRegisteredPairContrast
