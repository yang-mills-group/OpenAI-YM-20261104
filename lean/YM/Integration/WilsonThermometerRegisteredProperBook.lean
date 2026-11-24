import YM.Integration.WilsonThermometerRegisteredFaceTable

/-! Withdraw an arbitrary proper face of the whole ordinary ratio, preserving the
original fixed inverse wallet and retaining every lower product. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredProperBook
open Finset Marker QuadraticLocal Extra.Trajectories Comparison.RG02 Comparison.RG02.Order
open Primitives.GCC.Anchor WilsonThermometerCenteredAlgebra WilsonFiniteOrdinaryInverse
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
local notation "half" => ((2:ℂ)⁻¹)

def extra (s:(J).Mode) (Q:Poly J):Poly J:=Poly.send s half*inverseMass Q
def paper (s:(J).Mode) (Q:Poly J):Poly J:=1-extra s Q

open private nil from YM.Integration.WilsonThermometerRegisteredFaceTable

theorem inverse (s:(J).Mode) (live:s≠(J).quiet) (Q:Poly J):
    inverseMass (paper s Q)=1+extra s Q:=by
  let X:=extra s Q
  have zero:X*X=0:=by
    calc
      _=(Poly.send s half*Poly.send s half)*(inverseMass Q*inverseMass Q):=by unfold X extra;ring
      _=0:=by rw [nil s live,zero_mul]
  have mul:(1+X)*(1-X)=1:=by calc
    _=1-X*X:=by ring
    _=1:=by rw [zero,sub_zero]
  have unit:(paper s Q).part (J).quiet=1:=by
    change (1:Poly J).part (J).quiet-(Poly.send s half*inverseMass Q).part (J).quiet=1
    rw [Poly.quiet_mul,Poly.part_send,if_neg (Ne.symm live),zero_mul,sub_zero];rfl
  calc
    _=((1+X)*(1-X))*inverseMass (paper s Q):=by rw [mul,one_mul]
    _=(1+X)*((paper s Q)*inverseMass (paper s Q)):=mul_assoc ..
    _=_:=by rw [right_inverse unit,mul_one]

theorem ordinary (F Q:Poly J) (t:(J).Mode) (live:t≠(J).quiet):
    (total F (paper t Q)).part full-(total F 1).part full=half*(total F Q).part (complement t):=by
  have invoice:=WilsonThermometerRegisteredFaceTable.ordinary (total F Q) t live half
  have same:total F (paper t Q)-total F 1=
      total (total F Q) (WilsonThermometerRegisteredFaceTable.table t half)-total (total F Q) 1:=by
    simp only [total,inverse t live,WilsonThermometerRegisteredFaceTable.inverse t live,WilsonThermometerRegisteredFaceTable.unit,
      mul_one,extra];ring
  exact (congrArg (fun a:Poly J=>a.part full) same).trans invoice

theorem fixed (w:Fin 3→ℝ) (positive:∀v,0<w v) (capped:∀v,w v≤1) (t:(J).Mode) (live:t≠(J).quiet)
    (Q:Poly J) (bought:Poly.price w (inverseMass Q)≤fee J):
    Poly.price w (inverseMass (1:Poly J))≤fee J ∧ Poly.price w (inverseMass (paper t Q))≤fee J:=by
  have room:=WilsonThermometerRegisteredFaceTable.room_two
  have toll:Poly.toll w t≤1:=Finset.prod_le_one (fun v _=>(positive v).le) (fun v _=>capped v)
  have slot:Poly.price w (Poly.send t half)≤(2:ℝ)⁻¹:=by
    rw [Poly.solo,norm_inv];norm_num
    linarith
  have tagged:Poly.price w (extra t Q)≤(2:ℝ)⁻¹*fee J:=
    (Poly.multiplication positive _ _).trans (mul_le_mul slot bought (Poly.nonnegative positive _) (by norm_num))
  rw [WilsonThermometerRegisteredFaceTable.unit,inverse t live,Poly.one_price]
  refine ⟨by linarith,?_⟩
  have cap:=Poly.addition positive (1:Poly J) (extra t Q)
  rw [Poly.one_price] at cap
  linarith

end YM.Integration.WilsonThermometerRegisteredProperBook
