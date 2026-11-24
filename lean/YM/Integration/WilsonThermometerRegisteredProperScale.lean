import YM.Integration.WilsonThermometerRegisteredProperBook

/-! A proper ordinary face can be withdrawn at every positive original wallet.
Its restoration fee uses exactly the toll of the missing names. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredProperScale
open Finset Marker QuadraticLocal Extra.Trajectories Comparison.RG02 Comparison.RG02.Order
open Primitives.GCC.Anchor WilsonThermometerCenteredAlgebra WilsonFiniteOrdinaryInverse
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
variable (w:Fin 3→ℝ) (t:(J).Mode)

def restoration :ℝ:=2*(1+Poly.toll w t)
def extra (Q:Poly J):Poly J:=Poly.send t (((restoration w t)⁻¹:ℝ):ℂ)*inverseMass Q
def tested (Q:Poly J):Poly J:=1-extra w t Q

open private nil from YM.Integration.WilsonThermometerRegisteredFaceTable

theorem inverse (live:t≠(J).quiet) (Q:Poly J):
    inverseMass (tested w t Q)=1+extra w t Q:=by
  let X:=extra w t Q
  let a:=(((restoration w t)⁻¹:ℝ):ℂ)
  have zero:X*X=0:=by
    calc
      _=(Poly.send t a*Poly.send t a)*(inverseMass Q*inverseMass Q):=by unfold X extra a;ring
      _=0:=by rw [nil t live,zero_mul]
  have mul:(1+X)*(1-X)=1:=by calc
    _=1-X*X:=by ring
    _=1:=by rw [zero,sub_zero]
  have unit:(tested w t Q).part (J).quiet=1:=by
    change (1:Poly J).part (J).quiet-(Poly.send t a*inverseMass Q).part (J).quiet=1
    rw [Poly.quiet_mul,Poly.part_send,if_neg (Ne.symm live),zero_mul,sub_zero];rfl
  calc
    _=((1+X)*(1-X))*inverseMass (tested w t Q):=by rw [mul,one_mul]
    _=(1+X)*((tested w t Q)*inverseMass (tested w t Q)):=mul_assoc ..
    _=_:=by rw [right_inverse unit,mul_one]

theorem positive (prices:∀v,0<w v):0<restoration w t:=by
  have pos:0<Poly.toll w t:=Finset.prod_pos (fun v _=>prices v)
  unfold restoration;linarith

theorem ordinary (prices:∀v,0<w v) (F Q:Poly J) (live:t≠(J).quiet):
    (total F Q).part (complement t)=(restoration w t:ℂ)*
      ((total F (tested w t Q)).part full-(total F 1).part full):=by
  let a:=(((restoration w t)⁻¹:ℝ):ℂ)
  have invoice:=WilsonThermometerRegisteredFaceTable.ordinary (total F Q) t live a
  have same:total F (tested w t Q)-total F 1=
      total (total F Q) (WilsonThermometerRegisteredFaceTable.table t a)-total (total F Q) 1:=by
    simp only [total,inverse w t live,WilsonThermometerRegisteredFaceTable.inverse t live,WilsonThermometerRegisteredFaceTable.unit,
      mul_one,extra,a];ring
  have eq: (total F (tested w t Q)).part full-(total F 1).part full=a*(total F Q).part (complement t):=
    (congrArg (fun x:Poly J=>x.part full) same).trans invoice
  rw [eq,←mul_assoc]
  have nz:((restoration w t:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (positive w t prices).ne'
  simp [a,nz]

theorem fixed (prices:∀v,0<w v) (live:t≠(J).quiet) (Q:Poly J) (income:Poly.price w (inverseMass Q)≤fee J):
    Poly.price w (inverseMass (1:Poly J))≤fee J ∧ Poly.price w (inverseMass (tested w t Q))≤fee J:=by
  have positive₀:=positive w t prices
  have room:=WilsonThermometerRegisteredFaceTable.room_two
  have slot:Poly.price w (Poly.send t (((restoration w t)⁻¹:ℝ):ℂ))≤(2:ℝ)⁻¹:=by
    rw [Poly.solo,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr positive₀),←div_eq_mul_inv,div_le_iff₀ positive₀]
    unfold restoration;linarith
  have tagged:Poly.price w (extra w t Q)≤(2:ℝ)⁻¹*fee J:=
    (Poly.multiplication prices _ _).trans (mul_le_mul slot income (Poly.nonnegative prices _) (by norm_num))
  rw [WilsonThermometerRegisteredFaceTable.unit,inverse w t live,Poly.one_price]
  refine ⟨by linarith,?_⟩
  have add:=Poly.addition prices (1:Poly J) (extra w t Q)
  rw [Poly.one_price] at add
  linarith

end YM.Integration.WilsonThermometerRegisteredProperScale
