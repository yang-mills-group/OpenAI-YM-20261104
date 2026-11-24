import YM.Integration.WilsonThermometerRegisteredProperScale

/-! The exact signed response to an independently nominated ordinary table uses only its inverse on the requested names. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredRestrictedWithdrawal
open Finset Marker QuadraticLocal Extra.Trajectories Comparison.RG02 Comparison.RG02.Order
open Primitives.GCC.Anchor WilsonThermometerCenteredAlgebra WilsonFiniteOrdinaryInverse
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
variable (w:Fin 3→ℝ) (t:(J).Mode)


def selected (t:(J).Mode) (F:Poly J):Poly J:=Poly.inject fun s=>
  if Disjoint t.val s.val then F.part s else 0

def head (Q:Poly J):Poly J:=Poly.send t 1*inverseMass Q
def restoration (Q:Poly J):ℝ:=2*(1+Poly.price w (head t Q))
def extra (Q:Poly J):Poly J:=Poly.send t (((restoration w t Q)⁻¹:ℝ):ℂ)*inverseMass Q
def tested (Q:Poly J):Poly J:=1-extra w t Q

theorem restricted (Q:Poly J):head t Q=Poly.send t 1*selected t (inverseMass Q):=by
  apply Marker.Poly.ext
  intro x
  rw [head,Poly.part_mul,Poly.part_mul]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  by_cases same:b=t
  · subst b
    by_cases joined:Poly.merges t c x
    · simp only [if_pos joined];change _=_*(if Disjoint t.val c.val then _ else _)
      rw [if_pos joined.1]
    · rw [if_neg joined,if_neg joined]
  · simp [Poly.part_send,same]

theorem charge (prices:∀v,0<w v) (Q:Poly J):
    Poly.price w (head t Q)≤Poly.toll w t*
        (∑s:(J).Mode with Disjoint t.val s.val, Poly.toll w s*‖(inverseMass Q).part s‖):=by
  rw [restricted t Q]
  have rate:=Poly.multiplication prices (Poly.send t 1) (selected t (inverseMass Q))
  rw [Poly.solo,norm_one,mul_one] at rate
  apply rate.trans_eq
  congr 1
  unfold Poly.price
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  change Poly.toll w v * ‖(if Disjoint t.val v.val then _ else _)‖=_
  by_cases belongs:Disjoint t.val v.val
  · simp [belongs]
  · simp [belongs]

theorem positive (prices:∀v,0<w v) (Q:Poly J):0<restoration w t Q:=by
  have pos:=Poly.nonnegative prices (head t Q)
  unfold restoration;linarith

theorem scaled (Q:Poly J):extra w t Q=(((restoration w t Q)⁻¹:ℝ):ℂ) • head t Q:=by
  unfold head extra
  rw [←smul_mul_assoc]
  congr 1
  apply Marker.Poly.ext
  intro s
  simp [Poly.part_send,Poly.part_smul]

open private nil from YM.Integration.WilsonThermometerRegisteredFaceTable

theorem inverse (live:t≠(J).quiet) (Q:Poly J):
    inverseMass (tested w t Q)=1+extra w t Q:=by
  let X:=extra w t Q
  let a:=(((restoration w t Q)⁻¹:ℝ):ℂ)
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

theorem ordinary (prices:∀v,0<w v) (F Q:Poly J) (live:t≠(J).quiet):
    (total F Q).part (complement t)=(restoration w t Q:ℂ)*
      ((total F (tested w t Q)).part full-(total F 1).part full):=by
  let a:=(((restoration w t Q)⁻¹:ℝ):ℂ)
  have invoice:=WilsonThermometerRegisteredFaceTable.ordinary (total F Q) t live a
  have same:total F (tested w t Q)-total F 1=
      total (total F Q) (WilsonThermometerRegisteredFaceTable.table t a)-total (total F Q) 1:=by
    simp only [total,inverse w t live,WilsonThermometerRegisteredFaceTable.inverse t live,WilsonThermometerRegisteredFaceTable.unit,
      mul_one,extra,a];ring
  have eq: (total F (tested w t Q)).part full-(total F 1).part full=a*(total F Q).part (complement t):=
    (congrArg (fun x:Poly J=>x.part full) same).trans invoice
  rw [eq,←mul_assoc]
  have nz:((restoration w t Q:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (positive w t prices Q).ne'
  simp [a,nz]


theorem affordable (prices:∀v,0<w v) (live:t≠(J).quiet) (Q:Poly J):
    Poly.price w (inverseMass (1:Poly J))≤fee J ∧ Poly.price w (inverseMass (tested w t Q))≤fee J:=by
  have good:=positive w t prices Q
  have extraCost:Poly.price w (extra w t Q)≤(2:ℝ)⁻¹:=by
    rw [scaled,Poly.adapted,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr good),inv_mul_eq_div,
      div_le_iff₀ good]
    unfold restoration;linarith
  have charges:=Poly.addition prices (1:Poly J) (extra w t Q)
  rw [Poly.one_price] at charges
  have room:=WilsonThermometerRegisteredFaceTable.room_two
  rw [WilsonThermometerRegisteredFaceTable.unit,inverse w t live,Poly.one_price]
  exact ⟨by linarith,by linarith⟩

end YM.Integration.WilsonThermometerRegisteredRestrictedWithdrawal
