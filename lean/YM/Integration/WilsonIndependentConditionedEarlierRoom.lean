import YM.Integration.WilsonIndependentConditionedEarlierCredit
import YM.Integration.WilsonIndependentConditionedProfileCredit

/-! One scalar budget for the optical report, its earlier measuring home and both genuine profiles. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedEarlierRoom
open Filter Real Function Lattice Wilson RG RG.Supply Precision PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer
open WilsonIndependentConditionedBankFittedFees (age)
open WilsonIndependentConditionedActualCredit (badge gramAge homes)
open WilsonIndependentConditionedEarlierCredit (drift)
open WilsonIndependentConditionedProfileCredit (Paid)
open WilsonInvariantActionPosition (berth)
open scoped Topology Classical BigOperators
variable {G:Gauge}{R:Run G}{T U:ℕ}
local notation "J" => Fin 2

structure Room (R:Run G)(T U:ℕ) where
  f : ℕ
  m : ℕ
  t : ℝ
  z : ℝ
  B : J→ℝ
  one : 1 ≤ badge R f
  home : |age R m m|≤(drift R T U).buy (badge R f)
  field : |age R m (berth R T f)|≤(drift R T U).buy (badge R f)
  gram : |gramAge R m (berth R T f)|≤(drift R T U).buy (badge R f)

namespace Room
variable (X:Room R T U)
def K:=berth R T X.f

def amount (badge t z:ℝ)(B:J→ℝ):ℝ:=1+badge+|t⁻¹|+|z|+|B 0|+|B 1|

def bill:=amount (badge R X.f) X.t X.z X.B

theorem bound:badge R X.f≤X.bill ∧ |X.t⁻¹|≤X.bill ∧ |X.z|≤X.bill ∧ ∀s:J,|X.B s|≤X.bill:=by
  unfold bill amount
  have f:=X.one
  have t:=abs_nonneg X.t⁻¹
  have z:=abs_nonneg X.z
  have l:=abs_nonneg (X.B 0)
  have r:=abs_nonneg (X.B 1)
  refine ⟨by linarith,by linarith,by linarith,?_⟩
  intro s
  fin_cases s
  · change |X.B 0| ≤ _
    linarith
  · change |X.B 1| ≤ _
    linarith

theorem cap:1≤X.bill:=X.one.trans X.bound.1

theorem ages (R:Run G)(T U:ℕ)(P:Credit):
    Paid (Room.bill (R:=R) (T:=T) (U:=U)) (fun X=>P.buy (age R X.m X.m)) ∧
    Paid Room.bill (fun X:Room R T U=>P.buy (age R X.m X.K)) ∧
    Paid Room.bill (fun X:Room R T U=>P.buy (gramAge R X.m X.K)):=by
  have receive (h:Room R T U→ℝ)
      (s:∀X,|h X|≤(drift R T U).buy (badge R X.f)):Paid Room.bill (fun X=>P.buy (h X)):=by
    apply Paid.book _ P
    exact ⟨drift R T U,fun X _=>(s X).trans ((drift R T U).elder X.one X.bound.1)⟩
  exact ⟨receive _ Room.home,receive _ Room.field,receive _ Room.gram⟩

theorem shapes:
    Paid (Room.bill (R:=R) (T:=T) (U:=U)) (fun X=>X.t⁻¹) ∧
    Paid Room.bill (fun X:Room R T U=>X.z) ∧ ∀s:J,Paid Room.bill (fun X:Room R T U=>X.B s):=
  ⟨Paid.direct (fun X=>X.bound.2.1),Paid.direct (fun X=>X.bound.2.2.1),
   fun s=>Paid.direct (fun X=>X.bound.2.2.2 s)⟩
end Room
end YM.Integration.WilsonIndependentConditionedEarlierRoom
