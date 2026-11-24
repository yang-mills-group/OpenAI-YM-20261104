import YM.Integration.WilsonVacuumPreResetMarkedNodalPrice
import YM.Integration.WilsonVacuumPreResetFiniteHeatCourse
import YM.Integration.WilsonVacuumPreResetMarkedTensorSlope

/-! On the original financial course the full finite-period mixed tensor
has one polynomial bill before either regulator, including its kinetic reset. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMarkedNodalCourse
open Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonVacuumPreResetFiniteHeatIntake WilsonVacuumPreResetFiniteHeatWindow
open WilsonVacuumPreResetMarkedProducts WilsonVacuumPreResetMarkedOrdinaryBound
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open scoped Classical BigOperators
variable {ι:Type}[DecidableEq ι]

theorem original (G:Gauge)(D:ι→ℕ)(I:Finset ι)(k:ι→ℕ)(e i r:ℕ)(hi:i≤e):
    ∃v:Gear G→ℝ,∃M:ℝ,0≤M ∧ ∃d:ℕ,∀Q:Realm G (e+1) Credit.leanC,
    ∀m (hm:Q.anchor ≤ m),v (Q.mint m hm).gear≤Q.cash Credit.leanC m → ∀N (live:m < N) n,
    let p:=cloVent Q m N n hm live 1 zero_lt_one
    let f:=p.n*(holt Q m hm 1 zero_lt_one).P.L
    ∀V:PChart G f,(∀j≤e,∀s≤horizon e (r+2*mass k I),∀y,|V j s y|≤1) →
    ∀t:ℝ,|t|≤1 →∀(K:family G D)(a:ι→ℝ),(∀j,0<a j)→
    (∀J⊆I,J.Nonempty→Bounded e (horizon e (r+2*mass k I)) ((K J).1 f) (weights a J))→
    ∀x,‖mist p.wheel p.shadow p.H (p.T p.n) Q.paid (p.W'+t•V) K
      (ratioHigh Q.draws Q.paid N m) k I i r x‖≤M*(gross (Q.y m) f)^d*weights a I:=by
  let l:=mass k I
  let E:=WilsonVacuumPreResetMarkedNodalPrice.power e l r I.card
  obtain ⟨w,b,store⟩:=WilsonMarkedIndependentEnrolledHeatWallet.original G e (r+2*l)
  obtain ⟨v,c,reset⟩:=WilsonVacuumPreResetFiniteHeatCourse.reversion G e i r hi
  obtain ⟨M,Mpos,selected⟩:=WilsonVacuumPreResetMarkedNodalPrice.selected G D I k e r
  refine ⟨fun u=>max (w u) (v u),M,Mpos,c+b*E,?_⟩
  intro Q m hm bought N live n p f V small t unit K a hot word x
  obtain ⟨A,apos,old,raw⟩:=store Q m hm ((le_max_left ..).trans bought) N live n
  have coin:=reset Q m hm ((le_max_right ..).trans bought) N live
  have yp:0≤Q.y m:=zero_le_one.trans (Q.depth m hm)
  let z:=gross (Q.y m) f
  have yz:Q.y m≤z:=le_mul_of_one_le_right yp (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg f.val)))
  have weighted:0≤weights a I:=positive a (fun j=>(hot j).le) I
  have α:=selected _ p A apos old V small t unit K a hot word (ratioHigh Q.draws Q.paid N m) i hi x
  have cash:fee p A (r+2*l)≤z^b:=raw
  have feePos:0≤fee p A (r+2*l):=by
    have cmp:=(inputs p A (r+2*l) apos old V small t unit).1
    linarith
  have change:rimJ (ratioHigh Q.draws Q.paid N m) i r≤z^c:=coin.trans (pow_le_pow_left₀ yp yz _)
  apply α.trans
  change _≤M*z^(c+b*E)*weights a I
  have exp: (fee p A (r+2*l))^E≤(z^b)^E:=pow_le_pow_left₀ feePos cash _
  calc
    _≤z^c*(M*(z^b)^E*weights a I):=mul_le_mul change
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left exp Mpos) weighted)
      (mul_nonneg (mul_nonneg Mpos (pow_nonneg feePos _)) weighted) (pow_nonneg (yp.trans yz) _)
    _=M*z^(c+b*E)*weights a I:=by rw [pow_add,pow_mul];ring

end YM.Integration.WilsonVacuumPreResetMarkedNodalCourse
end
