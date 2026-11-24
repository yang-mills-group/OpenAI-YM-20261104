import YM.Integration.WilsonOriginalPublicNodalTestedMarket
import YM.Integration.WilsonOlderFreshSoftSocketRemainder

/-! The valence of the original measured group supplies its power at the real stopping coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalTestedRelease
open PowerSeries Laurent Bloch Precision Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open XSpace XSpace.Rose RegulatorIR RegulatorIR.Cluster PhysicalNext.Repeat.Legato
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonOlderFreshSoftSocketKinetic (kinetic)
open WilsonReportingAbsoluteInletForecastBooks (value)
open WilsonOriginalPublicNodalTestedChronology (rank)
open private accounts from YM.Integration.WilsonOriginalPublicNodalTestedChronology
open scoped Classical BigOperators

variable {G:Gauge}
local instance all {I:Type}[Fintype I][Nonempty I]:Nonempty (Finset.univ:Finset I):=Finset.univ_nonempty.to_subtype

theorem scaled (P:Cost)(a x:ℝ)(q:ℕ):value q (C a*P) x=a*value q P x:=by
  unfold value
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  rw [coeff_C_mul]
  ring

theorem crop (q h:ℕ)(P:Cost)(x:ℝ):
    value q (PowerSeries.X^h*P) x=if h≤q then x^h*value (q-h) P x else 0:=by
  split_ifs with seen
  · obtain ⟨t,rfl⟩:=Nat.exists_eq_add_of_le seen
    simpa using WilsonOlderFreshSoftSocketRemainder.shift h t P x
  · unfold value
    apply sum_eq_zero
    intro i hi
    have lo:i<h:=by have:=mem_range.mp hi; omega
    simp only [coeff_X_pow_mul',if_neg (Nat.not_le.mpr lo),mul_zero]

theorem motion (A:Levels G)(O:ChartRatio G)(N b m:ℕ)(mb:m≤b)(x y:Cost):
    clock A O N b m (x*y)=clock A O N b m x*clock A O N b m y:=by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le mb
  simp only [WilsonIndependentFittedRelativeClock.reported,map_mul]

theorem scalar (A:Levels G)(O:ChartRatio G)(N b m:ℕ)(mb:m≤b)(u:ℝ):
    clock A O N b m (C u)=C u:=by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le mb
  rw [WilsonIndependentFittedRelativeClock.reported,reel_C]

theorem held (A:Levels G)(O:ChartRatio G)(N K j v:ℕ)(vj:v≤j)(jK:j≤K)
    (P:Era G ℝ)(u:ℝ)(q h:ℕ)(θ:ℝ):
    let stake:=C u*(PowerSeries.X:Cost)^h
    let issued:=affiled (clock A O N K j stake) P
    let bank:=(kinetic A O N K v)^h*clock A O N j v (ground P)
    value q (clock A O N j v (ground issued)) θ=
      if h≤q then u*θ^h*value (q-h) bank θ else 0:=by
  dsimp only
  have enter (k:Cost):ground (affiled k P)=k*ground P:=
    WilsonOlderFreshSoftSocketKinetic.valued P.2 k Fin.elim0
  rw [enter,motion A O N j v vj,WilsonOlderFreshSoftSocketKinetic.combine A O N K j v vj jK,
    motion A O N K v (vj.trans jK),scalar A O N K v (vj.trans jK),
    WilsonOlderFreshSoftSocketKinetic.pole A O N K v h (vj.trans jK)]
  let M:=clock A O N j v (ground P)
  let k:=kinetic A O N K v
  change value q (C u*(PowerSeries.X^h*k^h)*M) θ=_
  rw [show C u*(PowerSeries.X^h*k^h)*M=C u*(PowerSeries.X^h*(k^h*M)) by ring,scaled,crop]
  split_ifs <;> ring

theorem registered {I:Type}[Fintype I][LinearOrder I][Nonempty I](R:Run G)(d:I→ℕ)
    (b:∀i,(R.family.labels.level (d i)).Index):
    rank R d b (Finset.univ:Finset I)=∑i,((R.family.labels.level (d i)).grades (b i)).2:=by
  let e:(Finset.univ:Finset I)≃I:=⟨Subtype.val,fun i=>⟨i,mem_univ _⟩,fun _=>rfl,fun _=>rfl⟩
  rw [rank,accounts]
  apply Fintype.sum_equiv e
  intro i
  rfl

theorem amount {I:Type}[Fintype I][LinearOrder I][Nonempty I](R:Run G)(d:I→ℕ)
    (b:∀i,(R.family.labels.level (d i)).Index)(x:∀i,(R.family.labels.level (d i)).Coeff)(g θ:ℝ):
    let h:=rank R d b (Finset.univ:Finset I)
    WilsonOriginalPublicTrialFigure.weight R d g x b*((θ^h:ℝ):ℂ)=
      (∏i,x i (b i))*(((θ/g)^h:ℝ):ℂ):=by
  dsimp only
  rw [registered]
  simp only [WilsonOriginalPublicTrialFigure.weight,WilsonOriginalPublicTrialFigure.amount,
    Complex.ofReal_inv,Complex.ofReal_pow,prod_mul_distrib,prod_inv_distrib,prod_pow_eq_pow_sum,div_eq_mul_inv,Complex.ofReal_mul,mul_pow]
  ring

end YM.Integration.WilsonOriginalPublicNodalTestedRelease
end
