import YM.Integration.WilsonRootedNonflatReference

/-! All actual sectors and all source degrees at the same held field.
Normalization takes place after the complete columns have been added. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedNonflatLog
open Function Filter MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Matrix Pressure Pressure.Testing Pressure.Stores Next.SectorChange Next.SectorChange.Rows
open Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent.Affine
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open scoped Topology BigOperators Classical
variable {G:Gauge}{I:Type} [DecidableEq I] {Γ:Census I}(R:Run G)(d:LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => Pressure.Testing.ships R.alloy.B d.cutoff d.level d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "K" => d.kernel (RunFormalChain.fromRun R)
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "J₀" => R.metals.O
local notation "i₀" => R.alloy.B.a.clock.J d.level
local notation "i₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "w" => R.kit.walls i₁ i₀
local notation "b" => radiusW R.kit.rider i₁ i₀ * R.alloy.B.a.clock.threshold (d.level+1)
local notation "Coarse" => fieldDir G (R.family.side d.level d.period) 1

def sum (D:Allocation G Δ Θ w)(q:Chi)(V:Config G (R.family.side d.level d.period))
    (x:Coarse)(u:Config G (R.family.side (d.level+1) d.period)→ℂ):ℂ:=
  ∑ A:Stores Δ,∑ k:(Δ).Choices,WilsonRootedNonflatReference.full R d D q A k V x u

theorem measured (D:Allocation G Δ Θ w)(q:Chi)(V:Config G (R.family.side d.level d.period))(x:Coarse)
    (u:Config G (R.family.side (d.level+1) d.period)→ℂ)(hu:Envelope u)(inv:GaugeInvariant u):
    sum R d D q V x u=(Δ).push (P).beta u V:=by
  have h:=congrFun ((ManuscriptQLocalSector.bought R d D q).apply_push hu inv) V
  erw [h,Marked.paidSum,sum]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro k _
  exact (WilsonRootedNonflatReference.whole R d D q A k V x u hu).symm

variable [Fintype I] {J:Request I} {A:NumericSchedule R.family J}
    (F:AnalyticInput J A d)(test:TestSpace J.tests)
local notation "Π" => ManuscriptQLocalActualLog.source R d F test
local notation "W" => F.colors test
local notation "Y" => RunFormalChain.fromRun R

/-- Every degree of the full signed numerator is obtained with its one
true old density. The sector sum is prior to division by the quiet entry. -/
theorem source (D:Allocation G Δ Θ w)(q:Chi)(V:Config G (R.family.side d.level d.period))
    (x:Coarse)(s:Γ.Mode):
    sum R d D q V x (Actual.atMark s Π)=(Actual.Push Δ (P).beta Π V).part s:=by
  have paid:=ManuscriptQLocalActualLog.floor R d F test
  have inv:GaugeInvariant (Actual.atMark s Π):=fun k U=>
    congrArg (fun t:Poly Γ=>t.part s) (paid.gauges k U)
  rw [measured R d D q V x _ (paid.safe s) inv]
  exact (congrFun (Actual.grades (S:=Δ) Π V (P).beta) s).symm

/-- This is the original interacting logarithm and the exact remaining
source error, including the denominator column and the two singleton
modes separately. Evaluation is at the original nonconstant held field. -/
theorem original (D:Allocation G Δ Θ w)(q:Chi)(x:Coarse)(s:Γ.Mode):
    let V:=Integral.sample g x
    let d':LocalFormal.Datum R.family Γ:={d with colors:=W,field:=x}
    let Z:=fun _:(Δ).Choices=>Integral.zone K (P).p d.forest g x
    let error:=Local.markingError P Π K g d.forest d.tag W Z x J.order (Fintype.card I)
    sum R d D q V x (Actual.atMark s Π)=
      ((P₀).eval V:ℂ)*((Order.value (g:ℂ) (d'.markedLog Y J.order)+error).pass).part s:=by
  intro V d' Z error
  have h:=ManuscriptQLocalActualLog.conditional R d F test x
  rw [source R d F test D q V x s,h.2,Poly.part_smul,h.1]

end YM.Integration.WilsonRootedNonflatLog
