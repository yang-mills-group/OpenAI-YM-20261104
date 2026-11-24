import YM.Integration.WilsonOriginalClearedAngularRead
import YM.Integration.WilsonOriginalFoldedMarkedRightColumn

/-! The funded normalized primary source on the original full forest
curve. The arriving row is represented with its original group-word
salary and its designated pole-clearing power. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPrimerForestRead
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary
open Marker Next.SectorChange Multi Comparison.RG02 Comparison.RG02.Bulk AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Exterior Precision Tree Matrix
open PhysicalNext.Repeat.Legato AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic PowerSeries
open WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open PhysicalForestMarkedRay PhysicalForestRay
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(R:Run G)(N i p:ℕ)(hi:i<N)(F:Forest (step R i p).ratio)
local notation "n" => fine R i p
local notation "c" => coarse R i p
variable {V:Type}[DecidableEq V]{C:Marker.Census V}(Y:Bulk.Colors C G (fine R i p))(J:Hot C)
variable (w:ℂ)(T:PChart G (fine R i p))(j:ℕ)
local notation "K" => model R N i p hi
local notation "Ω" => shift R N i p hi F
local notation "Δ" => slice R N i p F
variable (g:Assembly.GradeAt (Y.power J) (Bulk.projected (Y.mark J)))
variable (known:∀ l≤j,∀ A:Link G (fine R i p),(Air.discharge Y l (Stationary.arm G (fine R i p) 1 A)).part J.val=
   w*Complex.ofReal (MvPolynomial.eval A (coeff l (flash T))))
include g known

theorem original (x:fieldDir G c 1)(z:Key F G→ℝ):
    readJet (Y.power J+j) (chartMark (step R i p) F (saddle R N i p F) K x z Y J)=
      w * Complex.ofReal (coeff j (OriginalRadialSeries.observed (sample (step R i p) F x z)
          (WilsonOriginalFoldedMarkedRightColumn.before R N i p hi F T))):=by
  let v:=sample (step R i p) F x z
  let a:=WilsonOriginalAffineAngularRay.direction Ω Δ v
  have ht:=shore_green (step R i p) F (saddle R N i p F) (center R N i p hi F) (center R N i p hi F).contDiff.contDiffAt (map_zero _)
  have hz:=shore_zero (step R i p) F (saddle R N i p F) (center R N i p hi F) (map_zero _)
  have ha:ContDiffAt ℝ ω a 0:=WilsonOriginalAffineAngularRay.smooth Ω Δ v ht hz
  let u:ℝ→ℝ×fieldDir G n 1:=fun s=>(1,Stationary.arm G n 1 (a s))
  have hu:ContDiffAt ℝ ω u 0:=contDiffAt_const.prodMk ((Stationary.arm G n 1).contDiff.contDiffAt.comp 0 ha)
  let A:=Bulk.projected (Y.mark J)
  have genuine:chartMark (step R i p) F (saddle R N i p F) K x z Y J=A ∘ Response.echo u:=by
    funext s
    change Y.mark J s (mantle (WilsonOriginalAffineAngularRay.pathAt Ω Δ v s))=_
    rw [WilsonOriginalAffineAngularRay.raw Ω Δ v hz,←Mosaic.mantle_input]
    change Y.mark J s (represent (Stationary.arm G n 1 (s • a s)))=_
    simp [A,Bulk.projected,Response.echo,u,map_smul]
  have row(l:ℕ)(hl:l≤j)(s:ℝ):Assembly.jet A (Y.power J+l) (u s)=
      w * Complex.ofReal (MvPolynomial.eval (a s) (coeff l (flash T))):=by
    simpa only [Air.discharge,part_lit,A,u] using known l hl (a s)
  rw [genuine,WilsonOriginalClearedAngularRead.original A g u hu a ha w (flash T) j row]
  rw [←WilsonOriginalAffineAngularRay.coefficient Ω Δ v ht hz (flash T) j]
  rfl

theorem named (B:Link G c)(z:Key F G→ℝ):
    readJet (Y.power J+j) (chartMark (step R i p) F (saddle R N i p F) K (Stationary.arm G c 1 B) z Y J)=
      w * Complex.ofReal (coeff j (OriginalRadialSeries.observed (Sum.elim z B)
          (WilsonOriginalFoldedMarkedRightColumn.before R N i p hi F T))):=by
  exact original R N i p hi F Y J w T j g known (Stationary.arm G c 1 B) z

end YM.Integration.WilsonOriginalPrimerForestRead
end
