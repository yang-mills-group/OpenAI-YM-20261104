import YM.Integration.WilsonPhysicalStationMixedWickPortfolio
import YM.Integration.WilsonPhysicalStationMixedBasisSale

/-! Spend all the raw entries of one funded mixed test on the authentic
field before taking its original regulator limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickNamedPrice
open Filter Finset Function Lattice RG Wilson Labels Source Cells Extraction Table Climb Trace
open PhysMS Spec OPE Next.UVStress Trace.Pilot PhysicalNext.Repeat.Legato
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare Next.Rank.Station
open WilsonPhysicalStationMixedWickTest (reference)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationThermalBasisOffice (rank)
open WilsonPhysicalStationMixedBasisSale (Sold fee)
open WilsonMovingForkReporterMixedBasis (Slot)
open WilsonPhysicalStationMixedWickMeasured (joined)
open WilsonOriginalBlissMixedGram (grades)
open WilsonMovingForkReporterBothArms (Filed)
open Further.CorrectedLift (ladder)
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}(J₀:ℝ→tower S)(J:Scaling S)
    (V:∀m,Vane R.family m){m D:ℕ}(A:Slot R.family)(hl:A.left < m+1)(hr:A.right < m+1)
    (checked:(V m).checked f H m)
set_option quotPrecheck false
local notation "AX" => R.family.path.levels
local notation "C₀" => Cells.standard R.family
local notation "d₁" => (⟨A.left,hl⟩:Fin (m+1))
local notation "d₂" => (⟨A.right,hr⟩:Fin (m+1))
local notation "T₀" => (AX).clock.monitor (V m).k
local notation "z₀" => probe R.family A.dual A.turn A.arm

def price (x:(C₀).Field A.left):ℝ:=∑i,‖ladder R.family A.left x i‖*fee R A i

theorem filed (sale:Sold R (V m) A hl hr D checked)(x:(C₀).Field A.left)(q:ℕ)
    (hom:∀i,ladder R.family A.left x i≠0 → rank R.family A.left i=q)
    (ξ:Points 2)(member:tested AX (V m).b (V m).k ξ∈A.site)(fits:FitSky AX (V m).b (V m).k ξ):
    ∀ᶠ N:ℕ in atTop,∀p:ℕ,∀fine:(V m).k<N,
    ((D:ℝ)+1)*(T₀)^((rank R.family A.right A.dual-q:ℕ):ℝ)*
      ‖WilsonPhysicalStationMixedWickPair.cell R (V m) d₁ d₂ (p:=p) checked fine (V m).k
        (choose AX (V m).b (V m).k ξ) (ladder R.family A.left x) z₀-
      reference R.family (ladder R.family A.left x) z₀ (tested AX (V m).b (V m).k ξ)‖≤price R A x:=by
  filter_upwards [sale] with N budget p fine
  apply WilsonPhysicalStationMixedWickPortfolio.priced R (V m) d₁ d₂ checked fine _ _ _ z₀ _ _
  · exact mul_nonneg (by positivity) (Real.rpow_nonneg (Real.exp_pos _).le _)
  · intro i live
    exact (hom i live) ▸ budget p fine ξ member fits i

include F in
theorem original {Ml Bl Mr Br:ℝ}(left:Filed (f:=f) (l:=ℓ) J₀ J V A.left m Ml Bl)
    (right:Filed (f:=f) (l:=ℓ) J₀ J V A.right m Mr Br)(simple:G.Simple)(below:(ℓ:Filter _)≤f.fuse)
    (sale:Sold R (V m) A hl hr D checked)(x:(C₀).Field A.left)(q:ℕ)
    (hom:∀i,ladder R.family A.left x i≠0 → rank R.family A.left i=q)
    (ξ:Points 2)(member:tested AX (V m).b (V m).k ξ∈A.site)(fits:FitSky AX (V m).b (V m).k ξ):
    ((D:ℝ)+1)*(T₀)^((rank R.family A.right A.dual-q:ℕ):ℝ)*
      ‖S.classMoment S (grades A.left A.right) ((V m).wheel.r • tested AX (V m).b (V m).k ξ)
        (joined R J (m:=m) d₁ d₂ x z₀)-
      reference R.family (ladder R.family A.left x) z₀ (tested AX (V m).b (V m).k ξ)‖≤price R A x:=by
  apply WilsonPhysicalStationMixedWickMeasured.original R F J₀ J V d₁ d₂ checked left right simple below x z₀ ξ fits
  exact filed R V A hl hr checked sale x q hom ξ member fits

end YM.Integration.WilsonPhysicalStationMixedWickNamedPrice
end
