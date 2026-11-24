import YM.Integration.WilsonReportHarvestSlabPhysicalGerm

/-! A common linear fold of the physical and retained cabinets preserves the affine identity separately on every marked mask. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabMaskBlend
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open WilsonReportHarvestSlabLabels WilsonAllDateHarvestPropagation
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

open private affine from YM.Integration.WilsonReportHarvestSlabPhysicalGerm
private theorem split (A B C z:ℂ)(eq:C-A=z*(B-A)):C=z*B+(1-z)*A:=by linear_combination eq

local notation "S₀"=>Stock.census (Fin 3)
variable {G:Gauge}{C:Family G}{n per:ℕ}

theorem original (o:Fin 3 → Site (C.side n per))(E:Fin 3 → Motion)(mask:(S₀).Mode)
    (L U:Poly (Mine.ward o E S₀ n))(z:ℂ):
    (baseFold o E S₀ (WilsonAllDateHarvestAffine.blend L U z)).part mask =
      z*(baseFold o E S₀ U).part mask + (1-z)*(baseFold o E S₀ L).part mask:=by
  let f:Poly (Mine.ward o E S₀ n) →ₐ[ℂ] Poly S₀:=feed (fun _=>(1:ℂ)) (chamber S₀ ((Mine.tree o E).labelY n))
  apply split
  exact affine f.toLinearMap L U z mask

end YM.Integration.WilsonSeparatedOriginalSlabMaskBlend
