import YM.Integration.WilsonPositionThermometerStationTransport
import YM.Integration.WilsonRegisteredRectangleChannelClock
import YM.Integration.WilsonPositionThermometerStationNorm

/-! Transport the actual signed star field intact to the already selected earlier date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedAlignedStation
open Function Set Filter Finset RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open Extra.Histories PhysicalNext.Repeat.Legato
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}

private theorem column (i:ℕ) :
    (R.family.path.levels.params (i+1)).columns ≤ ((R.family.S.block i).val:ℝ) := by
  have h:=WilsonRegisteredRectangleChannelClock.cost R.family.path.levels i
  let a:=R.family.path.levels.params (i+1)
  change 1+a.paths+a.width⁻¹+a.columns+a.clip.relaxation+a.supportExponent ≤ _ at h
  change a.columns ≤ _
  linarith only [h,a.paths_pos,inv_nonneg.mpr a.width_pos.le,a.price_pos,a.clip.radius_pos]

theorem original (simple:G.Simple) (d:ℕ) (ε:ℝ) (positive:0<ε) :
    ∀ᶠ m in atTop, ∀ {D:ℕ} (V:Vane R.family D) (j:Fin (D+1)),j.val=d → V.k=m →
    V.checked f H D → ∀ (w:(Bel R.family.book).Field j) (k N p:ℕ),
    R.family.ref j ≤ k → k ≤ m → m < N →
    let x:=V.wheel.atCut (N,p) j w
    (R.family.labels.level j).coeffSize (awake R.family j k N p x) ≤
      (R.family.S.a k / R.family.S.a m) * ((R.family.path.levels.clock.hatBeta m)^ε *
        (WilsonPositionThermometerStationNorm.cost R.family d * ‖w‖)) := by
  filter_upwards [WilsonPositionThermometerStationNorm.original (C:=R.family)
    (f:=f) (H:=H) simple R.makes d ε positive] with m pay D V j rank seat checked w k N p enter dated live
  let x:=V.wheel.atCut (N,p) j w
  have station:=pay V j rank seat checked w N p live
  have interval:=WilsonPositionThermometerStationTransport.interval (d:=j.val) (N:=N) (p:=p)
    R.family R.makes enter dated live.le x 1 (fun i _ _=>by simpa only [Real.rpow_one] using column R i)
  rw [Real.rpow_one] at interval
  exact interval.trans (mul_le_mul_of_nonneg_left station
    (div_nonneg (R.family.S.a_pos k).le (R.family.S.a_pos m).le))
end YM.Integration.WilsonAddressedAlignedStation
end
