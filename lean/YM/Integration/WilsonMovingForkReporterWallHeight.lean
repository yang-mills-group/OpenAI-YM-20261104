import YM.Integration.WilsonReporterWeightedCourt

/-! The actual dated physical Wilson chart supports every smaller registered measurement horizon on its same covariance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterWallHeight
open PhysicalNext PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft MergeProof
open Function Filter Set Lattice Wilson RG Pressure Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec Vac.Numbers West
     Weaver Worker Radian Tapes.West Market
open scoped Topology BigOperators Classical
variable {G:Gauge} {F:Family G} {k:ℕ} {b:ℝ}

theorem narrow (A:Levels G) {d D k p n θ:ℕ} {b:ℝ} {F:AtlasData G A.S p} (inside:d≤D)
    (actual:Wall.VantageSky A D k p n θ b F) : Wall.VantageSky A d k p n θ b F := by
  have model : Wall.Model A d k p F := ⟨actual.1.1,fun x y a c ha hc=>
    actual.1.2 x y a c (by omega) (by omega)⟩
  exact ⟨model,actual.2.lamps,actual.2.matchQ,actual.2.mirror,actual.2.closed,actual.2.preserve,
      fun x a h=>actual.2.budget x a (by omega),actual.2.lid⟩

variable {C:Family G} (B:Binding C) (H:C.Makes) (O:HaarBudget G) (J:ChartRatio G)
local notation "AX" => C.path.levels

include H in
theorem original (simple:G.Simple) (D:ℕ) : ∀ᶠ k:ℕ in atTop,
    ∀ {u:ℕ} {α:Purse} {w z l r:ℝ} (_:LegacyCostSky B J w z α k u D O l r),
      2≤u → ∀ N p d, d≤D →
      Wall.VantageSky AX d k p 2 α.taylor α.band (PhysicalNext.RankCovariance.stamp AX N p) := by
  filter_upwards [eventually_ge_atTop (C.ref D),Radian.commissioned AX simple D 2 (by decide) chartHeat_pos]
    with k aged model u α w z l r L two N p d h
  have stage : D-1 ≤ C.path.levels.clock.J k-1-2 := by
    have depth := (H.stages D).1
    have later := C.path.levels.fits.mono aged
    omega
  obtain ⟨sealed_,pay⟩ := y_supplySky _ _ rfl L.age.allot.permitted stage L.clears N p
  let chart := pay 2 two
  obtain ⟨Q,hS,hA,hP⟩ := chart.optics
  exact narrow AX h ⟨model p _ sealed_,Radian.flownSky _ _ _ _ _ hS hP hA
    chart.visor chart.hinge chart.rotor chart.force⟩

end YM.Integration.WilsonMovingForkReporterWallHeight
end
