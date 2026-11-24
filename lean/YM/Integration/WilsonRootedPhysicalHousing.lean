import YM.Integration.WilsonRootedPhysicalCatalogue
import YM.Integration.WilsonVacuumPreResetCatalogue
import YM.Push.GRID_APPROXIMATION.Hit

/-! Housing for the spatially truncated genuine pre-reset physical catalogue. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalHousing
open Function Filter Finset Set Lattice Wilson RG RG.Shoot Pressure
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals Gas Ursell Trees Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes PhysicalNext PhysicalNext.Repeat Legato
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Blaze.March Captain
open Opera Height Beam Song Greenbelt Next.Scheduling Extra.Iteration UVNext
open PriceCompiler Org Input Supply Pressure.Testing Time Roost Match Refrain WilsonStartup
open RG01Estimate RG01Estimate.CensusStep WilsonLimitConstruction.FundedCensusVacuum
open WilsonVacuumPreResetCatalogue
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {m N per : ℕ} (S : Station R N per m)
local notation "H" => S.guide
local notation "B" => R.alloy.B.a.budget m
local notation "X" => ledger R.kit H
local notation "α" => R.alloy.B.kin.alpha N m

def spatial (t D : ℕ) := (catalogue R S t).filter
  (fun i=>coverNumber (B).B (contents H B i).support ≤ D)

def radius (p : BudgetPoint) (D : ℕ):=(D+1)*Push.GridApprox.Attach.leg p.B

lemma center (x : Site (R.family.side m per)) (q : Magazine H) (hx : Meadow.share H B x q ≠ 0) :
    x∈(contents H B q).support := by
  cases q with
  | inl q =>
    change x∈(dashboard H q).support
    rw [Beam.see]
    by_contra h
    apply hx
    change (if x∈Song.perf H q then _ else 0)=0
    exact if_neg h
  | inr q =>
    have hi : (strings (ships R.alloy.B N m per).down B q).site=x:=by
      by_contra h
      exact hx (by simp [Meadow.share,h])
    exact hi ▸ (strings (ships R.alloy.B N m per).down B q).anchor

lemma extent (D t : ℕ) (q : Magazine H) (hq : q∈spatial R S t D) (x : Site (R.family.side m per))
    (hx : Meadow.share H B x q≠0) : (contents H B q).support⊆neighbors (radius B D) x := by
  intro y hy
  have bounds:=(Finset.mem_filter.mp hq).2
  have a:=Push.GridApprox.Attach.distance_charge _ (B).B x y (center R S x q hx) hy
  have z:= (Nat.div_lt_iff_lt_mul (Push.GridApprox.Attach.leg_pos (B).B)).mp (Nat.lt_succ_of_le (a.trans bounds))
  exact (neighbors_mem ..).2 z.le

/-- The retained finite physical catalogue, with genuine root shares and original rotations. -/
def rack (r D t : ℕ) :
    Abacus.Rack X (radius B D) (portion R S r (spatial R S t D)) :=
  address R S r (radius B D) (spatial R S t D) (extent R S D t)

lemma charge (i : ℕ) : coverNumber (B).B ((X).reg i).support =
    coverNumber (B).B (contents H B (pennant H i).2).support :=
  ProjectorNext.Equivariance.moves_cost _ _ _ _

end YM.Integration.WilsonRootedPhysicalHousing
