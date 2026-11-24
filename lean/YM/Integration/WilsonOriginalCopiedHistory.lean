import YM.Integration.WilsonOriginalCoverCoefficient
import YM.Integration.WilsonOriginalCoveredPlainStep

/-! The independently computed covered coefficient uses only the filed formal kernel and submitted source colors. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCopiedHistory
open FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {W : Census V}

/-- A submitted color and its covered output are defined on every multiple of the reporting torus. -/
abbrev Colors (G : Gauge) (W : Census V) (n : Side) :=
  (grid : Side) → n.val∣grid.val → Bulk.Colors W G grid

abbrev Values (G : Gauge) (W : Census V) (n : Side) :=
  (grid : Side) → n.val∣grid.val → ℕ → Stationary.Link G grid → Poly W

def forest (R : Run G) (i : ℕ) (grid : Side) (u : Covers R.family.path.levels.S i grid) :
    Forest (R.family.path.levels.clock.op i u.val).ratio :=
  (Tree.select (R.family.path.levels.clock.op i u.val).ratio
    (R.family.path.levels.clock.op i u.val).patch.odd_side).some

def tag (R : Run G) (i : ℕ) (grid : Side) (u : Covers R.family.path.levels.S i grid) :
    (R.family.path.levels.clock.op i u.val).Choices := Classical.arbitrary _

/-- One covered calculation on the prescribed input. No date in this recursion uses a tested output fit. -/
def block (R : Run G) {N i per : ℕ} (cut : i<N) (p : ℕ)
    (input : Colors G W (R.family.side (i+1) per)) : Values G W (R.family.side i per) :=
  fun grid tiles => WilsonOriginalCoverCoefficient.read R cut p grid
    (fun c=>input (R.family.side (i+1) c.val) (tiled R tiles c)) (forest R i grid) (tag R i grid)

/-- Restore all occupied coefficients to group variables using the same fixed unmarked bank and measured reset. -/
def receive {n : Side} (input : Values G W n) (quiet : Layout G) (tape : Finset Age) (grade : V → ℕ)
    (coin : Pace.Coin) (starts : coin 0=0) (depth p : ℕ) : Colors G W n :=
  fun grid tiles => WilsonOriginalCoverJetColors.colors (QuadraticLocal.Fk.money quiet tape)
    (fun s => Launch.index W grade s.val+1) p
    (WilsonOriginalCoverJetColors.reset p (input grid tiles) ((QuadraticLocal.Rebirth.caliber coin starts).back depth))

end YM.Integration.WilsonOriginalCopiedHistory
