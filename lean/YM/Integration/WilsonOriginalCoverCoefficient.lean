import YM.Integration.WilsonOriginalCopiedContraction

/-! The independently computed covered coefficient uses only the filed formal kernel and submitted source colors. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCoverCoefficient
open FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} (R : Run G)
variable {V ι μ ν α : Type} [DecidableEq V] [Fintype V] {m n N : ℕ}
local notation "S" => R.family.path.levels.clock.op
local notation "K" => RunFormalChain.fromRun R
local notation "c" => R.family.side m n
local notation "f" => R.family.side (m+1) n

variable {W : Census V} (cut : m<N) (order : ℕ) (grid : Side)
local notation "I" => Covers R.family.path.levels.S m grid
variable (inputs : ∀ b : Covers R.family.path.levels.S m grid, Bulk.Colors W G (R.family.side (m+1) b.val))
variable (trees : ∀ b : Covers R.family.path.levels.S m grid, Forest (R.family.path.levels.clock.op m b.val).ratio)
variable (tags : ∀ b : Covers R.family.path.levels.S m grid, (R.family.path.levels.clock.op m b.val).Choices)

/-- The finite programs prescribe all input colors, trees and tags before taking the copy limit. -/
def read (d : ℕ) (u : Stationary.Link G grid) : Poly W :=
  limUnder (coverFilter R.family.path.levels.S m grid)
    (WilsonOriginalCopiedContraction.contraction R cut order grid inputs trees tags u d)

/-- A cofinal publication computes this independent covered value. -/
theorem identified (d : ℕ) (u : Stationary.Link G grid) (value : Poly W)
    (publication : Tendsto
      (WilsonOriginalCopiedContraction.contraction R cut order grid inputs trees tags u d)
      (coverFilter R.family.path.levels.S m grid) (𝓝 value)) :
    read R cut order grid inputs trees tags d u = value := by
  haveI : NeBot (coverFilter R.family.path.levels.S m grid) := coverFilter_neBot R.kit.floor m grid
  exact publication.limUnder_eq

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (U Z : ℕ → E → ℂ)
  (unit : Comparison.RG02.Adjacent.UnitCost) (p d : ℕ)

theorem reset_eq (through : ∀ i≤p, U i = Z i) (x : E) :
    Comparison.RG02.Adjacent.born U unit 0 p d x =
    Comparison.RG02.Adjacent.born Z unit 0 p d x := by
  unfold Comparison.RG02.Adjacent.born
  congr 1
  funext t
  unfold Comparison.RG02.Adjacent.ages Comparison.RG02.Adjacent.cover
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [through i (Finset.mem_range_succ_iff.mp hi)]

end YM.Integration.WilsonOriginalCoverCoefficient
