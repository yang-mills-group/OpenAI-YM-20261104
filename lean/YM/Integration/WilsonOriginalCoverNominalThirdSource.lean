import YM.Integration.WilsonOriginalCoverNominalThirdTable
import YM.Integration.WilsonOriginalCopiedHistory
noncomputable section
namespace YM.Integration.WilsonOriginalCoverNominalThirdSource
open FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} (R : Run G)
variable {ι μ ν α : Type} {m n N : ℕ}
local notation "S" => R.family.path.levels.clock.op
local notation "K" => RunFormalChain.fromRun R
local notation "c" => R.family.side m n
local notation "f" => R.family.side (m+1) n
variable {J : Passport (R.family.side (m+1) n) (Fin 3)}
local notation "W" => WilsonSeparatedOriginalJointLog.three
variable (h : m < N)
variable (D : Layout G) (T : Finset Age) (p : ℕ) (M : ι → Row J W G α) (w : Fin 3 → ℕ)
local notation "CC" => Covers R.family.path.levels.S m
local notation "CC'" => coverFilter R.family.path.levels.S m


variable {J₁ : Passport (R.family.side m n) (Fin 3)} (Z : ν → Row J₁ W G α)

def Filed (source : α → WilsonOriginalCopiedHistory.Values G W (R.family.side m n)) : Prop :=
  ∀ (t:α) (X:Side) (hX:(R.family.side m n).val∣X.val)
    (Y:∀ b:CC X,Forest (S m b.val).ratio) (u:∀ b:CC X,(S m b.val).Choices)
    (x:Stationary.Link G X) (j:ℕ), j≤p →
    Tendsto (WilsonOriginalCoverNominalThirdCopy.triad R h D T p M w t X hX Y u x j) (CC' X)
      (𝓝 ((source t X hX j x).part (WilsonSeparatedOriginalJointLog.shape univ)))

theorem received (source : α → WilsonOriginalCopiedHistory.Values G W (R.family.side m n))
    (pupil : WilsonOriginalCoverNominalThirdTable.Read R h D T p M w Z)
    (issued : ∀ (t:α) (X:Side) (hX:(R.family.side m n).val∣X.val) (j:ℕ), j≤p →
      ∀ x:Stationary.Link G X, source t X hX j x=peek hX Z w D T t j x) :
    Filed R h D T p M w source := by
  intro t X hX Y u x j hj
  rw [issued t X hX j hj x]
  exact pupil t X hX Y u x j hj

end YM.Integration.WilsonOriginalCoverNominalThirdSource
