import YM.Integration.WilsonOriginalReceivedCopiedCover

/-! Uniqueness of the represented signed output on independently submitted complete copied inputs. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCopiedContraction
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
variable {J : Passport (R.family.side (m+1) n) V} {W : Census V}
variable (h : m < N)
variable (D : Layout G) (T : Finset Age) (p : ℕ) (M : ι → Row J W G α) (w : V → ℕ)
local notation "CC" => Covers R.family.path.levels.S m
local notation "CC'" => coverFilter R.family.path.levels.S m

def contraction (X:Side) (inputs:∀ b:Covers R.family.path.levels.S m X,Bulk.Colors W G (R.family.side (m+1) b.val))
    (Y:∀ b:Covers R.family.path.levels.S m X, Forest (R.family.path.levels.clock.op m b.val).ratio)
    (P:∀ b:Covers R.family.path.levels.S m X, (R.family.path.levels.clock.op m b.val).Choices)
    (x:Stationary.Link G X) (j:ℕ) (b:Covers R.family.path.levels.S m X) : Poly W :=
  let A := Stationary.arm G (R.family.side m b.val) 1 (convey (coverWin b.prop) x)
  (((Pages X (R.family.side m b.val):ℕ):ℝ)⁻¹ : ℝ) •
    Order.observe W p (Order.logMarked (Bulk.Fk ((K).step N m b h) (Y b) (P b) (inputs b) A p)) j



theorem named {K₀ : Passport (R.family.side m n) V} (Y : μ → Row K₀ W G α)
    (published : RepresentsCover R h D T p M w Y) (t : α) (grid : Side)
    (multiple : (R.family.side m n).val∣grid.val)
    (inputs : ∀ b : CC grid, Bulk.Colors W G (R.family.side (m+1) b.val))
    (matched : ∀ b : CC grid, copyColor (tiled R multiple b) M w (fun v=>(M v).paint t) D T = inputs b)
    (F : ∀ b : CC grid, Forest (S m b.val).ratio) (tag : ∀ b : CC grid, (S m b.val).Choices)
    (A : Stationary.Link G grid) (e : ℕ) (he : e ≤ p) :
    Tendsto (contraction R h p grid inputs F tag A e) (CC' grid)
      (𝓝 (peek multiple Y w D T t e A)) := by
  apply (published t grid multiple F tag A e he).congr'
  filter_upwards with b
  unfold FVA1Physical.TwoReset.FkCover contraction
  rw [matched b]

end YM.Integration.WilsonOriginalCopiedContraction
