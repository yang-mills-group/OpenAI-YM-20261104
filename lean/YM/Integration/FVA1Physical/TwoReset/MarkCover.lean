import YM.Integration.FVA1Physical.TwoReset.ReadCopies
import YM.Integration.RunFormalChain

/-!
# Independent (cover step) Wilson prescription in the mixed sector

Use RG02.Bulk.Fk on the SAME physical chain. Power of g held with
each stencil in its Loan; run the single normalized conditional prescription
to the fixed order in the indicated coupling. The `Layout` is the analytic
vacuum packet of that step; it too will be required to give the prescribed
orders. As in qlocal, period convention is to compare to the periodization
of the full cover kernel (thus NOT to render the exact finite-torus Fk as
though it agreed with the cover on short paths). Specify the periodized
answer by its defining diagram limit: for periodic inputs / fields repeated
to larger multiples, take the *whole connected logarithm* in the finite-torus
Fk rule, including all marked constants, then take infinite-volume limit,
normalized per repeat. Allow all distinct tests of marks, all cluster
separations; disjoint products from exponentiation, no connected weight
claimed on disconnected products.

Crucial for feeding this to another step: even on a fixed period c,
we identify also ALL multiple-period external-field readouts of the
c-periodized kernel. No short-offset/injective-support consolation for
forgetting which predecessors contributed (test addresses stay on the
actual layouts). This gives an induction in that cover convention.
-/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
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

/-- The covering-torus arithmetic keeps the lifted paths and tag schedule. -/
theorem tiled {C:Side} (z : (c).val ∣ C.val) (b : CC C) : (R.family.side (m+1) n).val ∣ (R.family.side (m+1) b.val).val :=
  subdiv_dvd (S m n).ratio (S m b.val).ratio rfl (z.trans b.prop)

protected def FkCover (t:α) (X:Side)(hX:(R.family.side m n).val∣X.val)
    (Y:∀ b:Covers R.family.path.levels.S m X, Forest (R.family.path.levels.clock.op m b.val).ratio)
    (P:∀ b:Covers R.family.path.levels.S m X, (R.family.path.levels.clock.op m b.val).Choices)
    (x:Stationary.Link G X) (j:ℕ) (b:Covers R.family.path.levels.S m X) : Poly W :=
  let D₁ := copyColor (tiled R hX b) M w (fun i:ι=>(M i).paint t) D T
  let A := Stationary.arm G (R.family.side m b.val) 1 (convey (coverWin b.prop) x)
  (((Pages X (R.family.side m b.val):ℕ):ℝ)⁻¹ : ℝ) •
    Order.observe W p (Order.logMarked (Bulk.Fk ((K).step N m b h) (Y b) (P b) D₁ A p)) j

/-- `Ψ`: values in Coupling unit BEFORE adjacently reparameterizing. -/
def MarkCover (Ψ : α → ∀ (X:Side), (R.family.side m n).val ∣ X.val →
    ℕ → Stationary.Link G X → Poly W) : Prop :=
  ∀ t X hX (Y: (b:CC X) → Forest (S m b.val).ratio) (P:∀ b:CC X, (S m b.val).Choices)
    (x:Stationary.Link G X) (j:ℕ), j ≤ p → Tendsto (TwoReset.FkCover R h D T p M w t X hX Y P x j)
      (CC' X) (𝓝 (Ψ t X hX j x))

lemma cover_unique {a b} (H:MarkCover R h D T p M w a) (H':MarkCover R h D T p M w b) :
    ∀ t X hX j x, j≤p → a t X hX j x=b t X hX j x := by
  intro t X hX j x hj
  haveI : NeBot (CC' X):= coverFilter_neBot R.kit.floor m X
  let Y(b:CC X) := (Tree.select (S m b.val).ratio (S m b.val).patch.odd_side).some
  let P(b: CC X) : (S m b.val).Choices := Classical.arbitrary _
  exact tendsto_nhds_unique (H t X hX Y P x j hj) (H' t X hX Y P x j hj)

-- Reading an actual family of analytic rows. Supplying the `D` from the
-- input at this step in `peek` is harmless: ONLY reading MARK jets here.
-- The unmarked formal action from the vacuum is supplied separately.
variable {B: Passport (R.family.side m n) V}
variable (Y:ν→Row B W G α)

def RepresentsCover := MarkCover R h D T p M w
    (fun t _ hX i v => peek hX Y w D T t i v)
end YM.Integration.FVA1Physical.TwoReset
