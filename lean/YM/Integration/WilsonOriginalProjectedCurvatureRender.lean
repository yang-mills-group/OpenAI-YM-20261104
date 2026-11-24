import YM.Integration.WilsonOriginalProjectedCurvatureLoan
import YM.QuadraticLocal.Earn.Rendering

/-! The positive, actually paid original Q rows as manuscript rows.
They carry the actual marked wallet, projected color tensor, coupled regulator,
and the full old footprint on the physical representative. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureRender
open Function Finset Lattice Wilson RG Source Labels Marker QuadraticLocal.Earn
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQPackets ActualOriginalQReaders
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureRoster
open WilsonOriginalProjectedCurvatureSalary WilsonOriginalProjectedCurvatureBudget
open scoped Classical BigOperators
variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ)
  (s : ActualOriginalQPackets.Row (R:=R) u) (σ : ℝ) (extra : ℕ)
  (h : 0 < wallet Q D u μ orders N s σ)

def row : QuadraticLocal.Earn.Row (paper D u) (Stock.census V) G (tastes D) where
  binder := WilsonOriginalProjectedCurvatureBinder.selected D u s.1.1 extra
  lamp := WilsonOriginalProjectedCurvatureLoan.filed u s
  atom := divided (placed u s) σ
  lawful := invariant _ _ (lawful u s)
  clear := ActualRunKernelPackets.tokenRank R (degree u) s = 0
  salary := wallet Q D u μ orders N s σ
  sound := h
  paint := paint Q D u μ orders N s σ
  rank := id

local notation "T" => row Q D u μ orders N s σ extra h

theorem priced : (T).Budget ∧ (T).Graceful σ ∧
    (T).Credentials (ActualOriginalQLayout.rankCap R u)
      (fun _ => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u) := by
  refine ⟨bound Q D u μ orders N s σ, (graceful _ _ (substantial Q D u μ orders N s σ h)).le, ?_⟩
  refine ⟨(WilsonOriginalProjectedCurvatureLoan.receipt u s).2.2.1, ?_⟩
  change _ = ∑ _ ∈ ({s.1.1} : Finset V), WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u
  simp
  rfl

theorem submitted (x : tastes D) (g : ℝ) (U : Config G (R.family.side L p)) :
    (T).nominal g x U = (g : ℂ) ^ (-(ActualRunKernelPackets.fieldRank R (degree u) s : ℤ)) *
      (ActualOriginalQPackets.token Q D u μ orders N s).read
        (testInclusion (ActualRunQlocalNativeTuple.orbit D) x) U := by
  let J := divided (placed u s) σ
  let o := ActualRunQlocalNativeTuple.root D s.1.1
  change paint Q D u μ orders N s σ x * (↑(g ^ (WilsonOriginalProjectedCurvatureLoan.filed u s).lag *
    J.unmasked U o) : ℂ) = _
  rw [(WilsonOriginalProjectedCurvatureLoan.receipt u s).1, Complex.ofReal_mul, Complex.ofReal_zpow]
  rw [← work Q D u μ orders N s σ x U (substantial Q D u μ orders N s σ h)]
  ring

theorem geometry : (T).mode = (Stock.census V).fire s.1.1 ∧
    (T).center = ActualRunQlocalNativeTuple.root D s.1.1 ∧
    (T).length = (paper D u).height s.1.1 + extra + ActualOriginalQCharges.rowFall u s := by
  have hb := WilsonOriginalProjectedCurvatureBinder.filed D u s.1.1 extra
  refine ⟨hb.1,hb.2.1,?_⟩
  change (WilsonOriginalProjectedCurvatureBinder.selected D u s.1.1 extra).length +
    (placed u s).length = _
  rw [hb.2.2, (charges u s).1]

end YM.Integration.WilsonOriginalProjectedCurvatureRender
