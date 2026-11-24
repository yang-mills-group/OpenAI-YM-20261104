import YM.Integration.WilsonOriginalProjectedCurvatureBudget
import YM.Integration.WilsonOriginalProjectedCurvaturePassport

/-! The second exponential weight appearing on a genuinely rendered row
pays for its rooted passport, each additional occupied lift, and the original
field paths. Its full physical price is expressed in the original row catalogue. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureEnvelope
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport
open scoped Classical BigOperators
variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ)
  (s : ActualOriginalQPackets.Row (R:=R) u) (σ τ : ℝ) (extra : V → ℕ)

def liftHeight : ℕ := (paper D u).height s.1.1 + extra s.1.1

def gross : ℝ := wallet Q D u μ orders N s σ *
  Real.exp (τ * ((liftHeight D u s extra + ActualOriginalQCharges.rowFall u s : ℕ) : ℝ))

omit [DecidableEq V] [Fintype V] in
theorem booked : gross Q D u μ orders N s σ τ extra =
    wallet Q D u μ orders N s (σ+τ) * Real.exp (τ * (liftHeight D u s extra : ℝ)) := by
  simp only [gross, wallet, Nat.cast_add, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem commissioned (hL : L ≤ N) (w : V → ℝ) :
    Poly.toll w ((Stock.census V).fire s.1.1) *
      ‖(Pert.Asymptotics.regulatorRun R.family N p L : ℂ) ^
        ((grade u s : ℤ) - (ActualRunKernelPackets.tokenRank R (degree u) s : ℤ))‖ *
      gross Q D u μ orders N s σ τ extra =
    (‖fee Q u μ orders s.1‖ * ActualOriginalQCharges.rowPrice D u w (σ+τ) s) *
      Real.exp (τ * (liftHeight D u s extra : ℝ)) := by
  rw [booked,← mul_assoc,WilsonOriginalProjectedCurvatureBudget.commissioned Q D u μ orders N s (σ+τ) hL w]

theorem full (hL : L ≤ N) (w : V → ℝ) :
    (∑ i : ActualOriginalQPackets.Row (R:=R) u,
      Poly.toll w ((Stock.census V).fire i.1.1) *
      ‖(Pert.Asymptotics.regulatorRun R.family N p L : ℂ) ^
        ((grade u i : ℤ) - (ActualRunKernelPackets.tokenRank R (degree u) i : ℤ))‖ *
      gross Q D u μ orders N i σ τ extra) =
    ∑ i : ActualOriginalQPackets.Row (R:=R) u,
      (‖fee Q u μ orders i.1‖ * ActualOriginalQCharges.rowPrice D u w (σ+τ) i) *
      Real.exp (τ * (liftHeight D u i extra : ℝ)) := by
  exact Finset.sum_congr rfl fun i _ => commissioned Q D u μ orders N i σ τ extra hL w

end YM.Integration.WilsonOriginalProjectedCurvatureEnvelope
