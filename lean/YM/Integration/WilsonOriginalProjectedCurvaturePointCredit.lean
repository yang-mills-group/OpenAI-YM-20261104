import YM.Integration.WilsonOriginalProjectedCurvatureCredits
import YM.Integration.ActualOriginalQInitialInput

/-! The original point registration has a common lifted stencil and a
constant addressed reader price at every period, scale and choice of origins.
This sharpens the rooted offer on the actual physical initial datum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvaturePointCredit
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope
open WilsonOriginalProjectedCurvatureCredits
open scoped Classical BigOperators
variable {G : Gauge} {B : MS.Local.Physical.Deck G}
  {V : Type} [DecidableEq V] [Fintype V] (R : Run G) (J : Request V)
  (Q : MS.Land.Prescription B) (u : V → MS.Rake.Label B)
  (p L : ℕ) (o : V → Site (R.family.side L p))
  (μ : ℝ) (orders : V → ℕ) (N : ℕ)
  (σ τ : ℝ) (extra : V → ℕ) (w : V → ℝ)

local notation "D₀" => ActualOriginalQPointSetup.pointDatum R J p L o
local notation "D₁" => ActualOriginalQPointSetup.pointDatum R J 0 0 (fun _ => 0)
local notation "Rows" => ActualOriginalQPackets.Row (R:=R) u
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N p L

omit [DecidableEq V] [Fintype V] in
theorem reader (i : V) : readerPrice D₀ i = readerPrice D₁ i := by
  simp only [readerPrice, ActualOriginalQPointSetup.pointDatum,
    ActualOriginalQPointDatum.constant_eq, ActualOriginalQPointDatum.depth_zero, pow_zero, one_mul]
  simp only [ActualOriginalQPointDatum.datum, RG05Readout.Flatten.originR]

theorem quote (s : Rows) : quoted Q D₀ u μ orders σ τ extra w s =
    quoted Q D₁ u μ orders σ τ extra w s := by
  simp only [quoted, ActualOriginalQCharges.rowPrice, ActualOriginalQCharges.rowMass, reader R J p L o]
  rfl

theorem same : invoice Q D₀ u μ orders σ τ extra w =
    invoice Q D₁ u μ orders σ τ extra w :=
  Finset.sum_congr rfl fun s _ => quote R J Q u p L o μ orders σ τ extra w s

theorem offered (hL : L≤N) (hg : 0<g₀) (hup : g₀≤1) (hw : ∀i,0<w i)
    (x : Site (R.family.side L p)) :
    SumBudget (fun i : Funded Q D₀ u μ orders N σ =>
      if ActualRunQlocalNativeTuple.root D₀ i.1.1.1=x then
        Poly.toll w ((Stock.census V).fire i.1.1.1) * gross Q D₀ u μ orders N i.1 σ τ extra
      else 0) (invoice Q D₁ u μ orders σ τ extra w) := by
  rw [← same R J Q u p L o μ orders σ τ extra w]
  exact WilsonOriginalProjectedCurvatureCredits.offered Q D₀ u μ orders N σ τ extra w hL hg hup hw x

end YM.Integration.WilsonOriginalProjectedCurvaturePointCredit
