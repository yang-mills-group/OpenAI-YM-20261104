import YM.Integration.WilsonOriginalProjectedCurvaturePointCredit

/-! The actual independently scaled test can be read at any originally appointed
site with a fixed price per unit of its original analytic income. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureReader
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open scoped Classical BigOperators
variable {G : Gauge} {B : MS.Local.Physical.Deck G}
  {V : Type} [DecidableEq V] [Fintype V] (R : Run G) (J : Request V)
  (hG : G.Simple) (Q : MS.Land.Prescription B) (u : V → MS.Rake.Label B)
  (A : NumericSchedule R.family J)
  (datum : LocalFormal.Datum R.family (Stock.census V))
  (o : V → Site (R.family.side (datum.level+1) datum.period))
  (μ : ℝ) (orders : V→ℕ)

local notation "D₁" => ActualOriginalQPointSetup.pointDatum R J 0 0 (fun _ => 0)
local notation "D₀" => ActualOriginalQPointSetup.pointDatum R J datum.period (datum.level+1) o
local notation "c₀" => ActualOriginalQInitialInput.scales R hG u J A datum Q o μ orders

theorem raw (i : V) (f : (ActualRunQlocalNativeTuple.orbit D₀ i).Mood) {b : ℝ}
    (hf : (ActualRunQlocalNativeTuple.orbit D₀ i).Bill f.val b) :
    ‖ActualRunQlocalNativeTuple.reader D₀ i f‖ ≤ readerPrice D₁ i*b := by
  rw [← WilsonOriginalProjectedCurvaturePointCredit.reader R J datum.period (datum.level+1) o i]
  exact (ActualRunQlocalNativeTuple.reader_bound D₀ i f hf).trans_eq (by unfold readerPrice; ring)

theorem scale (i : V) : ‖c₀ i‖ ≤ 1 := by
  let n := ActualOriginalQInitialInput.normalizer R hG u J A datum Q o μ orders
  have hn : 1≤n := le_max_left _ _
  have hp : 0<n := zero_lt_one.trans_le hn
  change ‖((n:ℂ)⁻¹)‖ ≤ 1
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  exact (inv_le_one₀ hp).mpr hn

theorem submitted (input : TestSpace (ActualRunQlocalNativeTuple.orbit D₀))
    (i : V) {b : ℝ} (hf : (ActualRunQlocalNativeTuple.orbit D₀ i).Bill (input i).val b) :
    ‖ActualRunQlocalNativeTuple.reader D₀ i (FullQLocal.VariableScaling.tests c₀ input i)‖ ≤
      readerPrice D₁ i*b := by
  change ‖ActualRunQlocalNativeTuple.reader D₀ i (c₀ i • input i)‖ ≤ _
  rw [map_smul, smul_eq_mul, norm_mul]
  calc
    _ ≤ 1 * ‖ActualRunQlocalNativeTuple.reader D₀ i (input i)‖ :=
      mul_le_mul_of_nonneg_right (scale R J hG Q u A datum o μ orders i) (norm_nonneg _)
    _ ≤ _ := (one_mul _).le.trans (raw R J datum o i (input i) hf)

end YM.Integration.WilsonOriginalProjectedCurvatureReader
