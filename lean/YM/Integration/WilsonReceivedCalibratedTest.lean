import YM.Integration.ActualOriginalQInitialPreparation
import YM.Integration.WilsonMixedTestTableau

/-! The reported old test on the authentic bare curvature source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCalibratedTest
open Lattice Wilson RG Source Labels Marker LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep QuadraticLocal.Affinity PhysicalNext.Repeat.Legato

variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V]
  (R:Run G) (simple:G.Simple) (u:V→MS.Rake.Label B)
  (J:Request V) (A:NumericSchedule R.family J)
  (d:LocalFormal.Datum R.family (Stock.census V)) (Q:MS.Land.Prescription B)
  (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (orders:V→ℕ)
local notation "req" => ActualOriginalQPointSetup.request R u J
local notation "D" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
local notation "H" => ActualOriginalQInitialInput.normalizer R simple u J A d Q o μ orders
local notation "source" => ActualOriginalQInitialPreparation.input R simple u J A d Q o μ orders
local notation "raw" => ActualOriginalQInput.input Q D u (μ-R.family.S.scale d.cutoff) orders simple d.cutoff d.below

def submit (x:IndependentTests (req).tests) : IndependentTests (ActualRunQlocalNativeTuple.orbit D) :=
  fun v=>⟨(H:ℂ)⁻¹ • (x v).val,by
    have one:(1:ℝ) ≤ H:=le_max_left _ _
    have pos:0<H:=zero_lt_one.trans_le one
    apply ((x v).property.smul (H:ℂ)⁻¹).more
    simpa only [mul_one,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos] using
      inv_le_one_of_one_le₀ one⟩

theorem original (x:IndependentTests (req).tests) (U:Config G (R.family.side (d.level+1) d.period)) :
    ((source).leaf (testInclusion (req).tests x)).density U =
      ((raw).leaf (testInclusion (ActualRunQlocalNativeTuple.orbit D)
        (submit R simple u J A d Q o μ orders x))).density U := by
  rw [ActualOriginalQInitialPreparation.input_density]
  rfl

end YM.Integration.WilsonReceivedCalibratedTest
