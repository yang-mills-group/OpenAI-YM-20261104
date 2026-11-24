import YM.Integration.WilsonOriginalProjectedCurvatureStartingField
import YM.Integration.WilsonOriginalProjectedCurvatureReader
import YM.Integration.ActualOriginalQInitialPreparation

/-! The complete enrolled density on the physical numerical schedule at its
own true upper datum, including the genuine submitted test normalization. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureScheduledField
open Function Finset Lattice Wilson RG Source Labels Marker Ac
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureCredits
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonOriginalProjectedCurvatureSalary
open FullQLocal FullQLocal.RenderedStep Extra.Trajectories QuadraticLocal
open scoped Classical BigOperators
variable {G : Gauge} {B : MS.Local.Physical.Deck G} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
  (R : Run G) (J : Request V) (hG : G.Simple) (Q : MS.Land.Prescription B)
  (u : V → MS.Rake.Label B) (A : NumericSchedule R.family J)
  (d : LocalFormal.Datum R.family (Stock.census V))
  (o : V → Site (R.family.side (d.level+1) d.period)) (μ : ℝ) (orders : V→ℕ)
local notation "D₀" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
local notation "c₀" => ActualOriginalQInitialInput.scales R hG u J A d Q o μ orders
local notation "clock₀" => μ-R.family.S.scale d.cutoff
local notation "Y" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "hL" => Nat.succ_le_of_lt d.below

def submitted (z:tastes D₀) : tastes D₀ := fun i =>
  ⟨c₀ i • (z i).val, ((z i).property.smul (c₀ i)).more (by
    simpa only [mul_one] using WilsonOriginalProjectedCurvatureReader.scale R J hG Q u A d o μ orders i)⟩

omit [Nonempty V] in
theorem scale (z:tastes D₀) :
    testInclusion (ActualRunQlocalNativeTuple.orbit D₀) (submitted R J hG Q u A d o μ orders z) =
      VariableScaling.tests c₀ (testInclusion (ActualRunQlocalNativeTuple.orbit D₀) z) := rfl

abbrev earliest : ℕ := (Finset.univ : Finset (Slot u)).sup (fun s=>R.family.ref s.2.size)

variable (σ:ℝ) (extra:V→ℕ)
local notation "subject" => submitted R J hG Q u A d o μ orders
local notation "previous" => WilsonOriginalScalarGallery.before (X:=tastes D₀)
  (o:=(WilsonOriginalProjectedCurvaturePassport.paper D₀ u).origin) (Γ:=Stock.census V)
  (WilsonOriginalProjectedCurvatureStartingField.lease (R:=R) (p:=d.period) (N:=d.cutoff) hL)
local notation "new" => WilsonOriginalProjectedCurvatureIntake.picture Q D₀ u clock₀ orders d.cutoff σ extra previous
local notation "excluded" => WilsonOriginalProjectedCurvatureIntake.missed Q D₀ u clock₀ orders d.cutoff σ extra
local notation "camp" => QuadraticLocal.Earn.rendered (WilsonOriginalProjectedCurvatureLamps.cohort Q D₀ u clock₀ orders d.cutoff σ extra) (Y).p (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1))
theorem original (ready:earliest R u≤d.level+1) (w:V→ℝ) (hw:∀i,0<w i) (z:tastes D₀)
    (U:Config G (R.family.side (d.level+1) d.period)) :
    (new).density (subject z) U * Poly.pass (excluded (subject z) U) =
      ((ActualOriginalQInitialPreparation.input R hG u J A d Q o μ orders).leaf
        (testInclusion (ActualRunQlocalNativeTuple.orbit D₀) z)).density U := by
  have h (s:Slot u):R.family.ref s.2.size≤d.level+1 :=
    (Finset.le_sup (f:=fun s : Slot u=>R.family.ref s.2.size) (Finset.mem_univ s)).trans ready
  rw [ActualOriginalQInitialPreparation.input_density,←scale R J hG Q u A d o μ orders]
  exact WilsonOriginalProjectedCurvatureStartingField.original Q D₀ u clock₀ orders d.cutoff σ extra hG hL h w hw (subject z) U

theorem accepted (ready:earliest R u≤d.level+1) (w:V→ℝ) (hw:∀i,0<w i) (z:tastes D₀)
    (U:Config G (R.family.side (d.level+1) d.period))
    (pass:∀i,(camp).clear i ∨ Healthy (Y).p.threshold ((camp).ground i) U) :
    (new).density (subject z) U = ((ActualOriginalQInitialPreparation.input R hG u J A d Q o μ orders).leaf
      (testInclusion (ActualRunQlocalNativeTuple.orbit D₀) z)).density U := by
  have e:=original R J hG Q u A d o μ orders σ extra ready w hw z U
  rw [WilsonOriginalProjectedCurvatureIntake.clear Q D₀ u clock₀ orders d.cutoff σ extra (subject z) U pass,
    Next.Rank.Exponential.pass_zero,mul_one] at e
  exact e

end YM.Integration.WilsonOriginalProjectedCurvatureScheduledField
