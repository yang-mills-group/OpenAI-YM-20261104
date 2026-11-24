import YM.Integration.WilsonReportingPrescribedOldMicroscopic
import YM.Integration.WilsonReportingPrescribedOldRawForecast

/-! Constant unit moods on each independent inserted arm. The spatial
profile is an external signed test of the actual original products. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldUnitProbes
open Filter Function Finset Lattice Wilson RG Source Marker Precision
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato
open IterationFour IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 QLocalVacuumOrderRestriction AnalyticBridge.VerifiedReset.Averaging
open WilsonLimitConstruction Pert.Asymptotics ActualRunInterpolatedPackets QLocalMarkedCouplingDifference
open RG3.Script.Picnic ComparisonDensity.Address MergeProof.Accent
open scoped Classical BigOperators
variable {V : Type}

def test (D : V→Orbit) : IndependentTests D := fun i=>⟨fun _=>1,by
  refine ⟨zero_le_one,contDiff_const,?_⟩
  intro k hk x hx
  cases k with
  | zero =>
    simp only [norm_iteratedFDeriv_zero,norm_one,mul_one,Orbit.height]
    exact one_le_pow₀ (by linarith [norm_nonneg x])
  | succ k =>
    rw [iteratedFDeriv_succ_const]
    simpa only [Pi.zero_apply,norm_zero,mul_one] using ((D i).sky x).le⟩

variable {G : Gauge} [DecidableEq V] [Fintype V] [Nonempty V] {B : MS.Local.Physical.Deck G}
  (R : Run G) (hG : G.Simple) (u : V→MS.Rake.Label B) (J : Request V)
  (d : LocalFormal.Datum R.family (Stock.census V)) (Q : MS.Land.Prescription B)
  (o : V→Site (R.family.side (d.level+1) d.period)) (μ : ℝ) (ks : V→ℕ)
local notation "JB" => ActualOriginalQPointSetup.request R u J
local notation "D" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
local notation "t₀" => μ-R.family.S.scale d.cutoff

def word (s : (Stock.census V).Mode) (W : Config G (R.family.side (d.level+1) d.period)) : ℂ :=
  ∏i∈s.val,ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) (t₀)
    (R.family.side (d.level+1) d.period) (o i) W (ks i)

/-- The original point protocol reads one on every slot at each of the
actual independent insertion sites. Every lower correction is retained. -/
theorem original (ref : ActualOriginalQLayout.referenceLevel R u ≤ d.level+1)
    {j : ℕ} (live : j ≤ d.level+1)
    (t : IndependentTests (JB).tests) (eq : HEq (testInclusion (JB).tests (test _)) (testInclusion (JB).tests t))
    (s : (Stock.census V).Mode) (U : Config G (R.family.side j d.period)) :
    (((R.family.path.rep d.cutoff d.period j).eval U)⁻¹ • gust R.family.path d.cutoff d.period (d.level+1)
      (WilsonReportingPrescribedOldRawForecast.raw R hG u J d Q o μ ks t) j live U).part s =
      actualTransport R.family (N:=d.cutoff) (word R u d Q o μ ks s) live U := by
  have trans := WilsonReportingPrescribedOldMicroscopic.original R Q (D) u (t₀) ks hG d.below
    (ActualOriginalQLayout.reference_le R u ref) (testInclusion (JB).tests t) live s U
  have equal := eq_of_heq eq
  refine trans.trans ?_
  apply congrArg (fun f=>actualTransport R.family (N:=d.cutoff) f live U)
  funext W
  unfold ActualStartupNormalizedQ.modeObservable word
  apply prod_congr rfl
  intro i _
  have read : ActualRunQlocalNativeTuple.reader (D) i (testInclusion (JB).tests t i)=1 := by
    rw [←equal]
    exact ActualOriginalQPointDatum.reader_eq R d.period (d.level+1) o (fun v=>(J.tests v).D) (fun _=>0) i _
  have site : ActualRunQlocalNativeTuple.root (D) i=o i :=
    ActualOriginalQPointDatum.root_eq R d.period (d.level+1) o (fun v=>(J.tests v).D) (fun _=>0) i
  rw [read,site,one_mul]

end YM.Integration.WilsonReportingPrescribedOldUnitProbes
