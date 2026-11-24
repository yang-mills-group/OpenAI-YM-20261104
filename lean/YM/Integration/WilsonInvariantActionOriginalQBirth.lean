import YM.Integration.WilsonReportingPrescribedOldSites
import YM.Integration.WilsonReceivedMarkedForcedSeries
import YM.Integration.WilsonInvariantActionMixedReceived

/-! Exact initialization of the independent original MS source in the same
microscopic marked density, including every compulsory and ordinary mode. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionOriginalQBirth
open Function Filter Finset MeasureTheory Lattice RG Wilson Precision Marker Multi Exterior Tree
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric PhysicalNext.Repeat.Legato Comparison.RG02 Integral
open Source MergeProof.Accent IterationFour IterationFour.Vacuum WilsonLimitConstruction
open Actual Order Push.SectorMeasure QLocalOriginalQHistory
open WilsonReceivedMarkedCofactor WilsonReceivedMarkedForcedSeries
open scoped Topology BigOperators Classical
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V] {B:MS.Local.Physical.Deck G}
  (R:Run G) (simple:G.Simple) (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
local notation "JB" => ActualOriginalQPointSetup.request R u J

omit [Nonempty V] in
private theorem perfect {Γ:Census V} {J':Request V} {A':NumericSchedule R.family J'}
    (d:LocalFormal.Datum R.family Γ) {H:AnalyticInput J' A' d} {η:ℝ} (I:FullPreparedInputAt H η)
    (native:Retained.NativeIntake I) (same:I.carrier.rep=R.family.path.rep d.cutoff d.period (d.level+1))
    (ord:I.regularPrice=0) (force:I.forcedPrice=0)
    (small:R.family.path.levels.clock.forcedAllowance (d.level+1)+
      (Fintype.card V:ℝ)*(forcedDivisor R.family (d.level+1)*I.forcedPrice)≤1)
    (x:IndependentTests J'.tests) (U:Config G (R.family.side (d.level+1) d.period)):
    (I.input.leaf (testInclusion J'.tests x)).density U=
      ManuscriptQLocalActualLog.source R d H (testInclusion J'.tests x) U:=by
  let w:=fun i=>H.inputRadii i/H.kernelCosts i
  have hw i:0<w i:=div_pos (H.input_radius_positive i) (H.kernel_positive i)
  have vanish (a:Poly Γ) (ha:Poly.price w a≤0):a=0:=by
    obtain ⟨M,M0,bound⟩:=Poly.equivalent_norm hw
    exact norm_le_zero_iff.mp ((bound a).trans (mul_nonpos_of_nonpos_of_nonneg ha M0))
  have ordinary:regular R d I x U=0:=vanish _ (by
    simpa only [ord,mul_zero,Real.exp_zero,sub_self] using (price R d I x U).1)
  obtain ⟨_,value,bill⟩:=paid R d I x native small U
  let p:=A'.inputNorm d.level;let row:=entry R d I x U
  let mass:=fun i:ℕ×Finset ℕ=>p.mass (I.carrier.rep.activities.forced i.1).support (Poly.price w (row i))
  have receipt:SumBudget mass 0:=by simpa only [force,mul_zero] using bill
  have nil (i):row i=0:=vanish _ (calc
    Poly.price w (row i)≤ mass i:=p.loMass _ _ (Poly.nonnegative hw _)
    _ ≤ ∑'l,mass l:=receipt.2.1.le_tsum i (fun l _=>receipt.1 l)
    _≤0:=receipt.2.2)
  have compulsory_zero:compulsory R d I x U=0:=by
    rw [value]
    change _ • ∑'i,row i=0
    simp only [nil,tsum_zero,smul_zero]
  apply sub_eq_zero.mp
  rw [split R d I x U,ordinary,compulsory_zero,same]
  simp only [smul_zero,sub_self,zero_smul,add_zero]

theorem original (T:Campaign R)
    (ord:∀k,k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power):
    ∀ᶠ m:ℕ in atTop,∀ (d:LocalFormal.Datum R.family (Stock.census V)),d.level=m→
      ∀b (fine:b≤d.level+1) (parents:V→Site (R.family.side b d.period))
      (residues:V→Site (R.family.S.toDepth fine d.period).count) (Q:MS.Land.Prescription B) (μ:ℝ) (ks:V→ℕ)
      (period:(JB).physicalPeriodLower≤(R.family.S.period d.period).val),d.cutoff=d.level+1→
      let sites:=fun i=>(R.family.S.toDepth fine d.period).assemble (parents i,residues i)
      ∃first:ActualOriginalQInitialInput.start R simple u J A ord≤d.level,
      let H:=ActualOriginalQInitialInput.input R simple u J A d Q sites μ ks ord first period
      ∃I:FullPreparedInputAt H 0,Origin R simple u J A d Q sites μ ks I ∧ Retained.NativeIntake I ∧
        ∀x:IndependentTests (JB).tests,∀U,(I.input.leaf (testInclusion (JB).tests x)).density U=
          ManuscriptQLocalActualLog.source R d H (testInclusion (JB).tests x) U:=by
  filter_upwards [WilsonReportingPrescribedOldSites.original R simple u J A T ord,
    eventually_retained_forced_smallness (V:=V) R.family simple (JB).forcedConstant] with m sold small
  intro d eq b fine parents residues Q μ ks period cut sites
  obtain ⟨first,I,native,same,reg,force,origin⟩:=sold d eq b fine parents residues Q μ ks period cut
  exact ⟨first,I,origin,native,perfect R d I native same reg force (eq▸small I.forcedPrice I.forced_bound)⟩

end YM.Integration.WilsonInvariantActionOriginalQBirth
