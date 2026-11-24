import YM.Integration.WilsonOriginalSignedForestAperture
import YM.Integration.ManuscriptQLocalPrepared
import YM.Integration.WilsonLimitConstruction.FundedIndependentTestScaling

/-! The complete received marked density and its signed inherited discrepancy
on the same original aperture, with all Haar and branch weights retained. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalSignedReceivedForest
open Function Filter Finset MeasureTheory Lattice RG Wilson Precision Marker Multi Exterior Tree
open RG3.Forms RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric PhysicalNext.Repeat.Legato Comparison.RG02 Integral Actual Order
open Push.SectorMeasure WilsonCoeffUV WilsonCoeffUV.Fk WilsonLimitConstruction WilsonOriginalSignedForestAperture
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι] {Γ : Census ι}
variable (R : Run G) {J : Request ι} {U : NumericSchedule R.family J}
    (d : LocalFormal.Datum R.family Γ) {H : AnalyticInput J U d} {η : ℝ}
    (I : FullPreparedInputAt H η) (hi : Retained.NativeIntake I) (x : TestSpace J.tests)
set_option quotPrecheck false in
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
set_option quotPrecheck false in
local notation "P₁" => R.family.path.rep d.cutoff d.period (d.level+1)
set_option quotPrecheck false in
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
set_option quotPrecheck false in
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
set_option quotPrecheck false in
local notation "Z" => (I.input.leaf x).density
set_option quotPrecheck false in
local notation "W" => ManuscriptQLocalActualLog.source R d H x

include hi in
private theorem incoming : Leaf.All (Z) ∧ GaugeInvariant (Z) := by
  obtain ⟨w,hw,y,hy⟩ := FundedIndependentTestScaling.represent x
  have A := ManuscriptQLocalPrepared.input R d I hi y
  let P := (I.input.leaf (testInclusion J.tests y)).density
  have same (U) (s : Γ.Mode) : ((Z) U).part s = envelopeProduct w s • (P U).part s := by
    change ((I.input.leaf x).density U).part s = envelopeProduct w s •
      ((I.input.leaf (testInclusion J.tests y)).density U).part s
    rw [hy,FundedIndependentTestScaling.restore I.input I.multilinear w hw x U s]
  refine ⟨fun s=>?_,fun k U=>?_⟩
  · rw [show (fun u=>((Z) u).part s)=(fun u=>envelopeProduct w s • (P u).part s) from funext (same · s)]
    obtain ⟨c,hc⟩ := (A.1 s).cost
    exact ⟨(A.1 s).meas.const_smul (envelopeProduct w s),‖envelopeProduct w s‖*c,
      fun u=>by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hc u) (norm_nonneg _)⟩
  · ext s
    rw [same (Lattice.gauge k U),same U]
    exact congrArg (fun a : Poly Γ => envelopeProduct w s • a.part s) (A.2 k U)

def reading (F : Forest (Δ).ratio) (A : (Δ).Choices→Set (F.Slice G))
    (V : Config G (R.family.side d.level d.period)) :=
  ∑ t : (Δ).Choices,column F t (A t) (P₁).beta V (Z)

include hi in
theorem original (F : Forest (Δ).ratio) (A : (Δ).Choices→Set (F.Slice G))
    (V : Config G (R.family.side d.level d.period)) :
    let H₀ := repeatF (Δ)
    let A' := fun t => Profiles.reroute F H₀ G '' A t
    let seen := reading R d I x F A V
    let filed := reading R d I x H₀ A' V
    seen=filed ∧ Extra.Trajectories.connected (((P₀).eval V)⁻¹ • seen)=
      Extra.Trajectories.connected (((P₀).eval V)⁻¹ • filed) := by
  intro H₀ A' seen filed
  have eq : seen=filed := by
    apply Finset.sum_congr rfl
    intro t _
    exact WilsonOriginalSignedForestAperture.change F H₀ t (A t) (P₁).beta V (Z)
      (incoming R d I hi x).2 (R.family.path.levels.blocks d.level d.period).branches
  exact ⟨eq,congrArg (fun b=>Extra.Trajectories.connected (((P₀).eval V)⁻¹ • b)) eq⟩

omit [Fintype ι] in
private theorem subcolumn {c f : Side} {S : StepData c f} (F : Forest S.ratio) (t : S.Choices)
    (A : Set (F.Slice G)) (ha : MeasurableSet A) (β : ℝ) (V : Config G c)
    {C D : Lit Γ (Config G f)} (hc : Leaf.All C) (hd : Leaf.All D)
    (hb : S.patch.Branches S.kernel G) :
    column F t A β V (C-D)=column F t A β V C-column F t A β V D := by
  unfold column
  rw [←sub_cost ((good_slice F t V β hb hc).on_window ha) ((good_slice F t V β hb hd).on_window ha)]
  apply congrArg (charge (F.order G))
  funext a
  by_cases h : a∈A <;> simp [h,Function.comp_apply,stack,smul_sub]

include hi in
theorem discrepancy (F : Forest (Δ).ratio) (A : (Δ).Choices→Set (F.Slice G))
    (closed : ∀ t,MeasurableSet (A t)) (V : Config G (R.family.side d.level d.period)) :
    reading R d I x F A V - WilsonOriginalSignedForestAperture.reading R d H x F A V =
      ∑ t : (Δ).Choices,column F t (A t) (P₁).beta V (fun U =>
        Poly.pass (H.packets.read x (g) U) * ((I.prepared.remainder.leaf x).density U -
          ((P₁).eval U : ℂ) • (1:Poly Γ))) := by
  unfold reading WilsonOriginalSignedForestAperture.reading
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [←subcolumn F t (A t) (closed t) (P₁).beta V (incoming R d I hi x).1
    (ManuscriptQLocalActualLog.floor R d H x).safe (R.family.path.levels.blocks d.level d.period).branches]
  apply congrArg (column F t (A t) (P₁).beta V)
  funext U
  exact ManuscriptQLocalActualLog.inherited R d H x I U

end YM.Integration.WilsonOriginalSignedReceivedForest
