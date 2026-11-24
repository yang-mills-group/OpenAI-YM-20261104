import YM.Integration.WilsonLimitConstruction.FundedCoverKineticWindow
import YM.Integration.WilsonLimitConstruction.FundedCoverStepPrice

/-! The recovered signed successor enters the original retained grant at the
single fixed flat calibration purchased before all of its later models. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedCoverFlatStep
open Filter Lattice Wilson RG Marker MeasureTheory
open PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch Comparison.RG02
open IterationFour IterationFour.Vacuum RG3.Script.Picnic
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.PreRun.SuccessiveRequests FundedPhysicalCatalogue FundedCoverKineticMeasurement OriginalRunConstruction
open scoped Topology Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {J : Request V}

def extendCalibration {n : Side} {B : Rep G n} {p : BudgetPoint} {s t : ℝ}
    (C : CalibrationPresentation B p s) (h : s≤t) : CalibrationPresentation B p t :=
  { C with
    size_nonnegative := C.size_nonnegative.trans h
    regular_total x := ⟨(C.regular_total x).1,(C.regular_total x).2.1,(C.regular_total x).2.2.trans h⟩
    full_hit x := ⟨(C.full_hit x).1,(C.full_hit x).2.1,(C.full_hit x).2.2.trans h⟩ }

def rebook {C : Family G} {A : NumericSchedule C J} {d : LocalFormal.Datum C Γ}
    {F : AnalyticInput J A d} {s t : ℝ} (I : FullPreparedInputAt F s) (h : s≤t) :
    FullPreparedInputAt F t :=
  { I with calibration := extendCalibration I.calibration h, exponent := I.exponent }

variable (R : Run G) {A : NumericSchedule R.family J} {K : NumericPrices A}
    {d : LocalFormal.Datum R.family Γ} {caps : Handoff.OutputCapacities}
     {F : AnalyticInput J A d} {η : ℝ}
    {I : FullPreparedInputAt F η}
    {M : FundedPhysicalCatalogue.Purchase caps K F}
    {S : FundedRenderedBank.Chosen K I M.toCatalogue}
    {P : FundedRenderedBank.Canonical S} {m r q : ℕ} {hm : d.level=m+1}
    {A' : NumericSchedule R.family (nextRequest J caps r)}
    {W : Bulk.Colors Γ G (R.family.side (m+1) d.period)}
    {x : Exterior.fieldDir G (R.family.side m d.period) 1}

structure Accepted (Q : FundedCoverStepPrice.Receipt R M S P r hm A' W x q) where
  input : FullPreparedInputAt Q.analytic
    (FundedCoverKineticWindow.next R caps A K (Γ := Γ) d.cutoff d.period m)
  carrier : HEq input.carrier P.bank.output.carrier
  marked : HEq input.input P.bank.output.output
  residual : HEq input.prepared.remainder P.bank.output.residual
  inherited : input.inherited = FundedCanonicalInputPayload.errorPrice R I K
  regular : input.regularPrice = Retained.ordinaryRate K I 1
  forced : input.forcedPrice = Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)^q
  intake : 0 ≤ η → Retained.NativeIntake I → Retained.ordinaryRate K I 1 ≤ 1 →
    Retained.NativeIntake input

theorem funded (hG : G.Simple) (hR : ActualRunNativeComponentRecipe.Attached R)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (caps : Handoff.OutputCapacities) (A : NumericSchedule R.family J) (K : NumericPrices A) :
    ∀ᶠ m : ℕ in atTop, ∀ (d : LocalFormal.Datum R.family Γ) (hm : d.level=m+1)
      (Y : Bulk.Chain R.family.path) (F : AnalyticInput J A d) (η : ℝ)
      (I : FullPreparedInputAt F η) (M : FundedPhysicalCatalogue.Purchase caps K F)
      (_contact : Tested R Y F M hG (fun v => (0 : (J.tests v).Mood))) (S : FundedRenderedBank.Chosen K I M.toCatalogue)
      (P : FundedRenderedBank.Canonical S) (r : ℕ)
      (A' : NumericSchedule R.family (nextRequest J caps r))
      (W : Bulk.Colors Γ G (R.family.side (m+1) d.period))
      (x : Exterior.fieldDir G (R.family.side m d.period) 1) (q : ℕ)
      (Q : FundedCoverStepPrice.Receipt R M S P r hm A' W x q),
      A'.inputNorm m=A.outputNorm d.level →
      η ≤ (Currency.g R.family d.cutoff d.period (d.level+1))^2 →
      I.carrier.rep.eval = (R.family.path.rep d.cutoff d.period (d.level+1)).eval →
      Nonempty (Accepted R Q) := by
  filter_upwards [FundedCoverKineticWindow.dominates R caps A K (Γ := Γ)
      hG hR hReadout] with m paid
  intro d hm Y F η I M contact S P r A' W x q Q hn small fine
  let s : FundedCoverKineticWindow.Sample R caps A K (Γ := Γ) d.cutoff d.period (m+1) :=
    ⟨d,rfl,rfl,hm,Y,F,η,I,M,fun _ => contact,S,P,small,fine⟩
  have h : FundedCanonicalCalibration.charge R P (A'.inputNorm m) ≤
      FundedCoverKineticWindow.next R caps A K (Γ := Γ) d.cutoff d.period m := by
    rw [hn]
    exact paid d.cutoff d.period s
  let L := rebook Q.physical h
  exact ⟨⟨L,Q.carrier,Q.marked,Q.residual,Q.inherited,Q.ordinary,Q.forced,
    fun hη hI ho => by
      obtain t := Q.intake hη hI ho
      exact ⟨t.original,t.reserved,t.ordinary_nonnegative,t.ordinary_small⟩⟩⟩

end YM.Integration.WilsonLimitConstruction.FundedCoverFlatStep
end
