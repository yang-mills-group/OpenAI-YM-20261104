import YM.Integration.WilsonLimitConstruction.FundedPhysicalReceiving
import YM.Integration.WilsonLimitConstruction.FundedCanonicalCalibration
import YM.Integration.WilsonLimitConstruction.FundedCoverPredictionRatio

/-! The incoming analytic and physical data are issued together at the measured
beta and the exact paid discrepancy, before any next marked probe is chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedCoverStepPrice
open Filter Lattice Wilson RG Marker MeasureTheory
open PhysicalNext.Repeat.Legato Comparison.RG02 IterationFour IterationFour.Vacuum
open RG3.Script.Picnic LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.PreRun.SuccessiveRequests FundedCoverKineticMeasurement
open scoped Topology Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {J : Request V}
    (R : Run G) {A : NumericSchedule R.family J} {K : NumericPrices A}
    {d : LocalFormal.Datum R.family Γ} {caps : Handoff.OutputCapacities}
    {F : AnalyticInput J A d} {η : ℝ}
    {I : FullPreparedInputAt F η}

structure Receipt (M : FundedPhysicalCatalogue.Purchase caps K F)
    (S : FundedRenderedBank.Chosen K I M.toCatalogue)
    (P : FundedRenderedBank.Canonical S) (r : ℕ) {m : ℕ} (hm : d.level=m+1)
    (A' : NumericSchedule R.family (nextRequest J caps r))
    (W : Bulk.Colors Γ G (R.family.side (m+1) d.period))
    (x : Exterior.fieldDir G (R.family.side m d.period) 1) (q : ℕ) where
  analytic : AnalyticInput (nextRequest J caps r) A' (ActualNextLocalDatum.descend d hm W x)
  shared : FundedCanonicalReceiving.Attached R S r hm analytic
  physical : FullPreparedInputAt analytic (FundedCanonicalCalibration.charge R P (A'.inputNorm m))
  carrier : HEq physical.carrier P.bank.output.carrier
  marked : HEq physical.input P.bank.output.output
  residual : HEq physical.prepared.remainder P.bank.output.residual
  inherited : physical.inherited = FundedCanonicalInputPayload.errorPrice R I K
  ordinary : physical.regularPrice = Retained.ordinaryRate K I 1
  forced : physical.forcedPrice = Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)^q
  intake : 0 ≤ η → Retained.NativeIntake I → Retained.ordinaryRate K I 1 ≤ 1 →
    Retained.NativeIntake physical

/-- The measured ratio, the finite-copy packet cost, and the exact native
calibration are discharged on the same cofinal set of scales. -/
theorem eventually_issued_with_radii (hG : G.Simple) (hR : ActualRunNativeComponentRecipe.Attached R)
    (caps : Handoff.OutputCapacities) (A : NumericSchedule R.family J) (K : NumericPrices A) :
    ∀ᶠ l : ℕ in atTop, ∀ (d : LocalFormal.Datum R.family Γ), d.level = l →
    ∀ (Y : Bulk.Chain R.family.path) (F : AnalyticInput J A d) (η : ℝ)
      (I : FullPreparedInputAt F η) (M : FundedPhysicalCatalogue.Purchase caps K F)
      (_contact : Tested R Y F M hG (fun v => (0 : (J.tests v).Mood))) (S : FundedRenderedBank.Chosen K I M.toCatalogue)
      (P : FundedRenderedBank.Canonical S) (r m : ℕ) (hm : d.level=m+1)
      (A' : NumericSchedule R.family (nextRequest J caps r))
      (W : Bulk.Colors Γ G (R.family.side (m+1) d.period))
      (x : Exterior.fieldDir G (R.family.side m d.period) 1)
      (width : ℕ→ℝ), FundedPhysicalCatalogue.Width width M →
      A'.inputNorm m=A.outputNorm d.level → width d.level=A'.inputWidth m →
      (4:ℝ)^J.order*K.geometry d.level ≤ A'.admittedCost m →
      ActualNextAnalyticInput.Eligibility R.family J m →
      AnalyticBridge.VerifiedReset.Geo.Width (A.outputNorm d.level)
        (R.family.path.levels.params d.level).clip (R.family.path.levels.params d.level).width →
      FundedCanonicalInputPayload.errorPrice R I K ≤ J.inheritedConstant *
        Pert.Asymptotics.regulatorRun R.family d.cutoff d.period d.level ^
          ((J.order:ℝ)+1-J.eta) →
      ∀ q : ℕ, FundedRenderedBank.Bounds K I M.toCatalogue P.bank 1 q →
        Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)^q ≤ J.forcedConstant →
        ∃ Q : Receipt R M S P r hm A' W x q,Q.analytic.outputRadii = (fun v=>F.outputRadii v / A'.radiusLoss m) := by
  filter_upwards [FundedCoverPredictionRatio.actual_ratio R hG hR (R := Γ) caps A K,
    ActualRunInterpolatedPackets.onRun_paid_eventually caps.packetPower R hG (by norm_num : (0:ℝ)<1)]
    with l hratio hcopy
  intro d hl Y F η I M contact S P r m hm A' W x width H hn hw hc eligible hgeo hi q bound hf
  subst l
  have hratio := hratio d rfl Y F M contact
  have hcap : S.bank.output.model.powerCap ≤ caps.packetPower := by
    rw [S.bank.same_model]
    exact M.power_bounded
  have hPaid := H.paid
  have copy := hcopy d.cutoff d.period d.below S.bank.output.model hcap r
    (by simpa only [S.bank.same_model] using hPaid)
  have htwo : (1+(1:ℝ))=2 := by norm_num
  rw [htwo] at copy
  obtain ⟨F',shared,radii⟩ := FundedPhysicalReceiving.attachedWithOutput R M S r hm A' W x width H
    hn hw hc hratio.2.1 hratio.2.2 copy eligible
  obtain ⟨C,hC⟩ := FundedCanonicalCalibration.measured R P (A'.inputNorm m) hn hgeo
  obtain ⟨L,hcar,hmark,hres,hinh,hord,hforce,hintake⟩ :=
    FundedCanonicalReceiving.prepare R S P r hm F' shared hn hG hgeo M.output_layers_paid
      C hC hi q bound hf (FundedPhysicalReceiving.read R M S P r)
  exact ⟨⟨F',shared,L,hcar,hmark,hres,hinh,hord,hforce,hintake⟩,radii⟩

theorem eventually_issued (hG : G.Simple) (hR : ActualRunNativeComponentRecipe.Attached R)
    (caps : Handoff.OutputCapacities) (A : NumericSchedule R.family J) (K : NumericPrices A) :
    ∀ᶠ l : ℕ in atTop, ∀ (d : LocalFormal.Datum R.family Γ), d.level = l →
    ∀ (Y : Bulk.Chain R.family.path) (F : AnalyticInput J A d) (η : ℝ)
      (I : FullPreparedInputAt F η) (M : FundedPhysicalCatalogue.Purchase caps K F)
      (_contact : Tested R Y F M hG (fun v => (0 : (J.tests v).Mood))) (S : FundedRenderedBank.Chosen K I M.toCatalogue)
      (P : FundedRenderedBank.Canonical S) (r m : ℕ) (hm : d.level=m+1)
      (A' : NumericSchedule R.family (nextRequest J caps r))
      (W : Bulk.Colors Γ G (R.family.side (m+1) d.period))
      (x : Exterior.fieldDir G (R.family.side m d.period) 1)
      (width : ℕ→ℝ), FundedPhysicalCatalogue.Width width M →
      A'.inputNorm m=A.outputNorm d.level → width d.level=A'.inputWidth m →
      (4:ℝ)^J.order*K.geometry d.level ≤ A'.admittedCost m →
      ActualNextAnalyticInput.Eligibility R.family J m →
      AnalyticBridge.VerifiedReset.Geo.Width (A.outputNorm d.level)
        (R.family.path.levels.params d.level).clip (R.family.path.levels.params d.level).width →
      FundedCanonicalInputPayload.errorPrice R I K ≤ J.inheritedConstant *
        Pert.Asymptotics.regulatorRun R.family d.cutoff d.period d.level ^
          ((J.order:ℝ)+1-J.eta) →
      ∀ q : ℕ, FundedRenderedBank.Bounds K I M.toCatalogue P.bank 1 q →
        Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)^q ≤ J.forcedConstant →
        Nonempty (Receipt R M S P r hm A' W x q) := by
  filter_upwards [eventually_issued_with_radii (Γ:=Γ) R hG hR caps A K] with l purchased
  intro d hl Y F η I M contact S P r m hm A' W x width H hn hw hc eligible hgeo hi q bound hf
  obtain ⟨Q,_⟩ := purchased d hl Y F η I M contact S P r m hm A' W x width H hn hw hc eligible hgeo hi q bound hf
  exact ⟨Q⟩

end YM.Integration.WilsonLimitConstruction.FundedCoverStepPrice
end
