import YM.Integration.OriginalCensusTail
import YM.Integration.OriginalInsuredVacuum
import YM.Integration.CensusFusionPrice
import YM.Integration.CensusTailExtraction
import YM.Integration.WilsonLimitConstruction.FundedCensusComparison

/-! Full canonical reset of the actual discarded vacuum cluster at the
requested norm and at the original forced allowance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalCensusFusion

open Filter Lattice Wilson WilsonStartup RG RG.Shoot Marker
open AnalyticBridge VerifiedReset Collection
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG01Estimate RG01Estimate.CensusStep ConnectedActivityE6.Coat Push.SectorMeasure
open IterationFour IterationFour.Vacuum Extra.Iteration
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction.FundedCensusVacuum Pert.Asymptotics
open scoped Topology

variable {G : Gauge} {V : Type} {J : Request V}

/-- One actual physical discarded sector and all its canonical charges. -/
def AtStation (R : Run G) (A : NumericSchedule R.family J) (ε : ℝ)
    (m N per : ℕ) (hN : m < N) : Prop :=
      let S := station R N per m hN
      let L := R.alloy.B.a
      let W := R.alloy.B.kin.path N m
      let U := R.family.path.rep N per (m+1)
      let Y := R.family.path.rep N per m
      let X := ledger R.kit S.guide
      let D := discarded R.kit S.guide S.guide S.identity J.order
      let H := (2*gStep U.beta)^(J.order+1)
      let q := A.outputNorm m
      let charge := ActualNextInheritedPrice.extractionFactor R A m*H
      let Z (b τ : ℝ) := Reset.after W (L.params m).clip q X D b τ 0
      Collection.Local X q D H (hardCost R.kit m) ∧
      charge ≤ ε*regulatorRun R.family N per m^((J.order:ℝ)+1-J.eta) ∧
      (∀ b τ, (Z b τ).Lawful (L.params m).width (L.params m).paths (L.clock.loopCap m)
          charge (L.clock.forcedAllowance m) ∧
        (NativeRequestedInputNorm.regularPayload (Z b τ).activities).Invoice q charge ∧
        (Z b τ).beta = b+Averaging.delta (X.read D) ∧ (Z b τ).v = Collection.vac D τ ∧
        q.threshold^2*|(Z b τ).beta-b| ≤ H ∧ |(Z b τ).v-τ| ≤ H ∧
        ∀ z, (Z b τ).eval z = earlyValue X W (L.params m).clip q D b τ 0 z) ∧
      (∀ (O : Tree.Forest (L.clock.op m per).ratio) b z,
        Y.eval z = (Z b (Song.weighty S.guide Chi.canonical O)).eval z *
          Real.exp (-WilsonLimitConstruction.FundedCensusComparison.action S J.order b z))

/-- The threshold is uniform in the cutoff and torus period. -/
def AtOrder (R : Run G) (A : NumericSchedule R.family J) (ε : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ (N per : ℕ) (hN : m < N), AtStation R A ε m N per hN

/-- The original cash guide, selected before the order, supplies its signed
high cluster with the native hard indices. The actual canonical output
retains the same numerical forced allowance after fusion and the arbitrary
coarse error coefficient, with an exact comparison on every field. -/
theorem realized (R : Run G) (hG : G.Simple)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (horders : ∀ j, j ≤ (R.metals.p.profile j).order ∧ j ≤ (R.metals.p.profile j).power)
    (A : NumericSchedule R.family J)
    (hreserve : J.outputSupport ≤ (R.family.path.levels.budget 0).supportExponent)
    {ε : ℝ} (hε : 0 < ε) : AtOrder R A ε := by
  unfold AtOrder AtStation
  have hgeo := ActualRunReadoutWidth.eventually_geometry R hG hReadout
    J.outputFieldOrder J.outputDistanceOrder J.outputSupport
    J.field_minimum J.distance_minimum J.output_support_pos
  have hprice := CensusFusionPrice.funded R hG A (hgeo.mono fun _ h => h.1.direct)
  have hlevel := R.family.path.levels.fits.deep.eventually_ge_atTop
    (max J.outputFieldOrder J.outputDistanceOrder)
  filter_upwards [paid R hG J.order, CensusTailCost.estimate R hG A hε,
    hgeo,hlevel,hprice] with m hs hbill hwidth hdeep hpaid
  intro N per hN S L W U Y X D H q charge Z
  have ha := hs N per hN
  obtain ⟨ho,hp⟩ := ActualRunFixedOrders.budget_orders R horders m
  have hqo : q.order ≤ (L.budget m).order := (A.output_norm m).order.le.trans
    (((le_max_left _ _).trans hdeep).trans ho)
  have hqp : q.power ≤ (L.budget m).power := (A.output_norm m).distance.le.trans
    (((le_max_right _ _).trans hdeep).trans hp)
  have hqs : q.supportExponent ≤ (L.budget m).supportExponent :=
    (A.output_norm m).reserve.le.trans (hreserve.trans
      (R.family.path.levels.fits.deepExp (Nat.zero_le m)))
  have ht : q.threshold = (L.budget m).threshold := (A.output_norm m).threshold
  have hb : q.B = (L.budget m).B := (A.output_norm m).block
  have hv : Collection.Local X q D H (hardCost R.kit m) :=
    RequestedCensusSource.restrict ha.high ht hb hqo hqp hqs
  have hw0 : 0 ≤ hardCost R.kit m := Cost.nonneg
    (hv.expensive.choose_spec.2 (0 : Site (R.family.side m per)))
  obtain ⟨κ,hr⟩ := hpaid N per hN (hardCost R.kit m) hw0 (CensusFusionRate.original R m)
  have heq : q = ActualRunAdmissionScales.requestedBudget L m J.outputFieldOrder
      J.outputDistanceOrder J.outputSupport J.field_minimum J.distance_minimum J.output_support_pos :=
    ActualRepeatedNorm.norm_unique R.family _ _ _ _ _ _ m q (A.output_norm m)
  have hlevels : L = R.family.path.levels := rfl
  have hc : Decent (L.params m).clip q := ⟨hwidth.1.direct,
    by simpa only [hb,hlevels] using hwidth.1.radius,
    by simpa only [hb,ht,hlevels] using hwidth.1.cut⟩
  have hw : Geo.Width q (L.params m).clip (L.params m).width := heq ▸ hwidth.2
  have hy : R.family.path.Conv N per m := R.makes.wilson.represents N per m hN.le
  have hW : W.Bounds (L.params m).clip (L.params m).width
      (L.params m).paths (L.clock.loopCap m) := by
    rw [show W = Y.path from (CommonConstruction.runAlong_actual_path R N m per hN.le).symm,
      hlevels,← hy.clip]
    exact hy.good.paths
  have hcost : CappedRegularReset.regularNeed G q (L.params m).clip
      (L.params m).width (L.params m).paths 0 H = charge :=
    ActualNextInheritedPrice.regularNeed_linear _ _ _ _ _
  have hclose b τ := CappedCensusFusion.combine hG
    (ActualRunVacuumGermInput.period_room R m per) hW hv hc hw hr b τ
  refine ⟨hv,hbill N per hN,?_,?_⟩
  · intro b τ
    obtain ⟨hl,hev⟩ := hclose b τ
    rw [hcost] at hl
    have hk := CensusTailExtraction.extracted hG hv W (L.params m).clip b τ
    exact ⟨hl,NativeRequestedInputNorm.regular_invoice hl.labels rfl rfl le_rfl le_rfl le_rfl,
      hk.1,hk.2.1,hk.2.2.1,hk.2.2.2,hev⟩
  · intro O b z
    let τ := Song.weighty S.guide Chi.canonical O
    have hz : (Z b τ).eval z = earlyValue X W (L.params m).clip (L.budget m) D b τ 0 z :=
      ((hclose b τ).2 z).trans (OriginalCensusTail.early_zero X W (L.params m).clip D (L.budget m) q ht b τ z)
    exact (WilsonLimitConstruction.FundedCensusComparison.density S hN ha O b z).trans
      (congrArg (fun u : ℝ => u*Real.exp (-WilsonLimitConstruction.FundedCensusComparison.action S J.order b z)) hz.symm)

/-- On the original history the same threshold controls every intervening
step, even with a fixed stopping level and arbitrarily large cutoff. -/
theorem interval (R : Run G) (A : NumericSchedule R.family J) (ε : ℝ) (h : AtOrder R A ε) :
    ∃ first : ℕ, ∀ i N : ℕ, first ≤ i → i ≤ N → ∀ per m : ℕ, i ≤ m →
      ∀ hm : m < N, AtStation R A ε m N per hm := by
  obtain ⟨first,hfirst⟩ := eventually_atTop.1 h
  exact ⟨first,fun i N hi _ per m hm hN => hfirst m (hi.trans hm) N per hN⟩

end YM.Integration.OriginalCensusFusion
end
