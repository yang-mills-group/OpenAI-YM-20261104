import YM.Integration.WilsonLimitConstruction.FundedCensusVacuum
import YM.Integration.RequestedCensusSource
import YM.Integration.CensusTailCost
import YM.Integration.ActualRunVacuumNorm
import YM.Integration.ActualRunReadoutWidth
import YM.Integration.ActualRunFixedOrders

/-! The actual signed discarded cluster, all of its original forced labels,
and its scalar/kinetic extraction at a fixed requested output norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalCensusTail

open Filter Lattice Wilson WilsonStartup RG RG.Shoot Marker
open AnalyticBridge VerifiedReset Collection
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG01Estimate RG01Estimate.CensusStep ConnectedActivityE6.Coat Push.SectorMeasure
open IterationFour IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction.FundedCensusVacuum Pert.Asymptotics
open scoped Topology

variable {G : Gauge} {V : Type} {J : Request V}

/-- The zero-alpha pre-reset factor has exactly its old density on every
field when the true physical threshold is unchanged. -/
theorem early_zero {n : Side} (X : Listing G n) (P : PathData G) (c : Clip)
    (v : Source G n) (p q : BudgetPoint) (ht : q.threshold = p.threshold)
    (β τ : ℝ) (z : Config G n) :
    earlyValue X P c q v β τ 0 z = earlyValue X P c p v β τ 0 z := by
  have h := ActualRunVacuumNorm.eval_same_threshold (frozen X P c p v β τ) q p ht
  simpa only [earlyValue, frozen, neg_zero, zero_mul, Real.exp_zero, mul_one] using congrFun h z

/-- For every later cutoff and every period, the live cash guide's actual
signed tail pays the fixed output invoice with any positive coefficient at
the requested coarse exponent. The retained factor and the original forced
rows are recorded on all fields. -/
theorem realized (R : Run G) (hG : G.Simple)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (horders : ∀ j, j ≤ (R.metals.p.profile j).order ∧ j ≤ (R.metals.p.profile j).power)
    (A : NumericSchedule R.family J)
    (hreserve : J.outputSupport ≤ (R.family.path.levels.budget 0).supportExponent)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ m : ℕ in atTop, ∀ (N per : ℕ) (hN : m < N),
      let S := station R N per m hN
      let L := R.alloy.B.a
      let U := R.family.path.rep N per (m+1)
      let Y := R.family.path.rep N per m
      let X := ledger R.kit S.guide
      let D := discarded R.kit S.guide S.guide S.identity J.order
      let K := kept R.kit S.guide S.guide S.identity J.order
      let H := (2*gStep U.beta)^(J.order+1)
      let force := Real.sqrt (L.clock.forcedAllowance m)*H
      let q := A.outputNorm m
      let charge := ActualNextInheritedPrice.extractionFactor R A m*H
      Collection.Local X q D H force ∧
        charge ≤ ε*regulatorRun R.family N per m^((J.order:ℝ)+1-J.eta) ∧
        (∀ τ : ℝ, let T := VacuumGermReset.shell Y.path (L.params m).clip q X D U.beta τ 0
          let Z := Reset.after Y.path (L.params m).clip q X D U.beta τ 0
          T.Lawful (L.params m).width (L.params m).paths (L.clock.loopCap m) charge force ∧
          (NativeRequestedInputNorm.regularPayload Z.activities).Invoice q charge) ∧
        (∀ (O : Tree.Forest (L.clock.op m per).ratio) z,
          Y.eval z = earlyValue X Y.path Y.clip (L.budget m) K U.beta
            (Song.weighty S.guide Chi.canonical O) (R.alloy.B.kin.alpha N m) z *
              Real.exp (-((X.read D).additive q z))) := by
  have hgeo := ActualRunReadoutWidth.eventually_geometry R hG hReadout
    J.outputFieldOrder J.outputDistanceOrder J.outputSupport
    J.field_minimum J.distance_minimum J.output_support_pos
  have hlevel := R.family.path.levels.fits.deep.eventually_ge_atTop
    (max J.outputFieldOrder J.outputDistanceOrder)
  filter_upwards [resolution R hG J.order, CensusTailCost.estimate R hG A hε,
    hgeo, hlevel] with m hr hprice hwidth hdeep
  intro N per hN S L U Y X D K H force q charge
  obtain ⟨hsource, hrecord⟩ := hr N per hN
  obtain ⟨ho, hp⟩ := ActualRunFixedOrders.budget_orders R horders m
  have hqo : q.order ≤ (L.budget m).order :=
    (A.output_norm m).order.le.trans (((le_max_left _ _).trans hdeep).trans ho)
  have hqp : q.power ≤ (L.budget m).power :=
    (A.output_norm m).distance.le.trans (((le_max_right _ _).trans hdeep).trans hp)
  have hqs : q.supportExponent ≤ (L.budget m).supportExponent :=
    (A.output_norm m).reserve.le.trans (hreserve.trans
      (R.family.path.levels.fits.deepExp (Nat.zero_le m)))
  have ht : q.threshold = (L.budget m).threshold := (A.output_norm m).threshold
  have hb : q.B = (L.budget m).B := (A.output_norm m).block
  have hlocal : Collection.Local X q D H force :=
    RequestedCensusSource.restrict hsource ht hb hqo hqp hqs
  refine ⟨hlocal, hprice N per hN, ?_, ?_⟩
  · intro τ T Z
    have hq : q = ActualRunAdmissionScales.requestedBudget L m
        J.outputFieldOrder J.outputDistanceOrder J.outputSupport J.field_minimum
        J.distance_minimum J.output_support_pos :=
      ActualRepeatedNorm.norm_unique R.family _ _ _ _ _ _ m q (A.output_norm m)
    have hlevels : L = R.family.path.levels := rfl
    have hc : Decent (L.params m).clip q :=
      ⟨hwidth.1.direct, by simpa only [hb, hlevels] using hwidth.1.radius,
        by simpa only [hb, ht, hlevels] using hwidth.1.cut⟩
    have hw : Geo.Width q (L.params m).clip (L.params m).width := hq ▸ hwidth.2
    have hy : R.family.path.Conv N per m := R.makes.wilson.represents N per m hN.le
    have hpath : Y.path.Bounds (L.params m).clip (L.params m).width
        (L.params m).paths (L.clock.loopCap m) := by
      rw [hlevels, ← hy.clip]
      exact hy.good.paths
    have hl := CappedRegularReset.lawful hG
      (ActualRunVacuumGermInput.period_room R m per) hpath hlocal hc hw U.beta τ 0
    have he : CappedRegularReset.regularNeed G q (L.params m).clip (L.params m).width
        (L.params m).paths 0 H = charge := ActualNextInheritedPrice.regularNeed_linear _ _ _ _ _
    rw [he] at hl
    exact ⟨hl, (RequestedCensusSource.after Y.path (L.params m).clip q X D U.beta τ hl.labels).1⟩
  · intro O z
    have hact : (X.read D).additive q z = (X.read D).additive (L.budget m) z :=
      RequestedCensusSource.action (X := X) (v := D) ht z
    exact (hrecord O z).trans (congrArg (fun a : ℝ =>
      earlyValue X Y.path Y.clip (L.budget m) K U.beta (Song.weighty S.guide Chi.canonical O)
        (R.alloy.B.kin.alpha N m) z * Real.exp (-a)) hact.symm)

end YM.Integration.OriginalCensusTail
end
