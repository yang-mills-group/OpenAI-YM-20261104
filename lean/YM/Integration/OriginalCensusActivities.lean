import YM.Integration.CenteredCensusVacuum
import YM.Integration.SignedCensusActivities
import YM.Integration.OriginalForcedFlat

/-! The actual signed hard gas, healthy-field action and their locally
booked charges along the original finite-volume physical history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalCensusActivities

open Filter Lattice Wilson WilsonStartup RG RG.Shoot Marker
open AnalyticBridge VerifiedReset Collection
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG01Estimate RG01Estimate.CensusStep ConnectedActivityE6.Coat Push.SectorMeasure
open IterationFour IterationFour.Vacuum Extra.Iteration UVNext.CouplingReset
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction.FundedCensusVacuum Pert.Asymptotics
open scoped Topology

variable {G : Gauge} {V : Type} {J : Request V}

def Physical (R : Run G) (A : NumericSchedule R.family J) (ε ρ : ℝ) (r : ℕ)
    (m N per : ℕ) (hN : m < N) : Prop :=
  let S := station R N per m hN
  let L := R.alloy.B.a
  let Y := R.family.path.rep N per m
  let X := ledger R.kit S.guide
  let D := discarded R.kit S.guide S.guide S.identity J.order
  let b := Y.beta - Averaging.delta (X.read D)
  let q := A.outputNorm m
  let Z := CenteredCensusVacuum.record Y (Reset.after (R.alloy.B.kin.path N m)
    (L.params m).clip q X D b 0 0)
  let f := WilsonLimitConstruction.FundedCensusComparison.action S J.order b
  let H := (2*gStep (R.family.path.rep N per (m+1)).beta)^(J.order+1)
  let charge := ActualNextInheritedPrice.extractionFactor R A m*H
  let price := ρ*regulatorRun R.family N per m^r
  charge ≤ ε*regulatorRun R.family N per m^((J.order:ℝ)+1-J.eta) ∧
    L.clock.forcedAllowance m ≤ price ∧
    Y.activities.KBound Y.p price ∧ Z.activities.KBound Z.p price ∧
    Z.Lawful (L.params m).width (L.params m).paths (L.clock.loopCap m) charge
      (L.clock.forcedAllowance m) ∧
    (NativeRequestedInputNorm.regularPayload Z.activities).Invoice q charge ∧
    (∀ z, Y.eval z = Z.eval z * Real.exp (-(f z-f 1)) ∧
      Y.activities.gas Y.p z = Z.activities.gas Z.p z *
        Real.exp (Y.activities.additive Y.p z-Z.activities.additive Z.p z-(f z-f 1))) ∧
    (∀ z, flags Y.p.threshold z = ∅ →
      f z-f 1 = Y.activities.additive Y.p z-Z.activities.additive Z.p z ∧
        |f z-f 1| ≤ sites (R.family.side m per)*(L.clock.allowance m+charge))

theorem station (R : Run G) (A : NumericSchedule R.family J) (ε ρ : ℝ) (r : ℕ)
    (m N per : ℕ) (hN : m < N) (hs : OriginalCensusFusion.AtStation R A ε m N per hN)
    (hforce : R.family.path.levels.clock.forcedAllowance m ≤ ρ*regulatorRun R.family N per m^r) :
    Physical R A ε ρ r m N per hN := by
  unfold Physical
  intro S L Y X D b q Z f H charge price
  have hyn : R.family.path.Conv N per m := R.makes.wilson.represents N per m hN.le
  obtain ⟨hcharge,hC⟩ := CenteredCensusVacuum.atStation R A ε m N per hN hs
  obtain ⟨hv,hb,hw,hc,_,ht,hZ,hI,hrep⟩ := hC Y.beta
  obtain ⟨O⟩ := Tree.select (L.clock.op m per).ratio (L.clock.op m per).patch.odd_side
  have he : ∀ z, Y.eval z = Z.eval z * Real.exp (-(f z-f 1)) := (hrep O).2
  refine ⟨hcharge,hforce,OriginalForcedFlat.weaken _ _ hyn.good.labels.boundK hforce,
    OriginalForcedFlat.weaken _ _ hZ.labels.boundK hforce,hZ,hI,fun z => ⟨he z,?_⟩,
    fun z hz => ?_⟩
  · exact SignedCensusActivities.gas Y Z hv hb hw hc ht (fun z => f z-f 1) he z
  · exact SignedCensusActivities.healthy Y Z hv hb hw hc ht hyn.good.labels.boundE
      hZ.labels.boundE (fun z => f z-f 1) he z hz

/-- One stopping threshold per finite request, hard order and tolerance,
before every cutoff, period and intermediate native representative. -/
theorem interval (R : Run G) (hG : G.Simple) (A : NumericSchedule R.family J) (ε : ℝ)
    (h : OriginalCensusFusion.AtOrder R A ε) (r : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ first : ℕ, ∀ i N : ℕ, first ≤ i → i ≤ N → ∀ per m : ℕ, i ≤ m →
      ∀ hN : m < N, Physical R A ε ρ r m N per hN := by
  have hboth := h.and (OriginalForcedFlat.allowance R hG r hρ)
  obtain ⟨first,hfirst⟩ := eventually_atTop.1 hboth
  refine ⟨first,fun i N hi _ per m hm hN => ?_⟩
  obtain ⟨hs,hf⟩ := hfirst m (hi.trans hm)
  exact station R A ε ρ r m N per hN (hs N per hN) (hf N per hN.le)

end YM.Integration.OriginalCensusActivities
end
