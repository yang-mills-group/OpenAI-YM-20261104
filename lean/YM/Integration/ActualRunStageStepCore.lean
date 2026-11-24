import YM.Integration.ActualRunSpring
import YM.FVA1.OnLane

/-! The native all-test application to the original Run packet, independent
of the later common-construction funding wrapper. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunStageStep

open Function Filter Set Lattice RG Pressure Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums PhysicalNext PhysicalNext.Repeat RG.Supply Org Roost
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Daisy.Charity.RG12
open YM.ConnectedActivityE6.Blaze.Thermal1020
open YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open UVExtension Spire Orchard Mast Oasis Progress.DirectedRecipe Mallow YM.RG12 OPE
open GridApprox.Nil Marker Merge MergeProof Accent
open YM.Overlay.GapsLocal GapsLocal Full Menu
open UVNext.CouplingReset
open PhysicalNext.Repeat.Legato
open YM.FVA1

variable {G : Gauge} (R : Run G)

private theorem actual_pungent : Pungent R.kit.shape R.alloy.delay :=
  (R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors
    R.makes R.carries R.books).1.wall.hold

/-- Only the two requests not already supplied by the Run's Chateau. -/
def requests (Δ : Decal G) : Decal G :=
  (PhysicalNext.Repeat.FVA1.garrison G).paired ((markerBudget G).paired Δ)

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 2048 in
/-- The generic native supplier uses the actual Spring packet and two
genuine funding receipts.  Its input and output are the original Run Reps. -/
theorem packet_stipend (hG : G.Simple) {N p m : ℕ} {hm : m < N}
    (P : ActualRunSpring.Packet R N p m hm)
    (hMarker : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (hGarrison : Mallow.RG12.Earned (PhysicalNext.Repeat.FVA1.garrison G)
      R.kit.shape R.alloy.delay)
    (hSupport : ∀ i, 100 ≤ (R.alloy.B.a.budget i).supportExponent)
    {a b d : ℕ} (hOrder : Full.target a b d + 1 ≤ R.alloy.B.a.clock.J (m + 1)) :
    StageStep R.family m p N a b d := by
  constructor
  intro T I V _ _ _ _ _ _ _ Γ q C o w f header hL hT hq kX hHeader hA hO hOffer hPositive
  dsimp only
  have hFine := P.fine
  have hCoarse := P.coarse
  have hLabels := (R.makes.wilson.represents N p m hm.le).good.labels
  change (R.family.path.rep N p m).activities.Valid
    (R.family.path.rep N p m).p
    (R.family.path.levels.clock.allowance m)
    (R.family.path.levels.clock.forcedAllowance m) at hLabels
  have hPoint : (R.family.path.rep N p m).p = R.alloy.B.a.budget m :=
    (R.makes.wilson.represents N p m hm.le).vac
  have hRadius : horizonRadius G (R.rolls.L (R.alloy.B.a.clock.J (m + 1)))
      (R.alloy.B.a.clock.hatBeta m) = radius R.family m := by
    unfold radius horizonRadius
    refine congrArg (fun z : ℝ => z ^ YM.ConnectedActivityE6.Blaze.Thermal1020.ray) ?_
    exact (Push.PriceCompiler.beta_eq R.alloy.B.valid m).symm
  have hCoupling : Pert.Asymptotics.regulatorRun R.family N p (m + 1) =
      Vacuum.nativeG (P.input P.point.val).beta := by
    change (Real.sqrt ((R.family.path.rep N p (m + 1)).beta))⁻¹ = _
    rw [P.fine]
  generalize hInput : R.family.path.rep N p (m + 1) = input at *
  cases hFine
  generalize hOutput : R.family.path.rep N p m = output at *
  cases hCoarse
  rw [hPoint]
  have hNative := uncap hG P.spring P.point q w o f header
    (a := a) (b := b) (d := d) C hL hT hq kX hHeader hA
    hMarker (actual_pungent R) hGarrison hm R.b.r (hSupport (m + 1))
    (hSupport m) hOrder hO (by rw [hRadius]; exact hOffer) hPositive
  dsimp only at hNative
  obtain ⟨hk, hkOne, hα, hαOne, hChecks, hInvoice, hRestored, hPush⟩ := hNative
  unfold Full.shadowFactor at hα hαOne hChecks hInvoice hRestored hPush
  rw [hRadius] at hα hαOne hChecks hInvoice hRestored hPush
  let J := (Mallow.houseS P.spring P.point).fragrances
  haveI : Countable J := by
    unfold J YM.ConnectedActivityE6.Cash.fragrances YM.Push.AbsoluteSums.Ursell.Clusters YM.ConnectedActivityE6.Cash.ThinP
    infer_instance
  refine ⟨hk, hkOne, hα, hαOne, J, inferInstance, _, hChecks, hInvoice, ?_, ?_⟩
  · intro hCard
    rw [hCoupling]
    exact hRestored hCard
  · intro x
    exact ⟨hPush x, fun U => Film.quiet hInvoice.format.1 hInvoice.dossier hLabels x U⟩

end YM.Integration.ActualRunStageStep
