import YM.Integration.WilsonMovingMentorAffine
import YM.Integration.WilsonMovingMentorSpec
import YM.Integration.WilsonMovingMentorLodgePrice

/-! The selected Wilson hierarchy has a single nominated root and covariance
table satisfying all five original plan conditions on the measured physical archive. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorSpecRun
universe u
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy
open MergeProof LocalLTE
open scoped Topology BigOperators Classical
open RGLocalTaylor RGLocalTaylor.Laminate
open WilsonLimitConstruction WilsonLimitConstruction.FundedPredictionSupply WilsonGaussianDeterminantTender
open PhysicalNext.Repeat.Daisy.Charity.RG12 WilsonLimitConstruction.FundedCompanySelection
open WilsonOriginalMarkedExistence GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonMovingCourseElection (Course)
theorem original (ask : WilsonMovingShadowPrices.Ask) {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
    (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V) (χ : Chi) (δ : Charity.RG12.Decal G)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ)
    (ρ : WilsonLongContactSectorProtection.Premium G J.outputFieldOrder)
    (grant : WilsonLongContactSectorProtection.Admitted J ρ)
    (other rider : Prediction G) (funds : FundedPredictionSupply.AllPrices (@other))
    (ticket : WilsonMovingMentorOwnership.AllPrices ask Real.log
      (@WilsonMovingStoredFactor.OnMenu G (@rider))) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
      (affine : ManuscriptQLocalCofinalAffineFields.Paid R)
      (paid : QLocalRequestedSectorCalendar.Paid J (joined G J χ δ) extra γ R.kit),
      Course.{u} ask hG ε J extra γ ManuscriptQLocalCofinalAffineFields.schedule R T W affine.1 ∧
      ManuscriptQLocalScalarProgramSelection.ConditionalJetsOn R ∧
      (∀ through, ∃ first, WilsonRootedPhysicalSpringAffineRows.After R affine through first) ∧
      WilsonGaussianDeterminantTender.On R J χ δ extra γ paid ∧
      RG01Estimate.Chart.Barrier R.alloy (fun _ _=>1) ∧
      Juniper.Mulberry.Lanterns R.kit.shape R.alloy.delay ∧
      WilsonMovingSensorReserve.Extra R.kit ∧ WilsonVacuumPreResetRenderCalendar.Issued R.kit ∧
      RG01Estimate.Chart.Barrier R.alloy (fun _ i => ((i:ℝ)+1)⁻¹) ∧ WilsonRootedPhysicalBright.Eligible R.kit ∧
      WilsonRootedPhysicalCommonCut.Eligible R.kit ∧ WilsonVacuumPreResetCurvatureReserve.Issued R.kit ∧
      WilsonVacuumPreResetPrecursorReserve.Issued R.kit ∧ WilsonRootedHeldAffineWallet.Eligible R.kit ∧ other R.kit ∧
      Extension.UV.Archive R.alloy.B ∧ (∃ f, RankCovariance.ShapePort R.alloy.B.a R.alloy.B.M f) ∧
      WilsonMovingMentorSalary.Admitted ask R.kit ∧ WilsonMovingMentorPhase.Canonical R.kit ∧
      WilsonLongContactSectorProtection.Paid J (joined G J χ δ) extra γ ρ R.kit ∧ WilsonMovingMentorSpec.Filed R.kit ∧ rider R.kit := by
  let additional : Prediction G := @Both G (@WilsonMovingMentorSpec.Filed G) (@rider)
  have offer := WilsonMovingMentorUnion.together ask Real.log (WilsonMovingMentorSpec.paid hG ask Real.log) ticket
  obtain ⟨R,T,W,affine,paid,physical,jets,fields,det,chart,derivatives,sensor,render,times,
    bright,short,upper,lower,leaf,ordinary,archive,shape,salary,phase,protection,matriculation⟩ :=
      WilsonMovingMentorAffine.original ask hG hε J χ δ extra γ hγ ρ grant (@other) (@additional) funds offer
  exact ⟨R,T,W,affine,paid,physical,jets,fields,det,chart,derivatives,sensor,render,times,
    bright,short,upper,lower,leaf,ordinary,archive,shape,salary,phase,protection,matriculation.1,matriculation.2⟩

/-- At the actual temperature of every Wilson step, one unchanged covariance
table supplies the original covariance income and the rooted analytic prices. -/
theorem on_clock {G : Gauge} (R : Run G) (filed : WilsonMovingMentorSpec.Filed R.kit) :
    ∃ (r : AllOrder.Floe.Step.PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
      (Q : r.Tab R.rolls),
      (∀ m, let j := R.alloy.B.a.clock.J (m+1)
            let i := R.alloy.B.a.clock.J m
            let x := R.alloy.B.a.clock.hatBeta m
            r.Rise j (R.rolls.L j).val ∧
            AllOrder.Floe.Step.PlanV.Roots.Lease R.rolls r Q j i x ∧
            AllOrder.Floe.Step.PlanV.Roots.Cresting r i x ∧
            AllOrder.Shop.Summit R.rolls R.kit.shape (fun _ i => AllOrder.Shop.edgeW i) i j x) ∧
      Extension.UV.Archive R.alloy.B ∧ ∃ f, RankCovariance.ShapePort R.alloy.B.a R.alloy.B.M f := by
  obtain ⟨r,Q,paid⟩ := filed
  refine ⟨r,Q,?_,paid.terra,paid.triad⟩
  intro m
  have due := R.alloy.B.valid.pays m
  have step := step_paid R.alloy.B.a m
  exact ⟨paid.rentsK _,paid.bear.due _ _ step _ due,paid.bear.cream _ _ step _ due,
    paid.ladder.terms _ _ due _ step⟩

theorem measured {G : Gauge} (R : Run G) (simple : G.Simple) (filed : WilsonMovingMentorSpec.Filed R.kit)
    {a ε : ℝ} (ha : 0 ≤ a) (positive : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N per, m < N →
      WilsonMovingMentorLodgePrice.amount R N per m ≤ ε*(Pert.Asymptotics.regulatorRun R.family N per (m+1))^a := by
  obtain ⟨r,Q,plan⟩ := filed
  exact WilsonMovingMentorLodgePrice.measured R simple AllOrder.Shop.edgeW plan.ladder ha positive

section
open AllOrder.Floe.Step
variable {G : Gauge} (R : Run G) (m : ℕ)
local notation "j₁" => R.alloy.B.a.clock.J (m+1)
local notation "i₀" => R.alloy.B.a.clock.J m

/-- The chosen table funds the actual incoming card, at the same scale as the
physical step. Its original `Bears` bounds include the rank-two issue. -/
theorem on_card {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    (Q : r.Tab R.rolls) (paid : PlanV.Spec r Q R.alloy R.kit)
    (k : ℕ) (hj : 4 ≤ j₁) (hk : k+2 ≤ i₀) (card : PlanV.Card R.rolls r j₁ i₀ hj k) :
    PlanV.Income.Bears R.rolls r j₁ i₀ hj
      (Q.income j₁ i₀ hj (step_paid R.alloy.B.a m) k hk ⟨card⟩) (R.alloy.B.a.clock.hatBeta m) :=
  paid.bear.due j₁ i₀ (step_paid R.alloy.B.a m) _ (R.alloy.B.valid.pays m)
    hj (step_paid R.alloy.B.a m) k hk ⟨card⟩
end

end YM.Integration.WilsonMovingMentorSpecRun
end
