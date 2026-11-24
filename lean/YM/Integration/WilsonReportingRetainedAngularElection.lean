import YM.Integration.WilsonReportingRetainedMarkedRegister
import YM.Integration.WilsonRootedLightSelection

/-! One before-run appointment for the true upper angular threshold and
the complete original rooted marked sector and local Taylor inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportingRetainedAngularElection
open Function Filter Set Finset Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open PhysicalNext.Repeat.Legato
open WilsonLimitConstruction.FundedCompanySelection
open scoped Classical Topology BigOperators
open WilsonLimitConstruction WilsonReportingForestAngularFare WilsonReportingForestAngularReflection
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric QLocalRequestedSectorCalendar
open WilsonOriginalMarkedExistence PhysicalNext.Repeat.Daisy.Charity.RG12
open Filter RG RG.Supply Precision Org Push.PriceCompiler Lattice
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12 GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
universe u
variable {G : Gauge} {V : Type}

/-- The actual angular threshold for this physical upper stage and patch. -/
def entry (G : Gauge) (B : Stage) (L : Side) (k : ℕ) : ℝ :=
  (eventually_atTop.mp (angular_fare G B L k)).choose

def invoice (G : Gauge) : Prediction G := fun {_} {_} {A} _ =>
  ∀ m n, let a := A.B.a
    entry G (a.params (m+1)) (a.clock.op m n).patch.L (a.clock.op m n).patch.J ≤ a.clock.hatBeta m

theorem prepaid (G : Gauge) : FundedPredictionSupply.AllPrices (@invoice G) := by
  intro s t R E hc programs wages baton hw
  refine ⟨fun _ => 0,?_⟩
  intro l hl D w U register postage scouts protection records rates V quarter
  let Y := ThroughLaunch.raise s l
  let goal (i : ℕ) (x : ℝ) := entry G (Y.profile i) (D.L i) i ≤ x
  obtain ⟨u,_,further,paid⟩ := collect_upper V.betaEntry goal
    (fun i => eventually_ge_atTop (entry G (Y.profile i) (D.L i) i))
  refine ⟨{V with betaEntry:=u},⟨further,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro later after bar wait priced B
  dsimp only
  intro η q E' X J K b covered works divisors m n
  let i := B.a.clock.J (m+1)
  have stage : B.a.params (m+1) = Y.profile i := by
    unfold Levels.params Calendar.params
    rw [B.valid.stage]
  have width : (B.a.clock.op m n).patch.L = D.L i := by
    change B.a.S.block m = D.L i
    rw [← B.a.fits.sameFactor,B.valid.lengths]
  change entry G (B.a.params (m+1)) (B.a.clock.op m n).patch.L i ≤ B.a.clock.hatBeta m
  rw [stage,width]
  exact paid i _ ((after.beta i).trans (B.valid.pays m))

/-- The sector, physical angular forecast and every further submitted
prepayment are bought before the original factor and its family. -/
theorem selected [DecidableEq V] [Fintype V] (simple : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (J : Request V) (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ)
    (more : Prediction G) (offered : FundedPredictionSupply.AllPrices (@more)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (paid : QLocalRequestedSectorCalendar.Paid J (WilsonRootedJointCalendar.scheme G J) extra γ R.kit),
      posted R ∧ more R.kit ∧ WilsonOriginalHighSelection.Salary G R.kit ∧
      Stationary.LightPath R.alloy.B.kin Real.log ∧
      Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay ∧
      Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple ε W ∧ Charged R ∧
      ∀ (Γ : Marker.Census V) (A : NumericSchedule R.family J),
        WilsonRootedLightSelection.Admitted (Γ:=Γ) R A extra γ paid := by
  let sector : Prediction G := @QLocalRequestedSectorCalendar.Paid G V J (WilsonRootedJointCalendar.scheme G J) extra γ
  obtain ⟨R,T,W,⟨paid,angle,other⟩,salary,light,marks,checks,correlations,funded,charged⟩ :=
    WilsonOriginalHighLightRun.selectedWith.{u} WilsonOriginalLogLight.movable simple hε
      (@FundedPredictionSupply.Both G (@sector) (@FundedPredictionSupply.Both G (@invoice G) (@more)))
      (fun s t => FundedPredictionSupply.both
        (QLocalRequestedSectorCalendar.prepaid J (WilsonRootedJointCalendar.scheme G J) extra γ simple hγ s
          (ThroughLaunch.raging s t))
        (FundedPredictionSupply.both (prepaid G s t) (offered s t)))
  exact ⟨R,T,W,paid,angle,other,salary,light,marks,checks,correlations,funded,charged,
    fun Γ A => WilsonRootedLightSelection.onPaid (Γ:=Γ) R A extra γ paid simple⟩

end YM.Integration.WilsonReportingRetainedAngularElection
