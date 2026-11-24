import YM.Integration.WilsonReportingAbsoluteInletSchool
import YM.Integration.WilsonReportingForestAngularReflection

/-! The weak physical detector, its reflected panels, and the exceptional
angular bill of the measured two-date comparison on one original Wilson run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerDisplacedCourse
open PhysicalNext.Repeat.Legato QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open Function Filter Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open WilsonLimitConstruction.FundedCompanySelection WilsonWindowJointPurchase
open WilsonReportingForestAngularFare
open WilsonReportingAbsoluteInletSchool
open scoped Classical

universe u
variable {G : Gauge}

def angular (G : Gauge) : Prediction G := fun {_ _ A} _ =>
  ∀ j n, let P := (A.B.a.clock.op j n).patch
    (eventually_atTop.mp (angular_fare G (A.B.a.params (j+1)) P.L P.J)).choose ≤ A.B.a.clock.hatBeta j

theorem prepaid (G : Gauge) : WilsonFundedWindowMenu.AllPrices (@angular G) := by
  intro s T R E flags C z bt
  refine ⟨fun _ => 0,?_⟩
  intro l hl D w v Z F S pocket P records cost menus V quarter
  let Y := ThroughLaunch.raise s l
  let fare (a : ℕ) := (eventually_atTop.mp (angular_fare G (Y.profile a) (D.L a) a)).choose
  obtain ⟨u,_,hu,paid⟩ := collect_upper V.betaEntry (fun a x => fare a ≤ x)
    (fun a => eventually_ge_atTop (fare a))
  let W : Delays P := {V with betaEntry:=u}
  refine ⟨W,⟨hu,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro V' later bar wait priced B archive origins shape
  dsimp only
  intro η q exchange aux rider booth sheltered works hand j n
  let a := B.a.clock.J (j+1)
  have profile : B.a.params (j+1) = Y.profile a := by
    unfold Levels.params Calendar.params
    rw [B.valid.stage]
  have length : (B.a.clock.op j n).patch.L = D.L a := by
    change B.a.S.block j = D.L a
    rw [←B.a.fits.sameFactor,B.valid.lengths]
  change (eventually_atTop.mp (angular_fare G (B.a.params (j+1)) (B.a.clock.op j n).patch.L a)).choose ≤ _
  rw [profile,length]
  exact paid a _ ((later.beta a).trans (B.valid.pays j))

theorem original (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (U : ℕ → ℕ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      OnRun.{u} cap hG ε (VowsR.probe G MintClock.splits) U
        (@Together G (@WilsonReportColumnSubsidy.Eligible G) (@angular G)) R T W := by
  obtain ⟨V,clear⟩ := MSbar.Heath.vocals G
  exact selected.{u} cap mono hG hε V clear (VowsR.probe G MintClock.splits) le_rfl
    (fun _ _ _ _ _ _ => ⟨0,fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ D =>
      ⟨D,Push.PriceCompiler.DelayLe.refl _,fun _ _ => trivial⟩⟩)
    U _ (fun s M => joint (WilsonReportColumnSubsidy.allPrices s M) (prepaid G s M))

end YM.Integration.WilsonThermometerDisplacedCourse
end
