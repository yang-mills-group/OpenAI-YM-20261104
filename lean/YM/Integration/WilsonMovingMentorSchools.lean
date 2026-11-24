import YM.Integration.WilsonMovingMentorTuition
import YM.QuadraticLocal.View
import YM.QuadraticLocal.Mentor.Rated

/-! Both original before-length schools on the chosen factor, at its actual family of target wages.
The two true courses select their floors before any roll or physical period. -/

noncomputable section
namespace YM.Integration.WilsonMovingMentorSchools
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply
open Push.PriceCompiler ThroughLaunch Height Opera Roof Roost
open Progress.DirectedRecipe Time WilsonStartup Extra.Histories Next.Foundations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
variable {G : Gauge}

open WilsonMovingShadowPrices (Ask support)
open Brim.WilsonMovingSingleton (Year spring)
open FullVolume WilsonLimitConstruction

def Courses {G : Gauge} : Prediction G := fun {M} {_} {_} F =>
  QuadraticLocal.Beaming.Freq F.target M.p.floorL ∧ QuadraticLocal.Mentor.Institute F.target M.p.floorL

def Admitted {G : Gauge} (a : Ask) : Prediction G := fun {_} {_} {_} F =>
  WilsonMovingSingletonCalendar.Twice a F ∧ WilsonMovingMentorTuition.Exposures a F ∧ Courses F

theorem bought {G : Gauge} (simple : G.Simple) (ask : Ask) (slow : ℝ → ℝ) :
    WilsonMovingCommonPrices.AllPrices ask slow (@WilsonMovingStoredFactor.OnMenu G (@Admitted G ask)) := by
  intro s cost targets E charts C v baton wanting wage
  have rate := WilsonMovingMentorTuition.before ask E wanting wage
  obtain ⟨freq,small⟩ := QuadraticLocal.Beaming.orbit targets (fun j i _ => (rate j i).1)
    (fun j i _ => (rate j i).2.1)
  obtain ⟨institute,salaries⟩ := QuadraticLocal.Mentor.leases targets (fun j i _ => (rate j i).1)
    (fun j i _ => (rate j i).2.1)
  obtain ⟨u,buy⟩ := WilsonMovingMentorTuition.paired simple ask slow s cost targets E charts C v baton wanting wage
  refine ⟨(u ⊔ freq) ⊔ institute,?_⟩
  intro l hl upper D w U Z φ S θ p fee V pocket cap
  obtain ⟨before,inst⟩ := sup_le_iff.mp hl
  obtain ⟨first,fr⟩ := sup_le_iff.mp before
  obtain ⟨Y,floor,full⟩ := buy l first upper D w U Z φ S θ p fee V pocket cap
  refine ⟨Y,floor,?_⟩
  intro Y hy K I marked B light alloy η q E' X J K' b hZ hc hm hq
  obtain ⟨income,margin⟩ := full Y hy K I marked B light η q E' X J K' b hZ hc hm hq
  refine ⟨income,margin,?_,?_⟩
  · intro j i st L cap
    exact small j i st L ((fr j).trans cap)
  · intro j i st L cap
    exact salaries j i st L ((inst j).trans cap)

end YM.Integration.WilsonMovingMentorSchools
end
