import YM.Integration.WilsonMovingSingletonCalendar

/-! The actual target wages and analytic rates required by the original Beaming and Mentor courses. -/

noncomputable section
namespace YM.Integration.WilsonMovingMentorTuition
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

/-- The two original tuition tests on the same submitted target, together with its full
additional structural support salary. All three are known before any block length. -/
theorem before {s : Sheet G} {cost : MapPrices} (ask : Ask) {targets : Targets s cost}
    (E : Expenses targets) (wanting : ∀ j i,(E j i).wanting=-(7/16:ℝ))
    (wage : ∀ j i,(E j i).earn=WilsonMovingShadowPrices.earn ask s.profile cost j i) (j i : ℕ) :
    3/8 + (targets j i).rate < 0 ∧
    (s.profile i).supportExponent + 1 + 1 < (targets j i).exp ∧
    ask s.profile cost j i + 9 < (targets j i).exp := by
  have rate := (E j i).reach
  rw [wanting] at rate
  have gross := (E j i).worth
  have room : support ask s.profile cost j i ≤ (E j i).earn := by
    rw [wage]
    exact le_max_right _ _
  have ordinary := le_trans (le_max_left _ _ : (s.profile i).supportExponent + 3 ≤
    support ask s.profile cost j i) room
  have added := le_trans (le_max_right _ _ : ask s.profile cost j i + 9 ≤
    support ask s.profile cost j i) room
  have one := (E j i).first
  have two := (E j i).second
  constructor
  · linarith
  constructor <;> linarith

def Exposures {G : Gauge} (ask : Ask) : Prediction G := fun {M} {_} {_} F =>
  ∀ j i, 3/8 + (F.target j i).rate < 0 ∧
    (M.p.profile i).supportExponent + 1 + 1 < (F.target j i).exp ∧
    ask M.p.profile M.K j i + 9 < (F.target j i).exp

/-- The original double singleton lease and the before-block mentor tuition are purchased on
the same factor and the same original target. -/
theorem paired {G : Gauge} (simple : G.Simple) (ask : Ask) (slow : ℝ → ℝ) :
    WilsonMovingCommonPrices.AllPrices ask slow (@WilsonMovingStoredFactor.OnMenu G
      (@FundedPredictionSupply.Both G (@WilsonMovingSingletonCalendar.Twice G ask) (@Exposures G ask))) := by
  intro s cost targets E charts C v baton wanting wage
  have rooms := before ask E wanting wage
  obtain ⟨u,buy⟩ := WilsonMovingSingletonCalendar.bought simple ask slow s cost targets E charts C v baton wanting wage
  refine ⟨u,?_⟩
  intro l le upper D w U Z φ S θ p fee V pocket cap
  obtain ⟨Y,floor,full⟩ := buy l le upper D w U Z φ S θ p fee V pocket cap
  refine ⟨Y,floor,?_⟩
  intro Y hy K I marked B light alloy η q E' X J K' b hZ hc hm hq
  exact ⟨full Y hy K I marked B light η q E' X J K' b hZ hc hm hq,rooms⟩

end YM.Integration.WilsonMovingMentorTuition
end
