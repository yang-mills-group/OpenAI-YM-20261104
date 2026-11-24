import YM.Integration.WilsonMovingSingletonYear
import YM.Integration.WilsonMovingCommonForecasts

/-! Two true signed singleton estimates, for the one planned record and canonical menu on the eventual physical factor. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingSingletonCalendar
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

def Twice {G : Gauge} (a : Ask) : Prediction G := fun {M} {D} {A} F =>
  ∀ x j i, A.delay.betaEntry j ≤ x → StepStages j i → M.p.first ≤ i →
    let Y := fun t => Year (F.recordP j i) (F.menu j i).q (F.prices j i) (M.p.profile i)
      (F.shape.o j i) (F.v j i) x (Solo.raise t j i) (F.span j i) (F.target j i) (D.L j)
    Y F.t ∧ Y (support a M.p.profile M.K)

theorem bought {G : Gauge} (simple : G.Simple) (ask : Ask) (slow : ℝ → ℝ) :
    WilsonMovingCommonPrices.AllPrices ask slow (@WilsonMovingStoredFactor.OnMenu G (@Twice G ask)) := by
  intro s cost targets E charts C v baton wanting wages
  refine ⟨fun _ => 0,?_⟩
  intro l _ upper D w u Z φ S θ record fee V pocket cap
  let strong := support ask s.profile (ThroughLaunch.raging s cost)
  let Y (j i : ℕ) (x : ℝ) (t : Return.Wages) := Year (record j i) Chi.canonical (C j i) (s.profile i)
    (Z.o j i) (v j i) x (Solo.raise t j i) (mile j i) (targets j i) (D.L j)
  have paid (j i : ℕ) (st : StepStages j i) : ∀ᶠ x : ℝ in atTop, s.first ≤ i →
      Y j i x (rays s) ∧ Y j i x strong := by
    by_cases start : s.first ≤ i
    · have low : 0 ≤ rays s j i := by unfold rays; linarith [(s.profile i).price_pos]
      have high : 0 ≤ strong j i := low.trans (le_max_left ..)
      have both (t : Return.Wages) (ht : 0 ≤ t j i) : ∀ᶠ x : ℝ in atTop, Y j i x t :=
        spring _ _ _ _ simple (cap j i st start) (Z.o j i)
          ((by decide : 2 ≤ 6).trans (s.profile i).order_ge) (Solo.raise t j i) (add_nonneg ht zero_le_two)
      exact ((both _ low).and (both _ high)).mono fun _ pair _ => pair
    · exact Eventually.of_forall fun _ h => (start h).elim
  obtain ⟨cut,-,hv,approved⟩ := collect_upper V.betaEntry _ (fun j => eventually_transitions j _ _ (paid j))
  refine ⟨{V with betaEntry:=cut},⟨hv,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro W next bar wait price B light alloy η reset exchange menu aux rider booth shelter works divides fixed x j i hx st start
  have wind : (menu j i).q=Chi.canonical := fixed j i
  dsimp only
  rw [wind]
  exact approved j x ((next.beta j).trans hx) i st start

end YM.Integration.WilsonMovingSingletonCalendar
end
