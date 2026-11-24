import YM.LocalTaylorR2.Strange.Bayes
import YM.Integration.WilsonLimitConstruction.FundedCensusVacuum

/-! The previously submitted Wilson regular slate descends through the run's actual gauge-door spring at both genuine physical dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorBentHistory
open LocalTaylorR2
open Exponent
open King (overD capping SupplyF)
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Ovens Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open CalendarStep
open Reel Recoil Capstone Strand Rain Roost Mallow PhysicalNext.Repeat.Legato UVExtension Spire Orchard Mast Oasis LocalTaylorR2.Marker
open MergeProof Marker Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF
variable {G : Gauge} (R : Run G)

/-- The measured door of these two actual regulators, including its physically issued transport. -/
structure Head (N per m : ℕ) (hm : m < N) where
  low : ℝ
  high : ℝ
  input : In R.alloy.B.a m per
  spring : Mallow.Spring R.kit N m per low high input
  point : Set.Icc low high
  lower : R.family.path.rep N per m = spring.result point.val
  upper : R.family.path.rep N per (m+1) = input point.val
  door : R.doors N per m hm = duet R.family.path N per m lower upper (sandboxK spring point)

def appointment (N per m : ℕ) (hm : m < N) : Head R N per m hm :=
  Classical.choice (show Nonempty (Head R N per m hm) from by
    obtain ⟨l,k,Q,H,x,lower,upper,door⟩:=R.carries N m per hm
    exact ⟨⟨l,k,Q,H,x,lower,upper,door⟩⟩)

def scroll (p N per m : ℕ) : Reel.Scroll G (R.alloy.B.a.S.side m per) :=
  if hm : m < N then
    let H := appointment R N per m hm
    Strange.forest (Strange.jetEngine G) R.kit H.spring H.point.val (scroll p N per (m+1)) p
  else (R.family.path.rep N per m).activities.E
termination_by N - m

theorem terminal (p N per : ℕ) : scroll R p N per N = (R.family.path.rep N per N).activities.E := by
  rw [scroll,dif_neg (Nat.lt_irrefl _)]

theorem step (p N per m : ℕ) (hm : m < N) :
    let D := appointment R N per m hm
    scroll R p N per m = Strange.forest (Strange.jetEngine G) R.kit D.spring D.point.val
      (scroll R p N per (m+1)) p := by
  rw [scroll,dif_pos hm]

end YM.Integration.WilsonMovingMentorBentHistory
end
