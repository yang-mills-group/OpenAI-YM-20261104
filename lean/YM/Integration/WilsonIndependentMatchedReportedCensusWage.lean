import YM.Integration.WilsonIndependentMatchedPhysicalReportedPeer
/-! Buy every retained and discarded part of a mixed physical return at its
own submitted measured directions before picking its cutoff or geometry. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedReportedCensusWage
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentMatchedPhysicalReportedFilm (sponsors)
open WilsonIndependentFittedRosterCash (numerical)
open WilsonIndependentMatchedPhysicalReportedPeer (measured reserve)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonIndependentFittedMixedCash (embed)
open WilsonIndependentFittedRosterFilms (Vote factor)
open WilsonIndependentMatchedFittedSeat (dose)
open scoped BigOperators Classical
variable {G:Gauge}{n k u e:ℕ}
local notation "I" => Fin (n+1)
local notation "CC" => Credit.leanC

def Enrolled (R:Run G)(l d:I→ℕ)(admit:∀i,l i<d i)(own:∀i,Rails (l i) k u e)
    (floor:ℕ)(B J:I→Credit):Prop:=
  let Q:=deck (G:=G) l d admit
  let L:=R.family.path.levels
  ∀(m K N:ℕ),floor ≤ m → m ≤ K → K ≤ N →
  ∀X:∀i,CutsP (hol G) (Q i).ans (Q i).path (own i) CC CC CC CC,
    (∀i,(X i).ax=L ∧ (X i).tx=R.metals.O ∧ (X i).N=N ∧ (X i).m=m) →
  ∀{a:ℕ}(leg:Fin (a+1) → I)(mask:Fin (a+1) → Bool)(q:ℕ)(g:ℝ),q ≤ e →
  let data:=sponsors (Q:=Q ∘ leg) (v:=fun i=>own (leg i)) (fun i=>X (leg i)) mask
  numerical q g data ≤ ∏i,measured (Q (leg i)) (X (leg i)) q g (B (leg i)) m L (mask i) ∧
  WilsonIndependentFittedRosterCash.reserve q data ≤ ∏i,reserve (X (leg i)) q (J (leg i)) (mask i)

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (l d:I→ℕ)(admit:∀i,l i<d i)(own:∀i,Rails (l i) k u e):
    ∃B J:I→Credit,∀ᶠ floor:ℕ in atTop,Enrolled R l d admit own floor B J:=by
  let Q:=deck (G:=G) l d admit
  have earn i:=WilsonIndependentMatchedPhysicalReportedPeer.original R simple v funded (admit i) (own i)
  choose B J booked using earn
  refine ⟨B,J,?_⟩
  filter_upwards [Filter.eventually_all.2 booked] with floor quote
  intro m K N early mk live X filed a leg mask q g dep data
  have charged s:=quote (leg s) m K N early mk live (X (leg s)) (filed _).1 (filed _).2.1
    (filed _).2.2.1 (filed _).2.2.2 q g dep (mask s)
  constructor
  · exact Finset.prod_le_prod (fun _ _=>sum_nonneg fun _ _=>norm_nonneg _) (fun s _=>(charged s).1)
  · apply Finset.prod_le_prod _ (fun s _=>(charged s).2)
    intro z _
    exact sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _

end YM.Integration.WilsonIndependentMatchedReportedCensusWage
