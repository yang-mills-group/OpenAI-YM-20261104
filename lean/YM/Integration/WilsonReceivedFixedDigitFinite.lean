import YM.Integration.WilsonMarkedFiniteIndependentHistory
import YM.Integration.WilsonReceivedFixedDigitHistory

/-! The independently filed finite Wick recursion on one exact marked itinerary. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedFixedDigitFinite
open Function Filter Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch
open FormalBulk08 Flat Reef Jets Orb Series Next.Free PowerSeries Stationary Lotus Shore
open Work.F03 Work.F05 Work.F08 Mesa Gorge City Cork Rift Lava Kemp Wine Rial Roof Dove
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open PhysicalNext.Repeat.Legato Next.Foundations
open scoped Classical Matrix BigOperators Topology
variable {G:Gauge} {I:Type} [DecidableEq I] {D:I→ℕ}
variable (R:Run G) (u:G.ColorIndex)
local notation "V" => R.family.path.levels


open FormalBulk08.Series WilsonCoeffUV.Blue
variable (tags:∀i n,(FormalBulk08.Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)


open WilsonReceivedFixedDigitHistory (Digits itinerary sound)
open WilsonCoeffUV.Winding (chartIn)
def computed (N:ℕ)(cells:Digits V I)(seed:Outerm G D):
    (days m:ℕ) → (I → Cover) → (S:Finset I) → (Pen D S →L[ℝ] ℝ) → (n:Side) → PChart G n
  | 0,_,x,S,f,n=>(tuftV f (levelsO (seed x) S)).1 n
  | l+1,m,x,S,f,n=>
    let P:=loose V m
    WilsonMarkedFiniteIndependentStep.fixed R u tags N m n
      (computed N cells seed l (m+1) (chartIn P x (cells m)) S f (n*P.L))

theorem original (simple:G.Simple)(price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)
    (k:I→ℕ)(seed:Outerm G D)(well:Wellness k seed)(N:ℕ)(cells:Digits V I)(days m:ℕ)(cut:m+days≤N)
    (x:I → Cover)(S:Finset I)(f:Pen D S→L[ℝ]ℝ)(n:Side):
    (tuftV f (levelsO (itinerary V R.metals.O k N cells days m seed x) S)).1 n=
      computed R u tags N cells seed days m x S f n:=by
  induction days generalizing m x n with
  | zero=>rfl
  | succ d ih=>
    let P:=loose V m
    let y:=chartIn P x (cells m)
    let previous:=itinerary V R.metals.O k N cells d (m+1) seed
    let old:=levelsO (previous y) S
    have hi:m<N:=by omega
    have upper:m+1+d≤N:=by omega
    have paid:=sound V R.metals.O k N cells simple R.alloy.B.ratio seed well d (m+1) upper
    have even:=step_S V R.metals.O m N (previous y) k hi simple R.alloy.B.ratio (paid.level' y)
    have earned:Mer.Auth (mass k S) old:=placedO (previous y) (paid.level' y) S
    change (tuftV f (levelsO (logO V R.metals.O m N (previous y) k) S)).1 n=_
    rw [even]
    change (tuftV f (Mer.verseI V R.metals.O m N (mass k S) old)).1 n=_
    rw [Mer.ply_verse V hi simple R.alloy.B.ratio earned f]
    have step:=WilsonMarkedFiniteIndependentStep.original R u tags simple price funded N m (mass k S) hi
      (tuftV f old) (earned.tuft f) n
    exact step.trans (congrArg (WilsonMarkedFiniteIndependentStep.fixed R u tags N m n) (ih (m+1) upper y (n*P.L)))

end YM.Integration.WilsonReceivedFixedDigitFinite
end
