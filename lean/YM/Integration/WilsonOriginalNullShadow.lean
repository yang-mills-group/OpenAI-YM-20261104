import YM.Integration.WilsonOriginalNullReframe
import YM.Integration.WilsonCenteredDividedRoom

/-! A restored scalar density, read on every configuration of the original
return. The hard coefficient uses the same numerical vacuum and its forced
family as the incoming measured course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullShadow
open Function Filter Set Lattice RG Pressure Tree Wilson Finset MeasureTheory
open PhysicalNext Repeat Legato Graces
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Next.Foundations Labels Peak Mercury
open AllOrder AllOrder.Transit WheelP AllOrder.Floe
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} (R : Run G) {m N per k i d : ℕ}
    (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
    (Ψ : ∀ j, RG.Rep G (R.family.side j per))
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (start : m ≤ i) (live : i < N)
local notation "U" => Ψ (i+1)
local notation "B" => R.alloy.B.a.budget i
local notation "Ω" => R.alloy.B.a.clock.op i per
local notation "L" => R.rolls.L (R.alloy.B.a.clock.J (i+1))
local notation "p" => R.metals.p.profile (R.alloy.B.a.clock.J i)
local notation "room" => QuadraticLocal.Advent.spare R π Γ Ψ course (Nat.le_succ_of_le start) live
local notation "zeroI" => WilsonOriginalNullHouse.point

variable (S : Spring R.kit N i per 0 0 (fun _ => Ψ (i+1)))
    (o : Site (R.family.side (i+1) per)) (X : Support (R.family.side (i+1) per))
    (f : Config G (R.family.side (i+1) per) → ℂ)
    (hf : RegFit (Ψ (i+1)) o 0 (hol G) X f) (c : ℝ) (hc : (Ψ (i+1)).p.supBounds o X f c)
set_option quotPrecheck false
local notation "K0" => houseS S zeroI
local notation "cloud" => float (Ψ (i+1)) o X hf.anchor f c hf.smooth hc (QuadraticLocal.Advent.spare R π Γ Ψ course (Nat.le_succ_of_le start) live)
local notation "a0" => (Ω).ratio.parent o
local notation "scale" => ((L).val : ℂ)^0

open Marker RemainderComparison.Serif WilsonOriginalNullAdmission WilsonOriginalNullComplex
open QuadraticLocal RemainderComparison RemainderComparison.Lyric RemainderComparison.Muse
open RemainderComparison.Typeface RemainderComparison.Serif RemainderComparison.Sleet
open AllOrder.Floe.Step PlanV WheelP Mallow Fusion.Attached
local notation "divisor" => LocalComparison.forcedDivisor R.family i
local notation "fineMass" => (Ψ (i+1)).p.mass X c
local notation "tapW" => (fineMass)⁻¹
local notation "realCost" => Time.quoteHard R.alloy.B.a i R.kit.book (Ψ (i+1)).beta
local notation "high" => R.alloy.B.a.clock.hatBeta (i+1)

include course start live hf hc
theorem original (simple : G.Simple) (way : WayStation R.kit)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (tab : D.Tab R.rolls) (ticket : TicketP R.alloy R.kit D tab)
    (C₀ : Marker.Census Unit) (q : ℕ) (ready : q ≤ R.alloy.B.a.clock.J i)
    (hjet : 3 ≤ R.alloy.B.a.clock.J i) (fund : 0 < fineMass)
    (fit : minSide G d ≤ (R.family.side i per).val) (order : d ≤ (B).order) (power : d ≤ (B).power)
    (hits : Local.hitWidth B * divisor ≤ 1) :
    let T := localSection G d
    let A := hol G
    let display := Next.Foundations.price G (max (B).order (B).power)
    let v := Local.factor A T (B).supportExponent display
    let cap := v * (2 * coinFee G p 0 L * fineMass)
    let exceptional := ‖scale * (fineMass:ℂ)‖ * high ^ (-(q:ℝ))
    ∃ Y : Source.Coefficient ((Labels.frames G).level d) (R.family.side i per),
      Y.Format a0 A (Ψ i) ∧ Y.remBound a0 (Ψ i) divisor (cap+(exceptional+cap)) ∧
      ((Labels.frames G).level d).coeffSize Y.x ≤ cap ∧
      ∀ Zc, Y.density a0 T (Ψ i) Zc =
        scale * (Ω).push (Ψ (i+1)).beta (fun V =>
          ((Ψ (i+1)).eval V : ℂ) * masked (Ψ (i+1)).p.threshold X f V) Zc := by
  classical
  intro T A display v cap exceptional
  let spring := (WilsonOriginalNullHouse.original R π Γ Ψ course start live).choose
  let scope := Blush.scope (houseS spring zeroI) cloud a0
  obtain ⟨old,oldseed,_,oldshape,olddeck,oldfull⟩ :=
    WilsonOriginalNullRaw.original R π Γ Ψ course start live o X f hf c hc simple way D tab ticket C₀ q ready hjet fund
  let M := WilsonOriginalNullReframe.restore ((Labels.frames G).level d) old
  have seed : M.seed=0 := rfl
  have shape := WilsonOriginalNullReframe.format ((Labels.frames G).level d) old oldshape
  have deck := WilsonOriginalNullReframe.budget ((Labels.frames G).level d) old olddeck
  have full Zc := (WilsonOriginalNullReframe.physical ((Labels.frames G).level d) old oldseed a0 scope (Ψ i)
    (localSection G 0) (localSection G d) Zc).trans (oldfull Zc)
  let hold := QuadraticLocal.Advent.later R π Γ Ψ course start live.le
  have point := hold.truep.point
  let doors := (Planned.GuardedAtom.Guard.Keeper.sufficient (QuadraticLocal.Advent.spare R π Γ Ψ course start live.le)).supply
    (fun j => Local.joint T a0 (scope j))
  let Y := Planned.GuardedAtom.Guard.mint doors M A
  have read : Local.Readable A T (Ψ i).p (R.family.side i per) display := by
    rw [point]
    exact Local.foundation_readable G d fit order power
  have hκ : 0 < divisor := by
    change 0 < Real.sqrt (Real.exp _)
    exact Real.sqrt_pos.mpr (Real.exp_pos _)
  have hη : 0 < R.alloy.B.a.clock.forcedAllowance i := Real.exp_pos _
  have hj : Local.hitWidth (Ψ i).p * divisor ≤ 1 := by rw [point];exact hits
  have rev := Planned.GuardedAtom.Deck.usual hη hj read shape (h:=deck)
  have tally : Planned.GuardedAtom.Tare M a0 scope A T (Ψ i) display (R.alloy.B.a.clock.forcedAllowance i)
      divisor cap exceptional cap := by
    convert rev using 1 <;> first | rfl | change Local.factor A T (B).supportExponent display * _ = Local.factor A T (Ψ i).p.supportExponent display * _; rw [point]
  have law := hold.truep.valid
  refine ⟨Y,Planned.GuardedAtom.Guard.usage doors shape law read,?_,?_,?_⟩
  · exact (Planned.GuardedAtom.Guard.tab_mint doors shape law hκ read tally).bound le_rfl
  · have amount := Planned.GuardedAtom.Guard.size_mint doors shape read tally 0
    simpa [Y,M,WilsonOriginalNullReframe.restore] using amount
  · intro Zc
    exact (congrFun (Planned.GuardedAtom.Guard.value_mint doors shape law hκ read tally) Zc).trans (full Zc)

end YM.Integration.WilsonOriginalNullShadow
