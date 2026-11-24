import YM.Integration.WilsonOriginalNullCarrier

/-! A restored scalar density, read on every configuration of the original
return. The hard coefficient uses the same numerical vacuum and its forced
family as the incoming measured course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullRaw
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
    (hf : RegFit (Ψ (i+1)) o d (hol G) X f) (c : ℝ) (hc : (Ψ (i+1)).p.supBounds o X f c)
set_option quotPrecheck false
local notation "K0" => houseS S zeroI
local notation "cloud" => float (Ψ (i+1)) o X hf.anchor f c hf.smooth hc (QuadraticLocal.Advent.spare R π Γ Ψ course (Nat.le_succ_of_le start) live)
local notation "a0" => (Ω).ratio.parent o
local notation "scale" => ((L).val : ℂ)^d

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
    (hjet : d+3 ≤ R.alloy.B.a.clock.J i) (fund : 0 < fineMass) :
    let spring := (WilsonOriginalNullHouse.original R π Γ Ψ course start live).choose
    let K := houseS spring zeroI
    let T := cloud
    let scope := Blush.scope K T a0
    ∃ M : Local.Raw ((Labels.frames G).level d) (R.family.side i per),
      M.seed = 0 ∧ M.bulk = Blush.fields K T scale ∧ M.Format a0 scope (Ψ i) ∧
      Planned.GuardedAtom.Deck M a0 scope (Ψ i) divisor (2 * coinFee G p d L * fineMass)
        (‖scale * (fineMass:ℂ)‖ * high ^ (-(q:ℝ))) ∧
      ∀ Zc, M.eval a0 scope (localSection G d) (Ψ i) Zc =
        scale * (Ω).push (Ψ (i+1)).beta (fun V =>
          ((Ψ (i+1)).eval V : ℂ) * masked (Ψ (i+1)).p.threshold X f V) Zc := by
  classical
  intro spring K T scope
  obtain ⟨H,_,cost,reads,paid⟩ :=
    WilsonOriginalNullDensity.original R π Γ Ψ course start live o X f hf c hc simple way D tab ticket C₀ q ready hjet fund
  have addr := latch (Ψ (i+1)) o X hf.anchor room
  have crest : T.live.crest = X := by
    change ((Ψ (i+1)).activities.reg (found o X hf.anchor)).support = X
    rw [addr]
  have inside : a0 ∈ T.live.crest.image (Ω).ratio.parent :=
    crest.symm ▸ Finset.mem_image.mpr ⟨o,hf.anchor,rfl⟩
  have fmt := (Blush.bookbag simple live spring zeroI T a0 scale
    (localSection G d) R.b.r inside).1
  have p₁ := (QuadraticLocal.Advent.later R π Γ Ψ course start live.le).truep.point
  have p₂ := ((spring.moves simple live).2 zeroI (zeroI).property).1.bundle.point
  have shape (j : ℕ) : (Ψ i).p.Regular (scope j) (Blush.fields K T scale j) := by
    rw [p₁,←p₂]
    exact fmt.regular j
  let M := WilsonOriginalNullCarrier.raw (F:=((Labels.frames G).level d)) H (Blush.fields K T scale) (scale*(fineMass:ℂ))
  refine ⟨M,rfl,rfl,?_,?_,?_⟩
  · exact (WilsonOriginalNullCarrier.original H _ (scale*(fineMass:ℂ)) (hol G) scope divisor
      _ _ fmt.origin shape paid cost).1
  · exact (WilsonOriginalNullCarrier.original H _ (scale*(fineMass:ℂ)) (hol G) scope divisor
      _ _ fmt.origin shape paid cost).2
  · intro Zc
    exact (WilsonOriginalNullCarrier.read H _ _ (localSection G d) scope Zc).trans (reads Zc).symm

end YM.Integration.WilsonOriginalNullRaw
