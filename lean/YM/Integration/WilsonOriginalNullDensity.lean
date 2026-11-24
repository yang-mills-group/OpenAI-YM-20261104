import YM.Integration.WilsonOriginalNullFired

/-! A restored scalar density, read on every configuration of the original
return. The hard coefficient uses the same numerical vacuum and its forced
family as the incoming measured course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullDensity
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
    let bulk := Blush.fields K T scale
    ∃ hard : Hard Unit (Ψ i).p (Ψ i).activities.forced (Ψ i).activities.K (fun _ => a0) C₀,
      let F := WilsonMeasuredSingletonForce.row (F:=((Labels.frames G).level d)) hard () ()
      F.Format a0 (hol G) (Ψ i) ∧ F.remBound a0 (Ψ i) divisor (high ^ (-(q:ℝ))) ∧
      (∀ Zc, scale * (Ω).push (Ψ (i+1)).beta (fun V =>
          ((Ψ (i+1)).eval V : ℂ) * masked (Ψ (i+1)).p.threshold X f V) Zc =
          ((Ψ i).eval Zc : ℂ) * (∑' j, masked (Ψ i).p.threshold (scope j) (bulk j) Zc) +
            scale * (fineMass:ℂ) * F.density a0 (localSection G d) (Ψ i) Zc) ∧
      ∃ e : ℕ → ℝ, (∀ j, (Ψ i).p.supBounds a0 (scope j) (bulk j) (e j)) ∧
          SumBudget (fun j => Local.reservedMass (Ψ i).p (scope j) (e j))
            (2 * coinFee G p d L * fineMass) := by
  classical
  intro spring K T scope bulk
  obtain ⟨spr,eqSpr,H,_,hard,_,returns,rows⟩ :=
    WilsonOriginalNullDate.original R π Γ Ψ course start live o X f hf c hc simple way D tab ticket C₀ q ready hjet fund
  subst spr
  refine ⟨H,WilsonMeasuredSingletonForce.format H () () (hol G),?_,?_,?_⟩
  · have hD : 0 < divisor := by
      change 0 < Real.sqrt (Real.exp _)
      exact Real.sqrt_pos.mpr (Real.exp_pos _)
    have nh : 0 ≤ high ^ (-(q : ℝ)) := Real.rpow_nonneg (zero_lt_one.trans (R.alloy.B.a.fits.delayed (i+1))).le _
    have h := WilsonMeasuredSingletonForce.restored (F:=((Labels.frames G).level d)) H () ()
      (fun _ => 1) (fun _ => zero_lt_one) hD nh (by simpa [mul_comm divisor] using hard)
    simpa using h
  · have point := (QuadraticLocal.Advent.later R π Γ Ψ course start live.le).truep.point
    have lawful := (QuadraticLocal.Advent.later R π Γ Ψ course (Nat.le_succ_of_le start) live).truep.valid
    have hk : (Ω).IsKernel (Ψ (i+1)).beta G := (Ω).isKernel (funds_branch K.laws.intake.ready) _
    let w : ℝ := tapW
    have pw : (w:ℂ) ≠ 0 := by exact_mod_cast (inv_pos.mpr fund).ne'
    have undo : (w:ℂ) * (fineMass:ℂ) = 1 := by exact_mod_cast inv_mul_cancel₀ fund.ne'
    intro Zc
    obtain ⟨summable,eqn,reg⟩ := returns Zc
    let Lg := GridRenewal.Rain.fresh (∑' j, Serif.glyph (socket T) K Chi.canonical Set.univ
      (fun _ => w) 0 (fun b => letter C₀ (phase b)) j Zc)
    have scalar := WilsonOriginalNullFired.push Ω (Ψ (i+1)) C₀ lawful hk (socket T false) (socket T true)
      (masked (Ψ (i+1)).p.threshold X f) (fun _ => rfl) (fun _ => rfl) w Zc
    have heard := scalar.symm.trans ((congrArg (fun V : Poly C₀ => V.part (C₀.fire ())) eqn).trans
      (WilsonOriginalNullFired.output H (localSection G d) Zc Lg (GridRenewal.Rain.unwritten _) summable))
    let v : ℂ := (Ψ i).eval Zc
    let r := (WilsonMeasuredSingletonForce.row (F:=((Labels.frames G).level d)) H () ()).density
      a0 (localSection G d) (Ψ i) Zc
    let sum := ∑' j, masked (Ψ i).p.threshold (scope j) (bulk j) Zc
    have hFire : scale * Lg.part (C₀.fire ()) = (w:ℂ) * sum := by
      change scale * Lg.part (C₀.fire ()) = (w:ℂ) * ∑' j, masked (Ψ i).p.threshold (scope j) (bulk j) Zc
      rw [point]
      exact reg
    apply mul_left_cancel₀ pw
    calc
      _ = scale * ((w:ℂ) * (Ω).push (Ψ (i+1)).beta (fun V =>
        ((Ψ (i+1)).eval V : ℂ) * masked (Ψ (i+1)).p.threshold X f V) Zc) := by ring
      _ = scale * (v * Lg.part (C₀.fire ()) + r) := congrArg (scale * ·) heard
      _ = v * (scale * Lg.part (C₀.fire ())) + scale * r := by ring
      _ = (w:ℂ)*(v*sum) + ((w:ℂ)*(fineMass:ℂ))*(scale*r) := by rw [hFire,undo];ring
      _ = _ := by change _ = (w:ℂ)*(v*sum+scale*(fineMass:ℂ)*r);ring
  · rw [(QuadraticLocal.Advent.later R π Γ Ψ course start live.le).truep.point]
    exact rows

end YM.Integration.WilsonOriginalNullDensity
