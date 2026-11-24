import YM.Integration.WilsonOriginalNullBirth
import YM.Integration.WilsonOriginalNullResolved

/-! Complete one-date transfer of a supported null regular atom on the original elected Wilson course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullDate
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
    let T := cloud
    let w := tapW
    let physical := fun Zf => Poly.bead C₀ ((Ψ (i+1)).eval Zf) + Poly.send (C₀.fire ())
        (((w : ℂ) * ((Ψ (i+1)).eval Zf : ℂ)) * masked (Ψ (i+1)).p.threshold X f Zf)
    ∃ spring : Spring R.kit N i per 0 0 (fun _ => Ψ (i+1)),
      spring = (WilsonOriginalNullHouse.original R π Γ Ψ course start live).choose ∧
      let K := houseS spring zeroI
      let log₁ := fun Zc => GridRenewal.Rain.fresh (∑' j, Serif.glyph (socket T) K
        Chi.canonical Set.univ (fun _ => w) 0 (fun b => letter C₀ (phase b)) j Zc)
      ∃ hard : Hard Unit (Ψ i).p (Ψ i).activities.forced (Ψ i).activities.K (fun _ => a0) C₀,
        hard.Paid (fun _ => 1) (Ψ i).p.B (Ψ i).p.supportExponent realCost ∧
        hard.Paid (fun _ => 1) (Ψ i).p.B (Ψ i).p.supportExponent (high ^ (-(q:ℝ)) * divisor) ∧
        (((L).val:ℝ)^d * fineMass * realCost) / divisor ≤
          ((L).val:ℝ)^d * fineMass * high ^ (-(q:ℝ)) ∧
        (∀ Zc, Summable (packet (Ψ i).activities (Ψ i).p (hard.hard ()) Zc) ∧
          (Ω).push (Ψ (i+1)).beta physical Zc = ((Real.exp ((Ψ i).exponent Zc) : ℝ) : ℂ) •
            (Poly.pass (log₁ Zc) * ∑' j, packet (Ψ i).activities (Ψ i).p (hard.hard ()) Zc j) ∧
          scale * (log₁ Zc).part (C₀.fire ()) = (w : ℂ) * ∑' j,
            masked (Pressure.temp (R.alloy.B.a.clock.hatBeta i)) (Blush.scope K T a0 j)
              (Blush.fields K T scale j) Zc) ∧
        ∃ e : ℕ → ℝ,
          (∀ j, (B).supBounds a0 (Blush.scope K T a0 j) (Blush.fields K T scale j) (e j)) ∧
          SumBudget (fun j => Local.reservedMass B (Blush.scope K T a0 j) (e j))
            (2 * coinFee G p d L * fineMass) := by
  intro T w physical
  let spring := (WilsonOriginalNullHouse.original R π Γ Ψ course start live).choose
  obtain ⟨walk⟩ := (WilsonOriginalNullHouse.original R π Γ Ψ course start live).choose_spec
  let K := houseS spring zeroI
  have age : 1 ≤ R.alloy.B.a.clock.J i := by omega
  obtain ⟨_,_,_,allow⟩ := way.frost.license _ _ (step_paid R.alloy.B.a i) 1 (R.alloy.B.a.clock.J i) age le_rfl age
  obtain ⟨eye,_⟩ := Advent.invited R way D tab π Γ Ψ course ticket start live
    (R.alloy.B.a.clock.J i) K (allow _ (R.alloy.B.valid.pays i))
  let M := portraits (socket T)
  have book : brand M () = socket T := funext (fun b => Typeface.photo M () b)
  have hX (b : Bool) : (socket T b).crest = X := by
    have hA := Blush.latch (Ψ (i+1)) o X hf.anchor room
    cases b <;> change ((Ψ (i+1)).activities.reg (Blush.found o X hf.anchor)).support = X <;>
      exact congrArg RG.RegularAddress.support hA
  have hc' (b : Bool) : (socket T b).weight = c := by cases b <;> rfl
  have pledge := WilsonOriginalNullAdmission.registered K eye (socket T) o X c hf.anchor hX hc' fund
    (by norm_num : (Fintype.card Bool : ℝ) ≤ 4)
  have paying := WilsonOriginalNullAdmission.tap C₀ phase small (le_refl 1)
  have placed' := WilsonOriginalNullAdmission.placed (Y:=Ψ i) (S:=Ω) (socket T) o
    (fun b => (hX b).symm ▸ hf.anchor) C₀ phase
  have vac := Advent.later R π Γ Ψ course start live.le
  have positive : ∀ Zc, (Ψ i).eval Zc ≠ 0 := fun Zc => (congr_fun vac.view Zc).symm ▸
    (YM.Multi.AxisShift.chosen_positive R.makes.wilson live.le Zc).ne'
  have law := (course.1.visit i start live).ident
  obtain ⟨hard,bill,full⟩ := WilsonOriginalNullResolved.original K walk eye M () (fun _ => w) pledge
    C₀ (fun b => letter C₀ (phase b)) paying (fun _ => a0) placed'
    (Classical.choice (Tree.select (Ω).ratio (Ω).patch.odd_side)) (Willow.spare_pos _).le law positive
  have charge := Advent.force_bill R way π Γ Ψ course start live ready
  refine ⟨spring,rfl,hard,bill,hard.mono bill charge,?_,?_,?_⟩
  · have hD : 0 < divisor := by
      change 0 < Real.sqrt (R.alloy.B.a.clock.forcedAllowance i)
      exact Real.sqrt_pos.mpr (Real.exp_pos _)
    apply (div_le_iff₀ hD).2
    calc
      _ ≤ ((((L).val:ℝ)^d) * fineMass) * (high ^ (-(q:ℝ)) * divisor) :=
        mul_le_mul_of_nonneg_left charge (mul_nonneg (by positivity) fund.le)
      _ = _ := by ring
  · intro Zc
    have seen := full () Zc
    have identity : TuneR (brand M ()) Set.univ (fun _ => w) 0 (fun b => letter C₀ (phase b)) Ω =
        physical := by
      funext Zf
      rw [book]
      exact WilsonOriginalNullBirth.original R π Γ Ψ course start live o X f hf c hc C₀ w Zf
    have ident : TuneR (socket T) Set.univ (fun _ => w) 0 (fun b => letter C₀ (phase b)) Ω = physical := identity
    exact ⟨seen.2.1,ident ▸ seen.2.2,WilsonOriginalNullComplex.original R Ψ live spring a0 T C₀ w
      (inv_pos.mpr fund).le 1 le_rfl Zc seen.1 scale⟩
  exact WilsonOriginalNullRegular.original R π Γ Ψ course start live spring o X f hf c hc simple hjet

end YM.Integration.WilsonOriginalNullDate
