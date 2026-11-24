import YM.Integration.WilsonOriginalNullSeries

/-! A restored scalar density, read on every configuration of the original
return. The hard coefficient uses the same numerical vacuum and its forced
family as the incoming measured course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullFamily
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

include course start live in
/-- Sum all original rooted null rows on their unchanged upper and lower
physical representations, with a single charged true receiving hard family. -/
theorem original (simple : G.Simple) (way : WayStation R.kit)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (tab : D.Tab R.rolls) (ticket : TicketP R.alloy R.kit D tab) (C₀ : Marker.Census Unit)
    (ready : WilsonOriginalNullContraction.Ready R i d)
    (feet : ℕ → Support (R.family.side (i+1) per)) (rows : ℕ → Config G (R.family.side (i+1) per) → ℂ)
    (cost : ℕ → ℝ) (a : ℝ) (expenses : SumBudget (fun j => (Ψ (i+1)).p.mass (feet j) (cost j)) a)
    (specs : ∀ j, RegFit (Ψ (i+1)) o d (hol G) (feet j) (rows j))
    (bounds : ∀ j, (Ψ (i+1)).p.supBounds o (feet j) (rows j) (cost j)) :
    ∃ Y : Source.Coefficient ((Labels.frames G).level d) (R.family.side i per),
      Y.Format a0 (hol G) (Ψ i) ∧ Y.remBound a0 (Ψ i) divisor (Doors.rate L*a) ∧
      ((Labels.frames G).level d).coeffSize Y.x ≤ (Doors.rate L*a)/3 ∧
      ∀ W, Y.density a0 (localSection G d) (Ψ i) W =
        scale * (Ω).push (Ψ (i+1)).beta (fun V => ((Ψ (i+1)).eval V : ℂ) *
          ∑' j, masked (Ψ (i+1)).p.threshold (feet j) (rows j) V) W := by
  classical
  choose each shape pay size read using fun j => WilsonOriginalNullContraction.original R π Γ Ψ course start live o
    (feet j) (rows j) (specs j) (cost j) (bounds j) simple way D tab ticket C₀ ready
  let F := (Labels.frames G).level d
  let bill j : ℝ := Doors.rate L * (Ψ (i+1)).p.mass (feet j) (cost j)
  have wage : 0 ≤ Doors.rate L := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have finite : Summable bill := expenses.2.1.mul_left _
  have total : ∑' j, bill j ≤ Doors.rate L*a := by
    simp only [bill,tsum_mul_left]
    exact mul_le_mul_of_nonneg_left expenses.2.2 wage
  have numbers : Summable (fun j => F.coeffSize (each j).x) :=
    .of_nonneg_of_le (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) size (finite.div_const 3)
  let M := Extra.Histories.merge (Extra.Histories.code ℕ) each
  have charge : 0 < divisor := Real.sqrt_pos.mpr (Real.exp_pos _)
  obtain ⟨wallet,_,_⟩ := merge_budget (Extra.Histories.code ℕ) each charge pay finite
  refine ⟨M,merge_format _ _ shape,rem_mono wallet total,?_,?_⟩
  · change F.coeffSize (∑' j, (each j).x) ≤ _
    calc
      _ ≤ ∑' j, F.coeffSize (each j).x := Size.bound F numbers
      _ ≤ ∑' j, bill j/3 := numbers.tsum_le_tsum size (finite.div_const 3)
      _ = (∑' j, bill j)/3 := tsum_div_const
      _ ≤ _ := by linarith only [total]
  intro W
  have upper := (QuadraticLocal.Advent.later R π Γ Ψ course (Nat.le_succ_of_le start) live).truep.valid
  have lower := (QuadraticLocal.Advent.later R π Γ Ψ course start live.le).truep.valid
  let spring := (WilsonOriginalNullHouse.original R π Γ Ψ course start live).choose
  let H := houseS spring zeroI
  have kernel : (Ω).IsKernel (Ψ (i+1)).beta G := (Ω).isKernel (funds_branch H.laws.intake.ready) _
  obtain ⟨weights,meas⟩ := WilsonOriginalNullSeries.paid (Ψ (i+1)) o feet rows cost a expenses specs bounds upper
  have prices := push_tsum kernel weights meas W
  have identity := (merge_density (Extra.Histories.code ℕ) each charge lower pay finite numbers (localSection G d) W).tsum_eq
  rw [← identity]
  simp_rw [read]
  rw [tsum_mul_left]
  apply congrArg (fun z:ℂ => scale*z)
  calc
    _ = (Ω).push (Ψ (i+1)).beta (fun V => ∑' j,
      ((Ψ (i+1)).eval V:ℂ)*masked (Ψ (i+1)).p.threshold (feet j) (rows j) V) W := prices.tsum_eq
    _ = _ := by simp_rw [tsum_mul_left]

end YM.Integration.WilsonOriginalNullFamily
