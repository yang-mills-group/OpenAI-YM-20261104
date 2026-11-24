import YM.Integration.WilsonOriginalNullPayment
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Parcel

/-! All grouped singleton clusters on the original elected guide. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullRegular
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

include course start live hf hc
theorem original (simple : G.Simple) (hd : d+3 ≤ R.alloy.B.a.clock.J i) :
    let K := K0
    let T := cloud
    ∃ e : ℕ → ℝ,
      (∀ j, (B).supBounds a0 (Blush.scope K T a0 j) (Blush.fields K T scale j) (e j)) ∧
      SumBudget (fun j => Local.reservedMass B (Blush.scope K T a0 j) (e j))
        (2 * coinFee G p d L * (Ψ (i+1)).p.mass X c) := by
  intro K T
  have paid := WilsonOriginalNullPayment.isolated R π Γ Ψ course start live S o X f hf c hc hd
  let fee := coinFee G p d L * (Ψ (i+1)).p.mass X c
  have addr := latch (Ψ (i+1)) o X hf.anchor room
  have crest : T.live.crest = X := by
    change ((Ψ (i+1)).activities.reg (found o X hf.anchor)).support = X
    rw [addr]
  have here : a0 ∈ T.live.crest.image (Ω).ratio.parent :=
    crest.symm ▸ Finset.mem_image.mpr ⟨o,hf.anchor,rfl⟩
  obtain ⟨_,_,build⟩ := Blush.bookbag simple live S zeroI T a0 scale
    (localSection G d) R.b.r here
  obtain ⟨e, reg, budget⟩ := (build fee paid).bulk
  obtain ⟨stage,_⟩ := R.b.stamp _ _ (step_paid R.alloy.B.a i) d (by omega)
    _ (R.alloy.B.valid.pays i)
  have spare := (stage _ (Ψ (i+1)) T).1
  rw [crest] at spare
  refine ⟨e, reg, budget.1, budget.2.1, budget.2.2.trans ?_⟩
  have mass : T.live.weight = c := rfl
  rw [mass] at spare
  have norm : ‖scale‖ = ((L).val:ℝ)^d := by simp
  rw [norm]
  change _ + fee ≤ _
  calc
    _ ≤ fee + fee := add_le_add spare (le_refl _)
    _ = 2 * coinFee G p d L * (Ψ (i+1)).p.mass X c := by unfold fee; ring

end YM.Integration.WilsonOriginalNullRegular
