import YM.Integration.WilsonOriginalNullHouse
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Upswing

/-! The isolated, displaced regular leaf of the elected guide. The complex
source uses its original mask and the old gas when read in either real axis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullLeaf
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

theorem component (hd : d+3 ≤ R.alloy.B.a.clock.J i)
    (S : Spring R.kit N i per 0 0 (fun _ => U))
    (o : Site (R.family.side (i+1) per)) (X : Support (R.family.side (i+1) per))
    (f : Config G (R.family.side (i+1) per) → ℂ)
    (hf : RegFit U o d (hol G) X f) (c : ℝ) (hc : (U).p.supBounds o X f c)
    (a : ℂ →L[ℝ] ℝ) (ha : ∀ z, ‖a z‖ ≤ ‖z‖) :
    let K := houseS S zeroI
    let key := found o X hf.anchor
    let M := cove U o X hf.anchor f c hf.smooth hc a ha room
    ∃ t, (B).supBounds ((Ω).ratio.parent o) (plate K key).support
          (matin M K (icon K key) Chi.canonical) t ∧
       Local.reservedMass B (plate K key).support t ≤
          winG G p d L * (U).p.mass X c := by
  intro K key M
  have addr : (U).activities.reg key = reg o X hf.anchor := latch U o X hf.anchor room
  have site : (plate K key).site = (Ω).ratio.parent o := by
    change (Ω).ratio.parent ((U).activities.reg key).site = _
    rw [addr]
  have crest : M.crest = X := by
    change ((U).activities.reg key).support = X
    rw [addr]
  let h := a ∘ f
  have val : M.ingredient = masked (U).p.threshold ((U).activities.reg key).support h := by
    funext Z
    change a (masked (U).p.threshold X f Z) = _
    rw [addr]
    by_cases hz : Healthy (U).p.threshold X Z
    · exact (congr_arg a (masked_eq _ _ _ _ hz)).trans (masked_eq _ _ h _ hz).symm
    · change _ = masked (U).p.threshold X h Z
      rw [masked_ne _ _ _ _ hz, masked_ne _ _ _ _ hz, map_zero]
  have null : Nonwrapping ((U).activities.reg key).support ((U).activities.reg key).site →
        Peak.lit ((U).activities.reg key).site ((U).activities.reg key).support h d := by
    rw [addr]
    intro hx
    apply Peak.spoke f a (hol G) X hf.smooth (show Nonwrapping X o from hx)
      (by change 2 ≤ (R.alloy.B.a.S.side (i+1) per).val; have := Return.enough_room R.alloy.B (i+1) per; omega) (by
        rw [(S.knows (0:ℝ) zeroI.2).1.point]
        have hz := (R.b.clock.stage (i+1)).1
        have step := (step_paid R.alloy.B.a i).1
        exact (by omega : d ≤ R.alloy.B.a.clock.J (i+1)).trans hz)
      (le_refl d) (fun j => (hf.proj hx j).2)
  have regH : (U).p.Regular ((U).activities.reg key).support h := by
    rw [addr]
    exact readings a hf.smooth
  have price : (U).p.supBounds ((U).activities.reg key).site ((U).activities.reg key).support h M.weight := by
    rw [addr]
    exact pricesL a hf.smooth ha c hc
  obtain ⟨t, paid, bill⟩ := crowning live R.b.r R.b.tunes R.b.furthering
    (feet hd R.b.clock) S zeroI M h key rfl regH val price null
  exact ⟨t, site ▸ paid, bill.trans_eq (congr_arg (fun X' => winG G p d L * (U).p.mass X' c) crest)⟩

end YM.Integration.WilsonOriginalNullLeaf
