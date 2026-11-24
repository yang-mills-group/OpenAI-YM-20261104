import YM.Integration.WilsonOriginalNullContraction
import YM.Integration.WilsonOriginalNullShadow
import YM.Integration.WilsonOriginalNullFlatPrimary
import YM.Extra.SOURCE_HISTORIES.Pencil
import YM.Integration.WilsonOriginalNullScale
import YM.Integration.WilsonOriginalNullZero

/-! A restored scalar density, read on every configuration of the original
return. The hard coefficient uses the same numerical vacuum and its forced
family as the incoming measured course. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullCanonical
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

open Marker RemainderComparison.Serif WilsonOriginalNullAdmission WilsonOriginalNullComplex
open QuadraticLocal RemainderComparison RemainderComparison.Lyric RemainderComparison.Muse Source
open RemainderComparison.Typeface RemainderComparison.Serif RemainderComparison.Sleet
open AllOrder.Floe.Step PlanV WheelP Mallow Fusion.Attached
local notation "F₀" => (Labels.frames G).level d
local notation "T₀" => localSection G d
local notation "divisor" => LocalComparison.forcedDivisor R.family i
local notation "high" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "upperW" => Next.Foundations.price G (max (U).p.order (U).p.power)
local notation "lowerW" => Next.Foundations.price G (max (B).order (B).power)
local notation "ρ" => Local.factor (hol G) (T₀) (B).supportExponent lowerW
local notation "scale" => ((L).val:ℂ)^d

include course start live in
/-- The genuine printed, nonunit upper primary on the incumbent two vacua.
Engineering conversion is charged only once to the returned whole coefficient. -/
theorem original (simple : G.Simple) (way : WayStation R.kit)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (tab : D.Tab R.rolls) (ticket : TicketP R.alloy R.kit D tab) (C₀ : Marker.Census Unit)
    (ready : WilsonOriginalNullContraction.Ready R i d)
    (fine : WilsonOriginalNullContraction.Ready R (i+1) d)
    (o : Site (R.family.side (i+1) per)) (v : (F₀).Coeff) (null : v 0=0) :
    let a0 := (Ω).ratio.parent o
    let bill := ((L).val:ℝ)^d*(4*ρ+1)*(U).p.mass ((T₀).footprint o) (upperW*(F₀).coeffSize v)
    ∃ Y : Coefficient F₀ (R.family.side i per),
      Y.Format a0 (hol G) (Ψ i) ∧ Y.remBound a0 (Ψ i) divisor bill ∧
      (F₀).coeffSize Y.x ≤ bill ∧ ∀ Zc, Y.density a0 T₀ (Ψ i) Zc =
        scale * (Ω).push (U).beta ((Extra.Histories.primary o v).density o T₀ U) Zc := by
  classical
  intro a0 bill
  obtain ⟨hd,_,ord,pow,hits,fit,_⟩ := ready
  obtain ⟨_,_,upperOrd,upperPow,_,upperFit,_⟩ := fine
  have point := (QuadraticLocal.Advent.later R π Γ Ψ course (Nat.le_succ_of_le start) live).truep.point
  let X := (T₀).footprint o
  let f := Local.presented T₀ o (U).p.threshold v
  let rate := upperW*(F₀).coeffSize v
  let tabbed := (U).p.mass X rate
  have core : (F₀).core v=v := by simpa only [null,zero_smul,add_zero] using Size.core_plus (F₀) v
  have printed : Local.Readable (hol G) (T₀) (U).p (R.family.side (i+1) per) upperW := by
    rw [point];exact Local.foundation_readable G d (upperFit per) upperOrd upperPow
  have inc := WilsonOriginalNullFlatPrimary.canonical (F₀) (hol G) (T₀) U o printed v
  rw [core] at inc
  have ht : 0≤tabbed := mul_nonneg (Real.exp_pos _).le inc.2.1
  have reading : ((Extra.Histories.primary o v).density o (T₀) U) =
      fun V => ((U).eval V:ℂ)*masked (U).p.threshold X f V := by
    funext V;rw [primary_density]
    change _*(v 0+masked (U).p.threshold X (Local.presented T₀ o (U).p.threshold ((F₀).core v)) V)=_
    rw [null,zero_add,core]
  rw [reading]
  rcases ht.eq_or_lt with zero | positive
  · obtain ⟨Y,fmt,body,size,read⟩ := WilsonOriginalNullZero.original (d:=d) Ω U (Ψ i)
        o X f rate inc.2 zero.symm scale divisor (Real.sqrt_pos.mpr (Real.exp_pos _))
    have paid : bill=0 := by change _ * tabbed=0;rw [←zero,mul_zero]
    exact ⟨Y,fmt,paid.symm ▸ body,paid.symm ▸ size,read⟩
  obtain ⟨Y,fmt,paid,size,read⟩ := WilsonOriginalNullShadow.original R π Γ Ψ course start live
    o X f inc.1 rate inc.2 simple way D tab ticket C₀ 0 (Nat.zero_le _) (by omega) positive (fit per) ord pow hits
  let cap := ρ*(2*coinFee G p 0 L*tabbed)
  have nn : 0≤ρ := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans (Local.atomPrice_ge_one _ _ (zero_le_one.trans (Next.Foundations.price_one_le G _))))
  have cap0 : 0≤cap := by
    exact mul_nonneg nn (mul_nonneg (mul_nonneg zero_le_two (coin_pos G p 0 L).le) positive.le)
  have capmax : cap≤ρ*(2*tabbed) := by
    apply mul_le_mul_of_nonneg_left _ nn
    have le:=mul_le_mul_of_nonneg_left (Circlet.coinFlat G p L 0) zero_le_two
    simpa only [mul_one] using mul_le_mul_of_nonneg_right le positive.le
  have spent : cap+(tabbed+cap) ≤ (4*ρ+1)*tabbed := by linarith only [capmax]
  have full : ‖(tabbed:ℂ)‖=tabbed := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg positive.le]
  change Y.remBound a0 (Ψ i) divisor
      (cap+(‖((L).val:ℂ)^0*(tabbed:ℂ)‖*high^(-((0:ℕ):ℝ))+cap)) at paid
  simp only [pow_zero,one_mul,full,Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one] at paid
  have scaleNorm : ‖scale‖ = ((L).val:ℝ)^d := by simp
  have final := stretch_rem scale paid
  rw [scaleNorm] at final
  have pay := mul_le_mul_of_nonneg_left spent (pow_nonneg (Nat.cast_nonneg (L).val) d)
  refine ⟨stretch scale Y,stretch_format scale fmt,rem_mono final (pay.trans_eq (by unfold bill;ring)),?_,?_⟩
  · change (F₀).coeffSize (scale • Y.x) ≤ bill
    rw [Size.smul,scaleNorm]
    have base : cap≤(4*ρ+1)*tabbed := by
      linarith only [positive.le,cap0,spent]
    have value := mul_le_mul_of_nonneg_left (size.trans base) (pow_nonneg (Nat.cast_nonneg (L).val) d)
    exact value.trans_eq (by unfold bill;ring)
  · intro Zc
    simp only [pow_zero,one_mul] at read
    rw [stretch_density]
    congr 1
    exact read Zc

end YM.Integration.WilsonOriginalNullCanonical
