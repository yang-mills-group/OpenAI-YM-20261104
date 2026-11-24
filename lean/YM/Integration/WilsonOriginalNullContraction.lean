import YM.Integration.WilsonOriginalNullScale
import YM.Integration.WilsonOriginalNullZero

/-! A restored scalar density, read on every configuration of the original
return. The hard coefficient uses the same numerical vacuum and its forced
family as the incoming measured course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullContraction
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

/-- This one lower-date condition is eventually true independently of the
physical torus, every upper cutoff, every origin and every regular atom. -/
def Ready (K : Run G) (z r : ℕ) : Prop :=
  let A := K.alloy.B.a
  let Lz := K.rolls.L (A.clock.J (z+1))
  r+3 ≤ A.clock.J z ∧ 1 ≤ A.clock.J z ∧
  r ≤ (A.budget z).order ∧ r ≤ (A.budget z).power ∧
  Local.hitWidth (A.budget z)*LocalComparison.forcedDivisor K.family z ≤ 1 ∧
  (∀ per, minSide G r ≤ (K.family.side z per).val) ∧
  3*(Lz.val:ℝ)^r * (A.clock.hatBeta (z+1))^(-(1:ℝ)) ≤ Doors.rate Lz

theorem eventual (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (roster : ∀ j, j ≤ (R.metals.p.profile j).order ∧ j ≤ (R.metals.p.profile j).power)
    (d : ℕ) : ∀ᶠ i : ℕ in atTop, Ready R i d := by
  filter_upwards [WilsonOriginalNullClock.ready R simple d 1 roster,
    WilsonOriginalNullScale.forced R simple slow d] with i ⟨hd,hq,ho,hp,ht,hs⟩ hf
  exact ⟨hd,hq,ho,hp,ht,hs,by simpa [mul_assoc] using hf⟩

include course start live hf hc
theorem original (simple : G.Simple) (way : WayStation R.kit)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (tab : D.Tab R.rolls) (ticket : TicketP R.alloy R.kit D tab) (C₀ : Marker.Census Unit)
    (ready : Ready R i d) :
    ∃ Y : Source.Coefficient ((Labels.frames G).level d) (R.family.side i per),
      Y.Format a0 (hol G) (Ψ i) ∧ Y.remBound a0 (Ψ i) divisor (Doors.rate L*fineMass) ∧
      ((Labels.frames G).level d).coeffSize Y.x ≤ (Doors.rate L*fineMass)/3 ∧
      ∀ Zc, Y.density a0 (localSection G d) (Ψ i) Zc =
        scale * (Ω).push (Ψ (i+1)).beta (fun V =>
          ((Ψ (i+1)).eval V : ℂ) * masked (Ψ (i+1)).p.threshold X f V) Zc := by
  have hκ : 0 < divisor := Real.sqrt_pos.mpr (Real.exp_pos _)
  have mass : 0 ≤ fineMass := mul_nonneg (Real.exp_pos _).le hc.1
  rcases mass.eq_or_lt with he|fund
  · obtain ⟨Y,hY,budget,size,equal⟩ := WilsonOriginalNullZero.original (d:=d) Ω
      (Ψ (i+1)) (Ψ i) o X f c hc he.symm scale divisor hκ
    refine ⟨Y,hY,?_,?_,equal⟩
    · rw [← he,mul_zero]; exact budget
    · rw [← he,mul_zero,zero_div]; exact size
  obtain ⟨degree,q,base,power,hits,side,hforce⟩ := ready
  obtain ⟨Y,format,body,primary,equal⟩ :=
    WilsonOriginalNullStored.original R π Γ Ψ course start live o X f hf c hc simple way D tab ticket C₀
      1 q degree fund (side per) base power hits
  let v := Local.factor (hol G) (localSection G d) (B).supportExponent
    (Next.Foundations.price G (max (B).order (B).power))
  let cap := v*(2*coinFee G p d L*fineMass)
  have restored : v = vigors G p d := by
    change Local.factor _ _ (R.alloy.B.a.params i).supportExponent
      (Next.Foundations.price G (max (R.alloy.B.a.params i).order (R.alloy.B.a.params i).power)) = _
    rw [params_eq R.alloy.B.valid i]; rfl
  have fee : 3*cap ≤ Doors.rate L*fineMass := by
    dsimp only [cap]; rw [restored]
    have h := mul_le_mul_of_nonneg_right (WilsonOriginalNullScale.regular (G:=G) p d L) mass
    linarith only [h]
  have norm : ‖scale*(fineMass:ℂ)‖ = ((L).val:ℝ)^d*fineMass := by
    simp [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg mass]
  have gas : 3*(‖scale*(fineMass:ℂ)‖*high^(-(1:ℝ))) ≤ Doors.rate L*fineMass := by
    rw [norm]
    have h := mul_le_mul_of_nonneg_right hforce mass
    linarith only [h]
  simp only [Nat.cast_one] at body
  change Y.remBound a0 (Ψ i) divisor (cap+(‖scale*(fineMass:ℂ)‖*high^(-(1:ℝ))+cap)) at body
  refine ⟨Y,format,rem_mono body (by linarith only [fee,gas]),?_,equal⟩
  exact primary.trans (by change cap ≤ _; linarith only [fee])

end YM.Integration.WilsonOriginalNullContraction
