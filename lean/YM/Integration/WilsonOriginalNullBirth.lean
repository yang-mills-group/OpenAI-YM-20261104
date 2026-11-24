import YM.Integration.WilsonOriginalNullComplex

/-! Bare input on the actual possibly nonbare upper density, at the displaced physical address. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBirth
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
include course start live hf hc
theorem original (C₀ : Marker.Census Unit) (w : ℝ) (Zf : Config G (R.family.side (i+1) per)) :
    let T := cloud
    TuneR (socket T) Set.univ (fun _ => w) 0 (fun b => letter C₀ (phase b)) Ω Zf =
      Poly.bead C₀ ((Ψ (i+1)).eval Zf) + Poly.send (C₀.fire ())
        (((w : ℂ) * ((Ψ (i+1)).eval Zf : ℂ)) * masked (Ψ (i+1)).p.threshold X f Zf) := by
  intro T
  let key := Blush.found o X hf.anchor
  have same (b : Bool) : (socket T b).turn = .logKey key := by cases b <;> rfl
  have left : (socket T false).ingredient Zf = (masked (Ψ (i+1)).p.threshold X f Zf).re := rfl
  have right : (socket T true).ingredient Zf = (masked (Ψ (i+1)).p.threshold X f Zf).im := rfl
  refine (WilsonOriginalNullSource.original Ω (socket T) key same (fun _ => w) (fun b => letter C₀ (phase b)) Zf).trans ?_
  rw [Fintype.sum_bool]
  apply congrArg (Poly.bead C₀ ((Ψ (i+1)).eval Zf) + ·)
  ext m
  change ((↑(w*(socket T true).ingredient Zf*(Ψ (i+1)).eval Zf) : ℂ) * (letter C₀ (phase true)).part m +
      (↑(w*(socket T false).ingredient Zf*(Ψ (i+1)).eval Zf) : ℂ) * (letter C₀ (phase false)).part m) = _
  by_cases hm : m = C₀.fire ()
  · subst m
    simp only [letter,Poly.part_send,if_true,left,right,phase,Bool.false_eq_true,if_false,
      Complex.ofReal_mul,mul_one]
    let g := masked (Ψ (i+1)).p.threshold X f Zf
    let coin := (w:ℂ) * ((Ψ (i+1)).eval Zf : ℂ)
    calc
      _ = coin * ((g.re : ℂ) + (g.im : ℂ)*Complex.I) := by unfold coin g; ring
      _ = _ := congrArg (coin * ·) (Complex.re_add_im g)
  · simp [letter,Poly.part_send,hm]

end YM.Integration.WilsonOriginalNullBirth
