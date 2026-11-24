import YM.Integration.WilsonOriginalNullFiniteTap
import YM.Integration.WilsonOriginalNullAdmission
import YM.Integration.WilsonOriginalNullRegular

/-! Identify the funded real and imaginary words of one complex null leaf at its own root. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullComplex
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

open Merge Merge.Palette
variable {G : Gauge} (R : Run G) {N per i : ℕ}
    (Ψ : ∀ j, RG.Rep G (R.family.side j per))

open Marker RemainderComparison RemainderComparison.Lyric RemainderComparison.Mosaic
open RemainderComparison.Serif MergeProof.Accent

open WilsonOriginalNullAdmission
open RG Mallow RemainderComparison.Muse
def socket {n : Side} {X : RG.Rep G n} (T : Blush.Cloud X) (b : Bool) : Lotus.Leaf X :=
  if b then T.pale else T.live
def phase (b : Bool) : ℂ := if b then Complex.I else 1
lemma small (b : Bool) : ‖phase b‖ ≤ 1 := by cases b <;> simp [phase]

theorem original (live : i < N)
    (S : Mallow.Spring R.kit N i per 0 0 (fun _ => Ψ (i+1)))
    (o : Site (R.family.side i per)) (T : Blush.Cloud (Ψ (i+1)))
    (C : Marker.Census Unit) (w : ℝ) (hw : 0 ≤ w) (k : ℕ) (hk : 1 ≤ k)
    (U : Config G (R.family.side i per))
    (hsum : Summable (fun j => Serif.glyph (socket T) (houseS S WilsonOriginalNullHouse.point)
      Chi.canonical Set.univ (fun _ => w) 0 (fun b => letter C (phase b)) j U)) (scale : ℂ) :
    let K := houseS S WilsonOriginalNullHouse.point
    let t := Pressure.temp (R.alloy.B.a.clock.hatBeta i)
    scale * (GridRenewal.Rain.fresh (∑' j, Serif.glyph (socket T) K Chi.canonical Set.univ
      (fun _ => w) 0 (fun b => letter C (phase b)) j U)).part (C.fire ()) =
      (w : ℂ) * (∑' j,RG.masked t (Blush.scope K T o j) (Blush.fields K T scale j) U) := by
  intro K t
  have hb (b : Bool) : (letter C (phase b)).part C.quiet = 0 := by
    simp [letter,Poly.part_send,Ne.symm (C.fire_hot ())]
  rw [WilsonOriginalNullFiniteTap.original R Ψ live S C (socket T) (fun _ => w)
    (fun b => letter C (phase b)) (fun _ => 1) (fun _ => hw) (tap C phase small hk) hb U hsum ()]
  let amt (z : K.fragrances) := RG.masked t (Daisy.Charity.locus T.live K o z) (Blush.pane K T scale z) U
  have embed : (∑' j,RG.masked t (Blush.scope K T o j) (Blush.fields K T scale j) U) =
      ∑' z,amt z := by
    let g j := RG.masked t (Blush.scope K T o j) (Blush.fields K T scale j) U
    have h (z : K.fragrances) : amt z = g (Blush.enter K z) := by
      unfold amt g Blush.scope Blush.fields
      rw [(Blush.enter K).injective.extend_apply,stuffed]
      rfl
    simp_rw [h]
    symm
    exact (Blush.enter K).injective.tsum_eq (f:=g) (fun j hj => by
      by_contra absent
      apply hj
      unfold g Blush.fields
      rw [blank _ _ absent]
      by_cases h : Healthy t (Blush.scope K T o j) U <;> simp [h]; rfl)
  rw [embed,← tsum_mul_left,← tsum_mul_left]
  apply tsum_congr
  intro z
  change scale * (∑ j : Bool, ((w * masked t (K.bookFoot (.inr z))
      (matin (socket T j) K z Chi.canonical) U : ℝ) : ℂ) * (letter C (phase j)).part (C.fire ())) =
      (w : ℂ) * amt z
  have both (M : Lotus.Leaf (Ψ (i+1))) :
      masked t (Daisy.Charity.locus M K o z) (Complex.ofReal ∘ matin M K z Chi.canonical) U =
        ((masked t (K.bookFoot (.inr z)) (matin M K z Chi.canonical) U : ℝ) : ℂ) :=
    (Blush.liquid ..).trans (congrArg Complex.ofReal (Daisy.Charity.mask_ag M K Chi.canonical z U t o))
  have pale : masked t (Daisy.Charity.locus T.live K o z) (Complex.ofReal ∘ matin T.pale K z Chi.canonical) U =
      ((masked t (K.bookFoot (.inr z)) (matin T.pale K z Chi.canonical) U : ℝ) : ℂ) :=
    (congrArg (fun X => masked t X (Complex.ofReal ∘ matin T.pale K z Chi.canonical) U)
      (Blush.arches K T o z)).trans (both T.pale)
  have hpair : amt z = scale * (((masked t (K.bookFoot (.inr z)) (matin T.live K z Chi.canonical) U : ℝ) : ℂ) +
      Complex.I * ((masked t (K.bookFoot (.inr z)) (matin T.pale K z Chi.canonical) U : ℝ) : ℂ)) := by
    unfold amt Blush.pane
    rw [Blush.maskStar,Blush.breakT,Blush.maskStar]
    exact congrArg (scale * ·) (congrArg₂ HAdd.hAdd (both T.live) (congrArg (Complex.I * ·) pale))
  rw [hpair]
  simp only [Fintype.sum_bool,letter,Poly.part_send,if_true,socket,phase,Bool.false_eq_true,if_false,
    Complex.ofReal_mul,mul_one]
  ring

end YM.Integration.WilsonOriginalNullComplex
