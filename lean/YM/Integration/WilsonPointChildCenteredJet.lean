import YM.Integration.WilsonPointChildAddress
import YM.FormalBulk08.Annex.Palm
import YM.Integration.WilsonPointChildTestCoordinates
import YM.Integration.WilsonPointChildTestJet

/-! A genuine smooth test in the sup-norm half-cell and its physical
    Euclidean representative have equal pointed jets in the same axes. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildCenteredJet
open YM Lattice RG Laurent FormalBulk08 Dawn Pose Next.Foundations PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Embroider WilsonPointChildTestSupport WilsonNeutralPointCourse WilsonPointChildTestJet
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{d D:ℕ}


open WilsonPointChildTestCoordinates

def shape (D:ℕ)(z:Pier)(t:Spring D):Garden D:=
  ⟨fun x=>rose t.val (x+ -z.val),(rose_smooth t.val).of_le (show (D:WithTop ℕ∞)≤ω from le_top) |>.comp (contDiff_id.add contDiff_const)⟩

theorem sample (z:Pier)(b:Brush D)(t:Spring D):
    assess b z (portrait D (shape D z t))=if word b=t.val then 1 else 0:=by
  change iteratedFDeriv ℝ b.1.val (fun x:E4=>rose t.val (x+ -z.val)) z.val (basis ∘ b.2)=_
  rw [iteratedFDeriv_comp_add_right,add_neg_cancel]
  exact rose_corner _ _

def extend (D:ℕ)(z:Pier)(c:Chamber):Volume D →L[ℝ] Studio D:=
  ∑t:Spring D,(claim D (finger (paper_fits t)) c).smulRight (portrait D (shape D z t))

theorem picker (z:Pier)(c:Chamber)(p:Volume D)(b:Brush D)(t:Spring D)(right:word b=t.val):
    assess b z (extend D z c p)=claim D (finger (paper_fits t)) c p:=by
  simp only [extend,sum_apply,ContinuousLinearMap.smulRight_apply,map_sum,map_smul,smul_eq_mul,sample]
  rw [Finset.sum_eq_single t]
  · rw [right,if_pos rfl,mul_one]
  · intro v _ ne;rw [if_neg ((fun h=>ne (Subtype.ext (right.symm.trans h).symm))),mul_zero]
  · simp

theorem original (R:Run G)(wood:Primer.Families R.family)(a:G.ColorIndex)(depth:d<D)
    (digit:∀i,Site (R.family.S.block i))(N j:ℕ)(v:Letter (R.family.labels.level d))(p:Scroll D):
    let y:=WilsonPointChildTestSupport.points R digit (N-j) j
    let c:=WilsonPointChildAddress.seat R digit (N-j) j
    filed R wood a depth digit N j v (physical p) = filed R wood a depth digit N j v (extend D y c (page D p)):=by
  intro y c
  have supported:=WilsonPointChildTestSupport.path R wood a depth digit N (N-j) j v
  apply supported
  intro b
  let t:Spring D:=⟨word b,(paper_is _).mpr ((word_val b).le.trans (Nat.le_of_lt_succ b.1.isLt))⟩
  change (physical p).val b y = assess b y (extend D y c (page D p))
  rw [picker y c (page D p) b t rfl]
  have eq:word (finger (paper_fits t))=word b:=(draw_any t.val (paper_fits t)).choose_spec
  exact (congrArg (fun f:C(Pier,ℝ)=>f y) (same_word eq.symm (physical p))).trans
    (WilsonPointChildAddress.common R digit (N-j) j p _)

end YM.Integration.WilsonPointChildCenteredJet
