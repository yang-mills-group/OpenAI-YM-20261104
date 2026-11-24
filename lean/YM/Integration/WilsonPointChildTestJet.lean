import YM.Integration.WilsonPointChildTestSupport
import YM.WilsonCoeffUV.Test.Polynomial

/-! The independently registered test on the half-cell supplies the genuine
    unaveraged original zero-child test jet. Its extension has fixed fee. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildTestJet
open YM FormalBulk08 Lattice RG Laurent Next.Foundations PhysicalNext.Repeat.Legato
open Dawn Pose WilsonCoeffUV.Embroider
open WilsonPointChildTestSupport WilsonNeutralPointCourse
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped BigOperators Topology Classical ContDiff
variable {D d:ℕ}{G:Gauge}
local instance studio_group (D:ℕ):NormedAddCommGroup (Studio D):=inferInstance
local instance studio_space (D:ℕ):NormedSpace ℝ (Studio D):=inferInstance
local instance volume_group (D:ℕ):NormedAddCommGroup (Volume D):=inferInstance
local instance volume_space (D:ℕ):NormedSpace ℝ (Volume D):=inferInstance

def extend (D:ℕ)(x:Chamber):Volume D →L[ℝ] Studio D:=
  ∑t:Spring D,(claim D (finger (paper_fits t)) x).smulRight (cone D t.val)

def rent (D:ℕ):ℝ:=∑t:Spring D,‖cone D t.val‖

theorem price (x:Chamber):‖extend D x‖≤rent D:=by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _=>norm_nonneg _)
  intro q
  simp only [extend,sum_apply,ContinuousLinearMap.smulRight_apply,Finset.sum_mul]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum fun t _=>?_ )
  rw [norm_smul,mul_comm]
  exact mul_le_mul_of_nonneg_left (registry q _ x) (norm_nonneg _)

theorem notch_extend (x:Chamber)(q:Volume D)(t:Spring D):
    notch t.val (paper_fits t) (extend D x q)=q.val (finger (paper_fits t)) x:=by
  simp only [extend,sum_apply,ContinuousLinearMap.smulRight_apply,map_sum,map_smul,
    notch_basis,smul_eq_mul,claim_take]
  convert Finset.sum_eq_single t (s:=Finset.univ) (f:=fun w:Spring D=>
        q.val (finger (paper_fits w)) x * (if t.val=w.val then 1 else 0)) ?_ ?_ using 1
  · simp
  · intro b _ ne
    rw [if_neg (fun h=>ne (Subtype.ext h.symm)),mul_zero]
  · simp

theorem origin_step (L:Side)(h:2≤L.val):peninsula (0:Site L) h origin=origin:=by
  apply Subtype.ext
  have lift0:lift (0:Site L)=(0:Cover):=by ext; simp [lift]
  change pith (0:Site L)+scale L • (0:E4)=0
  simp [pith,lift0,Place.seat_zero]

theorem origin_path (R:Run G)(h i:ℕ):WilsonPointChildTestSupport.points R (fun _=>0) h i=origin:=by
  induction h generalizing i with
  | zero=>rfl
  | succ n ih=>exact (congrArg (peninsula (0:Site _) _) (ih (i+1))).trans (origin_step _ _)

theorem agrees (x:Chamber)(p:Volume D)(Y:Studio D)
    (agree:∀t:Spring D,notch t.val (paper_fits t) Y=p.val (finger (paper_fits t)) x):
    Same origin Y (extend D x p):=by
  intro k
  let t:Spring D:=⟨word k,(paper_is _).mpr (by rw [word_val]; exact Nat.le_of_lt_succ k.1.isLt)⟩
  rw [←notched (paper_fits t) Y k rfl,←notched (paper_fits t) (extend D x p) k rfl,notch_extend,agree]

theorem original (R:Run G)(wood:Primer.Families R.family)(a:G.ColorIndex)(depth:d<D)
    (N i:ℕ)(b:Letter (R.family.labels.level d))(p:Volume D)(Y:Studio D)
    (agree:∀t:Spring D,notch t.val (paper_fits t) Y=p.val (finger (paper_fits t)) zeroC):
    filed R wood a depth (fun _=>0) N i b Y=filed R wood a depth (fun _=>0) N i b (extend D zeroC p):=by
  apply WilsonPointChildTestSupport.original
  rw [origin_path]
  exact agrees _ _ _ agree

end YM.Integration.WilsonPointChildTestJet

