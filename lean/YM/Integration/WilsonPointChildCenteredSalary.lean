import YM.Integration.WilsonPointChildCenteredJet
import YM.Integration.WilsonPointChildAddress
import YM.FormalBulk08.Annex.Palm
import YM.Integration.WilsonPointChildTestCoordinates
import YM.Integration.WilsonPointChildTestJet

/-! A genuine smooth test in the sup-norm half-cell and its physical
    Euclidean representative have equal pointed jets in the same axes. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildCenteredSalary
open YM Lattice RG Laurent FormalBulk08 Dawn Pose Next.Foundations PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Embroider WilsonPointChildTestSupport WilsonNeutralPointCourse WilsonPointChildTestJet
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{d D:ℕ}


open WilsonPointChildTestCoordinates


open WilsonPointChildCenteredJet
local instance studio_group (D:ℕ):NormedAddCommGroup (Studio D):=inferInstance
local instance studio_space (D:ℕ):NormedSpace ℝ (Studio D):=inferInstance
local instance volume_group (D:ℕ):NormedAddCommGroup (Volume D):=inferInstance
local instance volume_space (D:ℕ):NormedSpace ℝ (Volume D):=inferInstance
def test (t:Spring D)(b:Brush D):C(Pier×Pier,ℝ):=
  ⟨fun q=>halo (tint D t.val) b (q.2.val + -q.1.val), (haloes (tint D t.val) b).comp
    ((continuous_subtype_val.comp continuous_snd).add (continuous_subtype_val.comp continuous_fst).neg)⟩

def bill (t:Spring D):ℝ:=∑b:Brush D,‖test t b‖

theorem nonnegative (t:Spring D):0≤bill t:=Finset.sum_nonneg fun _ _=>norm_nonneg _

theorem bound (z:Pier)(t:Spring D):‖portrait D (shape D z t)‖≤bill t:=by
  apply panel_le _ (nonnegative t)
  intro b v
  have eq:(portrait D (shape D z t)).val b v=test t b (z,v):=by
    change iteratedFDeriv ℝ b.1.val (fun x:E4=>rose t.val (x+ -z.val)) v.val (basis ∘ b.2)=
      iteratedFDeriv ℝ b.1.val (rose t.val) (v.val+ -z.val) (basis ∘ b.2)
    rw [iteratedFDeriv_comp_add_right]
  rw [eq]
  exact ((test t b).norm_coe_le_norm _).trans
    (Finset.single_le_sum (fun (a:Brush D) _=>norm_nonneg (test t a)) (Finset.mem_univ b))

theorem original (z:Pier)(c:Chamber):‖WilsonPointChildCenteredJet.extend D z c‖≤∑t:Spring D,bill t:=by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _=>nonnegative _)
  intro q
  simp only [WilsonPointChildCenteredJet.extend,sum_apply,ContinuousLinearMap.smulRight_apply,Finset.sum_mul]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum fun t _=>?_ )
  rw [norm_smul,mul_comm]
  exact mul_le_mul (bound z t) (registry q _ c) (norm_nonneg _) (nonnegative _)

end YM.Integration.WilsonPointChildCenteredSalary
