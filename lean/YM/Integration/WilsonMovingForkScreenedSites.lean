import YM.Integration.WilsonMovingForkOpticalQuadrature
import YM.Integration.WilsonMovingForkMixedSeed

/-! Every physical sample of the high-order moving aperture uses actual
lattice parents, even when some near or reflected coordinates originally
tie. The same sampled placements may be used for each signed corner. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkScreenedSites
open Function Filter Finset Set Metric Extraction Lattice
open Contacts.Mat Contacts.Sensor WilsonSeparatedPhysicalRay WilsonSeparatedBranchStencil WilsonSeparatedGridTree WilsonSeparatedGridDesign
open scoped Classical Topology BigOperators
variable {n m:ℕ}{E:Type}[Fintype E]
theorem margin {η:ℝ}(ep:0 < η)(m n:ℕ)(E:Type)[Fintype E]:
    ∃δ:ℝ,0 < δ ∧ ∀a:ℝ,0 ≤ a  →  a ≤ δ  →  radius n m E a ≤ min 1 (η/4):=by
  let M:=(levels n:ℝ)*span n m E
  have mn:0 ≤ M:=mul_nonneg (Nat.cast_nonneg _) span_nonneg
  have clear:0 < min 1 (η/4):=lt_min one_pos (by positivity)
  refine ⟨min 1 (η/4)/(1+M),div_pos clear (by positivity),?_⟩
  intro a ap paid
  have val:a*(1+M) ≤ min 1 (η/4):=(le_div_iff₀ (by positivity)).mp paid
  unfold radius
  calc _=a*M:=by dsimp [M];ring
       _ ≤ a*(1+M):=by gcongr;linarith
       _ ≤ _:=val

theorem actual (sched:Schedule)(j m:ℕ)(ref:E → E4){r t η M:ℝ}(rp:0 < r)(rt:r ≤ t)
    (X:Points n)(reach:∀i,‖r • X i‖ ≤ M*t)(spaced:∀i k,i≠k  → η ≤ dist (X i) (X k))
    (room:radius n m E (sched.a j/r) ≤ min 1 (η/4)):
    let prog:=sold m ref (div_pos (sched.a_pos j) rp) X
    ∀z:prog.sample,∃o:Fin n →  Cover,
      tag (sched.a j) o=r • prog.site z ∧ tag (sched.a j) o∈generic n ∧ tag (sched.a j) o∈conf n ∧
      (∀i,‖sched.gridPoint j (o i)‖ ≤ (M+1)*t) ∧
      (Pairwise fun i k=>(η/2)*r ≤ ‖sched.gridPoint j (o i)-sched.gridPoint j (o k)‖):=by
  intro prog z
  obtain ⟨o,placed⟩:=WilsonSeparatedGridDesign.actual sched j m ref rp X z
  have atSite(i:Fin n):r • prog.site z i=sched.gridPoint j (o i):=congrFun placed i
  have exactSite:tag (sched.a j) o=r • prog.site z:=by
    apply PiLp.ext;intro i;exact (atSite i).symm
  obtain ⟨ties,near⟩:=(checked m ref (div_pos (sched.a_pos j) rp) X).1 z
  have distinct:tag (sched.a j) o∈generic n:=by
    rw [exactSite];intro a i k eq
    change r*(prog.site z i a)=r*(prog.site z k a) at eq
    exact Ties.all_clear (fun i=>prog.site z i) ref _ ties a (mul_left_cancel₀ rp.ne' eq)
  refine ⟨o,exactSite,distinct,generic_conf n distinct,?_,?_⟩
  · intro i;rw [←atSite i]
    have bounds:=((PiLp.dist_apply_le (prog.site z) X i).trans near).trans (room.trans (min_le_left ..))
    have step:‖prog.site z i‖ ≤ ‖X i‖+1:=by
      have triangle:=dist_triangle (prog.site z i) (X i) 0
      rw [dist_zero_right,dist_zero_right] at triangle
      linarith only [triangle,bounds]
    have cost:=reach i
    rw [norm_smul,Real.norm_of_nonneg rp.le] at cost ⊢
    calc r*‖prog.site z i‖ ≤ r*(‖X i‖+1):=mul_le_mul_of_nonneg_left step rp.le
         _ ≤ (M+1)*t:=by linarith only [cost,rt]
  · intro i k neq
    have left:=((PiLp.dist_apply_le (prog.site z) X i).trans near).trans (room.trans (min_le_right ..))
    have right:=((PiLp.dist_apply_le (prog.site z) X k).trans near).trans (room.trans (min_le_right ..))
    have apart:η/2 ≤ dist (prog.site z i) (prog.site z k):=by
      have first:=dist_triangle (X i) (prog.site z i) (X k)
      rw [dist_comm (X i) (prog.site z i)] at first
      linarith only [spaced i k neq,first,dist_triangle (prog.site z i) (prog.site z k) (X k),left,right]
    rw [←atSite i,←atSite k,←smul_sub,norm_smul,Real.norm_of_nonneg rp.le,mul_comm]
    exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using apart) rp.le

end YM.Integration.WilsonMovingForkScreenedSites
