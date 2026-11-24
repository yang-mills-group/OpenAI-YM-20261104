import YM.RG11Proof.Nodes.Forest
import YM.RG11Proof.Scale.Grades
import YM.RG11Proof.Horizon.Restrict
/-!
# Multi-arity composite product frames

For OPE & nested operations. Keep any coupling/order; cost may depend
on arity cardinalities.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG11.Nodes
open scoped BigOperators Classical
open PowerSeries YM.RG11.Jets YM.RG11.Scale Function

variable {I J K R:Type*} {n:ℕ}
variable [CommSemiring R]

def cluster (s:Square J R)(n:ℕ):Square (Fin n→J) R:= Matrix.of (cross s)

variable [Fintype J]
 theorem cluster_mul (a b:Square J R):cluster (a*b) n = cluster a n * cluster b n:=by
    ext i j
    simp only [cluster,cross,Matrix.of_apply,Matrix.mul_apply]
    rw [Finset.prod_univ_sum (fun _:Fin n=> (Finset.univ (α:=J))) (fun x (z:J)=>a (i x) z * b z (j x))]
    refine Finset.sum_congr rfl (fun z _=> ?_)
    rw [Finset.prod_mul_distrib]
 theorem cluster_one [DecidableEq J]: cluster (1:Square J R) n=(1:Square (Fin n→J) R):=by
   classical
   ext i j
   simp only [cluster,cross,Matrix.of_apply,Matrix.one_apply]
   split
   · rename_i h; try subst j
     simp
   rename_i h
   obtain ⟨z,hz⟩:= Function.ne_iff.mp h
   exact Finset.prod_eq_zero (Finset.mem_univ z) (if_neg hz)

-- engineer
def cluster_weight (v:J→ℕ)(i:Fin n→J):ℕ:=∑ k,v (i k)

 theorem cluster_grade {s:Square J R}{v:J→ℕ}(he:graded v s): graded (cluster_weight v) (cluster s n):= by
   intro i j h
   obtain ⟨k,hk⟩ : ∃ k,v (i k) ≠ v (j k) := by
     by_contra! h'; apply h; unfold cluster_weight; simp only [h']
   exact Finset.prod_eq_zero (Finset.mem_univ k) (@he _ _ hk)
end YM.RG11.Nodes
