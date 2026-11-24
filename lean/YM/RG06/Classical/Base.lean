import YM.RG06.Classical.Connection
import YM.RG06.Classical.Stamp

/-! # Free end of the dress tour -/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.ClassicalOn
open Analysis Function Labels Continuum Maxwell Tensor Vectorial
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius Topology
variable {G:Gauge}
lemma parked (J:Jet G)(k:ℕ): data 0 (radField (k+2) J) k=0:=by
 funext i
 unfold data scene; simp only [covariant,zero_smul,add_zero, curvature]
 -- radial linear homogeneous grades.
 let A (j:ℕ)(a:Axis):= (J j).value a
 let R:= Finset.range (k+1)
 have he: radField (k+2) J=fun i=>∑ j∈R,A j i:=by funext i x; unfold radField Source.potential R A; rw [Finset.sum_apply, show k+2-1=k+1 by omega]
 have hA(j)(a:Axis):Level (j+1) (A j a):=Level.tax ..
 rw [he]
 simp_rw [par_sum R _ (fun p _=> (hA p _).smooth), ← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
 have hh(j a b): Level j (par a (A j b)+-par b (A j a)):=((hA j b).advance a).add ((hA j a).advance b|>.neg)
 simp_rw [par_sum R _ (fun p _=> (hh p _ _).smooth)]
 rw [part_sum (E:=G.Color) (Finset.univ:Finset Axis) (fun m=>∑ j∈R,par m (par m (A j i)+-par i (A j m))) (fun m _=>Good_sum R _ (fun j _=> (hh j m i).smooth.par m))]
 apply Finset.sum_eq_zero; intro a _; rw [part_sum R _ (fun j _=> (hh j a i).smooth.par a)]; apply Finset.sum_eq_zero; intro j hj; rcases j with _|j
 · rw [Level.bottom (hh 0 a i) a];exact (Secret.zero (k+1)).veiled _ (Nat.lt_succ_self _)
 exact part_spill ((hh (j+1) a i).advance a) (show k≠j by have he:=Finset.mem_range.mp hj;omega)

lemma charge_base (k:ℕ){E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](a:ℕ): ClassicalOn.inverse k a (0:E4→E)=0:=by
 induction k using Nat.strong_induction_on generalizing a with
 | h k H=>
   rw [ClassicalOn.inverse];split
   · unfold mask; ext; simp
   next e=>
     rw [lap_bottom (Level.zero (E:=E) 0) (show 0<2 by norm_num),H _ (by omega)]; unfold mask; ext; simp
lemma foyer (J:Jet G)(k:ℕ):invoice 0 J k=0:=by
 unfold invoice retract
 apply Subtype.ext
 change (fun i=> Tensor.coeff (Vectorial.chart k (data 0 (radField (k+2) J) k) i) (k+2) 0)=0
 rw [parked]
 unfold Vectorial.chart Vectorial.raw Vectorial.jem Vectorial.raw Vectorial.formal Vectorial.area; simp only [Pi.zero_apply,smul_zero,sub_zero];
 have he:ClassicalOn.inverse (k+1) 0 (fun _:E4=>(0:G.Color))=0:=charge_base ..
 simp_rw [he,sub_zero,smul_zero, Level.bottom (Level.zero (E:=G.Color) 0)]
 simp only [Finset.sum_const_zero,Pi.zero_apply,smul_zero]
 have ht(i:Axis):par i (fun _:E4=> (0:G.Color))=0:=Level.bottom (Level.zero (E:=G.Color) 0) i
 simp only [ht, sub_zero]; funext i; exact Tensor.coeff_zero (F:=G.Color) (k+2) (0:E4)

@[simp] theorem ultimate(J:Jet G):attire 0 J= J:=by funext i;rcases i with _|i; exact accounts_base ..; rw [accounts,foyer,sub_zero]
@[simp] theorem dawn(J:Jet G):out 0 J=J:=by funext i; rcases i with _|i; rfl; change _+invoice 0 J i= _; rw [foyer,add_zero]
end YM.RG06.ClassicalOn
