import YM.Integration.WilsonThermometerWeakCompactRoom

/-! Finite sums over the genuine four directions of each independently placed
child are sufficient to bound the norm of the full tested position derivative. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakCoordinateNorm
open Finset
open scoped Classical BigOperators
variable {n k:ℕ}{Y:Type*}[NormedAddCommGroup Y][NormedSpace ℝ Y]

def letter (a:Fin n×Axis):Points n:=points (Pi.single a.1 (basis a.2))

theorem split (x:Points n):x=∑ a:Fin n×Axis,(x a.1 a.2) • letter a:=by
  rw [Fintype.sum_prod_type]
  ext i j
  simp [letter,Pi.single_apply,basis_eq,Finset.sum_ite_irrel]

theorem read (A:ContinuousMultilinearMap ℝ (fun _:Fin k=>Points n) Y){B:ℝ}(bp:0≤B)
    (bound:∀a:Fin k→Fin n×Axis,‖A (fun i=>letter (a i))‖≤B):
    ‖A‖≤((Fintype.card (Fin k→Fin n×Axis):ℝ)*B):=by
  refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (Nat.cast_nonneg _) bp) (fun x=>?_)
  let c (i:Fin k)(p:Fin n×Axis):=(x i) p.1 p.2
  have against (i:Fin k)(p:Fin n×Axis):‖c i p‖≤‖x i‖:=
    (PiLp.norm_apply_le ((x i) p.1) p.2).trans (PiLp.norm_apply_le (x i) p.1)
  have expand:A x=∑ a:Fin k→Fin n×Axis,(∏i,c i (a i)) • A (fun i=>letter (a i)):=by
    let V (i:Fin k)(p:Fin n×Axis):=c i p • letter p
    have hx:x=fun i=>∑p,V i p:=funext (fun i=>split (x i))
    change A.toMultilinearMap x=_
    rw [hx,A.toMultilinearMap.map_sum V]
    apply Finset.sum_congr rfl
    intro a _
    exact A.toMultilinearMap.map_smul_univ (fun i=>c i (a i)) (fun i=>letter (a i))
  rw [expand]
  calc
    _≤∑a:Fin k→Fin n×Axis,‖(∏i,c i (a i)) • A (fun i=>letter (a i))‖:=norm_sum_le .. 
    _≤∑_a:Fin k→Fin n×Axis,(∏i,‖x i‖)*B:=by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul,norm_prod]
      exact mul_le_mul (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>against i (a i))) (bound a) (norm_nonneg _) (Finset.prod_nonneg fun _ _=>norm_nonneg _)
    _=_:=by simp;ring

end YM.Integration.WilsonThermometerWeakCoordinateNorm
end
