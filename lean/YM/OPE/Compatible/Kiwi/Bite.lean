import YM.OPE.Compatible.Kiwi.Smoke
import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Depth
/-!
# Ordered Wick moment. Covariance limit, Wick bundle
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Saga Shrew Maxwell Maxwell.Free
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {N:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I J:Type}{ℓ:Filter I}
lemma bond_cutL (p ℓ : WickPol G)(q:Probe G j)(x y:E4)(h:x≠y):
   bond G x y (Maxwell.symbol j q*p) ℓ=bond G x y p (eat q x y ℓ):=by
      let F:=Fin.cons (α:=fun _ : Fin 2=> WickPol G) p (fun _ : Fin 1=>ℓ); have he:= moment_one q F 0 (pair_ok h); simp only [bond_eval]; change Maxwell.Wick.moment _ _ _ = _; rw [show Fin.cons _ _=update F 0 (Maxwell.symbol j q * F 0) from ?_,he]; swap; · funext i;fin_cases i<;>simp [F]
      rw [Finset.sum_eq_single 1]; congr 1; funext i; fin_cases i <;> simp [F, pairPoints, Points.cons]
      · intro j hj hy; exfalso; fin_cases j<;>simp_all
      simp
lemma bond_cutR (p ℓ : WickPol G)(q:Probe G j)(x y:E4)(h:x≠y):
   bond G x y p (Maxwell.symbol j q*ℓ)=bond G x y (eat q y x p) ℓ:=by
      let F:=Fin.cons (α:=fun _ : Fin 2=> WickPol G) p (fun _ : Fin 1=>ℓ); have he:= moment_one q F 1 (pair_ok h); rw [bond_eval,bond_eval,show Fin.cons _ _=update F 1 (Maxwell.symbol j q * F 1) from ?_,he]; swap; · funext i;fin_cases i<;>simp [F]
      rw [Finset.sum_eq_single 0]; congr 1; funext i; fin_cases i <;> simp [F,pairPoints,Points.cons]
      · intro j hj hy; exfalso; fin_cases j<;>simp_all
      simp
open Finset
variable [LinearOrder I]
def choms (p:I→Reed G)(s:Finset I):WickPol G:=∏ i∈s,planeLeg (p i)
lemma chom_one (A:I→Reed G){p:I}{s:Finset I}(hx:p∈s):choms A s=planeLeg (A p) *choms A (s.erase p):=(Finset.mul_prod_erase s (planeLeg ∘ A) hx).symm
lemma eat_choms (A:I→Reed G)(p:Reed G)(x y:E4)(hp:x≠y)(s:Finset I):eat (rayLeg p) x y (choms A s)=∑ i∈s,(Maxwell.Free.K (rayLeg p) (rayLeg (A i)) x y:ℂ) • choms A (s.erase i):=by
    induction s using Finset.induction with
    | empty=> simp [choms]
    | insert a s ha ih=>
           rw [chom_one A (p:=a) (s:=insert a s) (mem_insert_self ..),Derivation.leibniz, sum_insert ha,erase_insert ha,ih, eat_symbol (rayLeg p) (rayLeg (A a)) hp]; simp_rw [smul_eq_mul,Finset.mul_sum]; rw [add_comm]; apply congr_arg₂ (·+·); rw [mul_comm]; rw [MvPolynomial.C_mul']
           apply sum_congr rfl; intro i hi; rw [erase_insert_of_ne (by aesop)]; unfold choms; rw [Finset.prod_insert (show a ∉ s.erase i from by simp [ha]), mul_smul_comm]
lemma chom_bond (A:I→Reed G)(x y:E4)(hh:x≠y)(s: Finset I)(a:Reed G)(v: WickPol G): bond G x y (planeLeg a*v) (choms A s)= ∑ i∈s, (Maxwell.Free.K (rayLeg a) (rayLeg (A i)) x y:ℂ)* bond G x y v (choms A (s.erase i)):=by rw [bond_cutL v _ _ x y hh,eat_choms _ _ x y hh,map_sum]; exact sum_congr rfl fun i _=> map_smul ..
lemma unitsB (x y:E4)(G:Gauge) : bond G x y 1 1=1:=by
       rw [bond_eval]; rw [show Fin.cons _ _= fun i : Fin 2=> (1:WickPol G) from funext fun i=>by fin_cases i<;>rfl]; exact Maxwell.Wick.constants ..
lemma units_drift (x y:E4)(hh:x≠y) (s:Finset I)(ht:s.Nonempty)(A:I→Reed G):bond G x y 1 (choms A s)=0:=by
       rw [chom_one A (Finset.min'_mem _ ht),bond_cutR 1 _ _ x y hh]; simp
end YM.OPE.Prairies
