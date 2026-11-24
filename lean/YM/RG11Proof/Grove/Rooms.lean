import YM.RG11Proof.Grove.Escrow
import YM.RG11Proof.Nodes.Ranks
/-!
# Correl conversion feeds every inserted slot through its own field horizon

Arity convention use `Fin (inner + exterior)`, incl `Fin (1+exterior)`
for replacement. No interchange of the actual perturbative estimates for
different heights or spots. This file slots algebra, C continuum afterward.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Grove
open scoped Classical BigOperators
open YM.RG11.Nodes YM.RG11.Jets YM.RG11.Scale PowerSeries
open Function
variable {I J R M:Type*}{n m:ℕ}

private theorem wedge [CommSemiring R][Fintype J] (A: reading J R (n+m))(s:Square J R)(v:Fin n→J)(w:Fin m→J):
    plant s A (Fin.append v w)=∑ i:Fin n→J, ∑ j:Fin m→J,A (Fin.append i j)*(cluster s n v i * cluster s m w j):=by
   unfold plant cluster cross
   rw [←Equiv.sum_comp (Fin.appendEquiv n m), Fintype.sum_prod_type]
   apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
   congr 1
   change (∏ k,s (Fin.append v w k) (Fin.append i j k))=_
   rw [Fin.prod_univ_add]; simp

-- permit restricting distinct incoming basis sizes at the same time.
private def parse {I K:Type*}(f:I↪K)(n:ℕ):(Fin n→I)↪(Fin n→K):=⟨fun t=>f∘t,fun _ _ h=>funext fun a=> f.injective (congrFun h a)⟩

private theorem docks [Fintype J]{G:Type*}[AddCommMonoid G][Fintype I](i:I↪J)(v:(Fin n→J)→G)(h:∀ x:(Fin n→J),x∉Set.range (parse i n) → v x=0): (∑ x,v x)=∑ t:Fin n→I, v (i ∘ t):=by
   change _ = ∑ t:Fin n→I,v (parse i n t)
   rw [← Finset.sum_map (Finset.univ (α:=Fin n→I)) (parse i n) v]
   exact (Finset.sum_subset (Finset.subset_univ _) (fun t _ ht=>h t (fun ⟨j,hj⟩=>ht (Finset.mem_map.mpr ⟨j,Finset.mem_univ _,hj⟩)))).symm

private theorem cluster_held [CommSemiring R](s:Square J R)(i:I↪J)(h:Horizon.Held i s):
    Horizon.Held (parse i n) (cluster s n):=by
  intro b j hj
  have he:∃a,j a∉ Set.range i:=by
    by_contra! he
    choose f hf using he; exact hj ⟨f,funext hf⟩
  obtain ⟨a,ha⟩:=he
  exact Finset.prod_eq_zero (Finset.mem_univ a) (h (b a) _ ha)

 theorem gathered [CommRing R][Fintype J][Fintype I][Fintype M](p:PowerSeries R)(A:reading J (PowerSeries R) (n+m))(s:Square J (PowerSeries R))(i:I↪J)(e:M↪J)(h:Horizon.Held i s)(H:Horizon.Held e s)
    (v:Fin n→I)(w:Fin m→M):
    plant s (PowerSeries.subst p ∘ A) (Fin.append (i ∘ v) (e ∘ w))=
      (cluster (Horizon.take i s) n * subs p (Matrix.of (fun (y:Fin n→I) (z:Fin m→M)=>A (Fin.append (i ∘ y) (e ∘ z)))) * Matrix.transpose (cluster (Horizon.take e s) m)) v w:=by
   rw [wedge]
   let F (y:Fin n→J)(z:Fin m→J):=PowerSeries.subst p (A (Fin.append y z)) * (cluster s n (i ∘ v) y *cluster s m (e ∘ w) z)
   change (∑ y,∑ z,F y z)= _
   rw [docks i (fun y=>∑ z,F y z) (fun y hy=> Finset.sum_eq_zero (fun z _=>by change PowerSeries.subst _ _ * (_ * _) = 0; rw [show cluster s n (i ∘ v) y = 0 from cluster_held s i h v y hy]; simp))]
   have ht(y:Fin n→I): (∑ z,F (i ∘ y) z)=∑ t:Fin m→M,F (i ∘ y) (e ∘ t):=docks e _ (fun z hz=> by unfold F; rw [show cluster s _ (e ∘ w) z=0 from cluster_held s e H w z hz]; simp)
   simp_rw [ht,Matrix.mul_apply,Matrix.transpose_apply, Finset.sum_mul,subs_apply,Matrix.of_apply]
   rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro j _
   simp only [F,cluster,Matrix.of_apply,cross,Horizon.take_apply,Function.comp_apply]; ring
end YM.RG11.Grove
