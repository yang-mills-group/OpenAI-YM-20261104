import YM.FormalBulk08.Lava.Splash

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lava
open Series Wick Orb Function
open MvPolynomial
open scoped BigOperators Classical
variable {V : Type*} {m n : ℕ}
def clutch (T : Tile V m) (K : Tile V n) : Tile V (m+n) := fun v=> T (v ∘ Fin.castAdd n)*K (v ∘ Fin.natAdd m)
def castle (V : Type*) (m n : ℕ) : chain V m × chain V n ≃ chain V (m+n) where
   toFun i:= Fin.append i.1 i.2
   invFun v:=(v ∘ Fin.castAdd n, v ∘ Fin.natAdd m)
   left_inv i:= by ext <;> simp
   right_inv v:= by funext i; cases i using Fin.addCases <;> simp
variable [Fintype V]
lemma facade_clutch (T : Tile V m) (K : Tile V n) : facade (m+n) (clutch T K)=facade m T * facade n K := by
   simp_rw [facade_eq]; rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]; rw [←Fintype.sum_prod_type']; symm
   refine Fintype.sum_equiv (castle V m n) _ _ fun i=>?_
   simp [clutch,castle,Function.comp_def,cards, Fin.prod_univ_add]; ring
omit [Fintype V] in
lemma comp_fuses (i : V) (r : ℕ) (p : TypeR V) : homogeneousComponent r (pderiv i p)= pderiv i (homogeneousComponent (r+1) p) := by
   ext1 n; simp only [coeff_homogeneousComponent, coeff_pderiv,map_add,Finsupp.degree_single,Nat.add_left_inj,ite_mul,zero_mul]
-- bounded expansion
omit [Fintype V] in
lemma cemento (p : TypeR V) (n : ℕ) (h : p.totalDegree < n) : ∑ i∈Finset.range n,homogeneousComponent i p=p := by
   conv_rhs => rw [←sum_homogeneousComponent p]
   symm; exact Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj=> homogeneousComponent_eq_zero _ _ (by simp at hj;omega)
omit [Fintype V] in
lemma comp_glue (r : ℕ) (p q : TypeR V) : homogeneousComponent r (p*q)= ∑ a∈Finset.antidiagonal r, homogeneousComponent a.1 p*homogeneousComponent a.2 q := by
   let B:=max p.totalDegree (max q.totalDegree r)+1
   let I:= Finset.range B
   have h1 : p.totalDegree < B:= by unfold B;omega
   have h2 : q.totalDegree < B:= by unfold B;omega
   have h3 : r < B:= by unfold B;omega
   conv_lhs => rw [← cemento p B h1,← cemento q B h2];
   simp_rw [Finset.sum_mul, Finset.mul_sum,map_sum];simp_rw [homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous _ p).mul (homogeneousComponent_isHomogeneous _ q))]; rw [← Finset.sum_product']
   let A:= fun a:ℕ × ℕ => if r=a.1+a.2 then homogeneousComponent a.1 p*homogeneousComponent a.2 q else 0
   change ∑ i ∈ I ×ˢ I,A i= _
   rw [←Finset.sum_subset (s₁:=Finset.antidiagonal r) (s₂:=I×ˢ I) (by intro i hi; rw [Finset.mem_antidiagonal] at hi; simp [I];omega) (fun i _ hi=> if_neg (Ne.symm (fun he=>hi (Finset.mem_antidiagonal.mpr he))))];exact Finset.sum_congr rfl fun i hi=> if_pos (Finset.mem_antidiagonal.mp hi).symm
end YM.FormalBulk08.Lava
