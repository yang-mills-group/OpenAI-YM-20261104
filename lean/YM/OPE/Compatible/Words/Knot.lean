import YM.OPE.Compatible.Begun.Ell
/-! # Gaussian algebra

Products via exp(-Δ/2). General nilpotent finite trans modules.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt
open MeasureTheory Function Finset Filter Module
open scoped Topology BigOperators Classical ContDiff
-- Let U,T act lowering the filtration degree ONE. state Ξ with cap $n$. Use Binomial
variable {E F:Type} [AddCommGroup E][Module ℝ E][AddCommGroup F][Module ℝ F] -- can generalize later
abbrev fixExp (A:Module.End ℝ E)(t:ℝ)(n:ℕ) : Module.End ℝ E := ∑ i∈range (n+1), (t^i/(i.factorial:ℝ)) • (A^i)
lemma Hflow (A:End ℝ E)(x:E)(t:ℝ)(n:ℕ): fixExp A t n x=∑ i∈range (n+1),(t^i/(i.factorial:ℝ)) • ((A^i) x):=by unfold fixExp; simp
-- filament proper filtration supports partial commuting
variable (V:ℕ→Submodule ℝ E)
def reduces (A:End ℝ E):Prop:=∀ i:ℕ,∀ x∈ V i,(i=0→ A x=0)∧A x∈V (i-1)
variable {V}
lemma iterateD {A: End ℝ E}(h:reduces V A) {x:E}{d:ℕ}(hp:x∈ V d)(i:ℕ): (A^i) x∈V (d-i) ∧ (d < i→ (A^i) x=0):=by
     induction i with
     | zero=> exact ⟨by simpa, by omega⟩
     | succ i ih=>
         rw [pow_succ', Module.End.mul_apply, show d-(i+1)=d-i-1 by omega]; exact ⟨(h _ _ ih.1).2,fun hx=>(h _ _ ih.1).1 (by omega)⟩
variable {A B:Module.End ℝ E} (h:reduces V A)(hp:reduces V B)
lemma reduces.plus : reduces V A → reduces V B → reduces V (A+B):= fun h hh i x hx=>⟨fun hy=>by simp [ (h _ _ hx).1 hy,(hh _ _ hx).1 hy], (V _).add_mem (h _ _ hx).2 (hh _ _ hx).2⟩
variable (he:∀ i:ℕ,∀ x∈ V i,A (B x)=B (A x)) {d:ℕ} (x:E) (hg:x∈V d)
include hp he hg
lemma powersA (n:ℕ): A ((B^n) x)=(B^n) (A x):=by
     induction n with
     | zero=>simp
     | succ n ih=> rw [pow_succ',End.mul_apply,he _ _ (iterateD hp hg n).1,End.mul_apply,ih]
include h
lemma powerBin (n:ℕ): ((A+B)^n) x=∑ i∈range (n+1),(n.choose i) • (A^i) ((B^(n-i)) x):=by
     -- choose commutativity at restricted module or range recurrence by Pascal
     induction n with
     | zero=>simp
     | succ n ih=>
          let z(j k:ℕ):=(A^j) ((B^k) x); have hc(j k): B (z j k)= z j (k+1):=by unfold z; rw [powersA h (fun i y hy=>(he i y hy).symm) _ (iterateD hp hg k).1 j, pow_succ', End.mul_apply]
          have ht(j k): A (z j k)=z (j+1) k:=by unfold z; rw [pow_succ',End.mul_apply]
          have hz : B (∑ i∈range (n+1), n.choose i • z i (n-i))=∑ i∈range (n+2),n.choose i • z i (n+1-i):=by rw [map_sum,sum_range_succ (n:=n+1)]; simp only [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n),zero_smul,add_zero]; apply sum_congr rfl; intro i hi; have he:=mem_range.mp hi; rw [map_nsmul, hc, show n-i+1=n+1-i by omega]
          rw [pow_succ', End.mul_apply, ih,LinearMap.add_apply, show B _= _ from hz, map_sum, sum_range_succ' (n:=n+1)]; -- rw wrong matching
          conv_rhs=>rw [sum_range_succ']
          rw [← add_assoc, ← sum_add_distrib]; apply congr_arg₂ (·+·); swap; · simp only [Nat.choose_zero_right]; rfl
          apply sum_congr rfl; intro i hi; change A (n.choose i • z i _)+_= _; rw [map_nsmul,ht,Nat.choose,add_smul, Nat.succ_sub_succ]
lemma equations (t:ℝ)(n:ℕ)(hd:d ≤ n): fixExp A t n (fixExp B t n x)=fixExp (A+B) t n x:=by
     let U:Finset (ℕ×ℕ):=range (n+1) ×ˢ range (n+1); let f(i):ℝ:=t^i/(i.factorial:ℝ); let g(i:ℕ×ℕ):=i.1+i.2; let p(i:ℕ×ℕ):E:= f i.1 • (A^i.1) (f i.2 • ((B^i.2) x)); let Z:=U.filter fun i=>g i≤n
     rw [Hflow,Hflow, Hflow]; let a(i j:ℕ):= p (i,j); rw [show ∑ i ∈ range (n+1), ((t^i)/(i.factorial:ℝ)) • (A^i) (∑ i∈range (n+1),(t^i/(i.factorial:ℝ)) • ((B^i) x))= ∑ i∈ U,p i from ?_]; swap
     · rw [Finset.sum_product]; refine sum_congr rfl ?_; intro i _; simp_rw [map_sum, Finset.smul_sum];rfl
     rw [← (sum_subset (filter_subset _ _) (f:=p) (s₁:=Z) (fun i hi hs=>show p i=0 from ?_))]; swap
     · have hx:g i>n:=lt_of_not_ge fun h=> hs (mem_filter.mpr ⟨hi,h⟩); have hk:= iterateD hp hg i.2; have hv:= iterateD h hk.1 i.1; unfold p; rw [map_smul]; unfold g at hx; by_cases H:i.2>d; rw [hk.2 H,map_zero,smul_zero,smul_zero]; rw [hv.2 (by omega),smul_zero,smul_zero]
     have ht:∀ x∈Z,g x ∈range (n+1):=fun i hi=> mem_range.mpr (Nat.lt_succ_of_le ((mem_filter.mp hi).2)); rw [← sum_fiberwise_of_maps_to ht p]; refine Finset.sum_congr rfl ?_; intro k hk; have hk': k≤n:=Nat.le_of_lt_succ (mem_range.mp hk)
     rw [powerBin h hp he x hg k, Finset.smul_sum]; let U':=Z.filter fun i=>g i=k; symm; change _=∑ i∈U',p i; apply Finset.sum_bij (fun (i:ℕ) (_:i∈range (k+1))=>(i,k-i))
     · intro i hi; simp only [mem_range] at hk hi; simp only [Z,U',U,g,mem_filter,mem_range,mem_product];omega
     · intro _ _ _ _ h; exact (Prod.mk.inj h).1
     · rintro ⟨i,j⟩ hg; have hj : i+j=k:= (mem_filter.mp hg).2; exact ⟨i,mem_range.mpr (by omega), Prod.ext rfl (show k-i=j by omega)⟩
     intro i hi; have hv:i≤k:=by have hg:= mem_range.mp hi; omega
     have hz:(Nat.choose k i:ℝ)*i.factorial*(k-i).factorial=k.factorial:= by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hv
     rw [← Nat.cast_smul_eq_nsmul ℝ (Nat.choose k i),smul_smul]; unfold p; rw [map_smul,smul_smul]; congr 1; unfold f; dsimp only; field_simp; rw [← hz]; rw [show t^k=t^i*t^(k-i) from (by rw [←pow_add,Nat.add_sub_of_le hv])]; ring
omit he h hp hg in
lemma flaxZero (v:E)(t:ℝ)(n:ℕ): fixExp (0:End ℝ E) t n v=v:=by rw [Hflow,sum_eq_single 0]; simp; intro i _ hi; simp [zero_pow hi];simp
omit he hp in
lemma negatives (t:ℝ)(n:ℕ)(hd:d≤n): fixExp A t n (fixExp (-A) t n x)=x:=by
     have hh:reduces V (-A):=fun i y hy=> ⟨fun hx=> by rw [LinearMap.neg_apply, (h i y hy).1 hx,neg_zero],(V _).neg_mem ((h i y hy).2)⟩
     rw [equations h hh (fun _ _ _=> by simp) x hg _ _ hd,add_neg_cancel,flaxZero]
end YM.OPE.Silt
