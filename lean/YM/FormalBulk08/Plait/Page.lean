import YM.FormalBulk08.Plait.Wax
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! External tallies. For first loop the Hessian is the only active tower
needed *after centering*. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Plait
open Function Wick Orb MvPolynomial
open scoped BigOperators Classical
variable {I V T : Type*} {n m k : ℕ}
-- TypeR universe second first
abbrev Pairs (V I:Type*) := MvPolynomial V (TypeR I)

def Tally (p:Pairs V I)(n):= ((sumAlgEquiv ℝ V I).symm p).IsHomogeneous n
lemma Tally.zero (i): Tally (0:Pairs V I) i:=by simp [Tally,isHomogeneous_zero]
lemma Tally.xt {i : V} : Tally (X (R:=TypeR I) i) 1 := by simp [Tally,isHomogeneous_X]
variable {p q: Pairs V I}
lemma Tally.add (h:Tally p n)(hx:Tally q n): Tally (p+q) n:= by unfold Tally; rw [_root_.map_add]; exact IsHomogeneous.add h hx
lemma Tally.mul (h:Tally p n)(hx:Tally q k): Tally (p*q) (n+k):= by unfold Tally; rw [_root_.map_mul]; exact IsHomogeneous.mul h hx
lemma Tally.sub (h:Tally p n)(hx:Tally q n): Tally (p-q) n:= by unfold Tally;rw [_root_.map_sub]; exact IsHomogeneous.sub h hx
lemma Tally.neg (h:Tally p n): Tally (-p) n:= by unfold Tally;rw [_root_.map_neg]; exact IsHomogeneous.neg h
lemma Tally.sum {p:T→Pairs V I}(S:Finset T)(h:∀ i∈ S,Tally (p i) n): Tally (∑ i∈S,p i) n:= by unfold Tally; rw [_root_.map_sum]; exact IsHomogeneous.sum _ _ _ h
lemma Tally.base {p:TypeR I}(h:p.IsHomogeneous n): Tally (C (σ:=V) p) n:= by
   have hp:(sumAlgEquiv ℝ V I).symm (C (σ:=V) p)=MvPolynomial.rename Sum.inr p:= by apply (sumAlgEquiv ℝ V I).injective; rw [AlgEquiv.apply_symm_apply]; exact (DFunLike.congr_fun (sumAlgEquiv_comp_rename_inr ℝ V I) p).symm
   unfold Tally; rw [hp]; exact h.rename_isHomogeneous
lemma remap {p:Pairs V I}: constantCoeff p=aftEval V I ((sumAlgEquiv ℝ V I).symm p):= by
   rw [show constantCoeff p=constantCoeff (sumAlgEquiv _ _ _ ((sumAlgEquiv _ _ _).symm p)) from congr_arg constantCoeff ((sumAlgEquiv _ _ _).apply_symm_apply p).symm]; generalize (sumAlgEquiv ℝ V I).symm p=g; induction g using MvPolynomial.induction_on with
   | C c=>simp [aftEval]
   | add p q hp hq=> simp only [_root_.map_add,hp,hq]
   | mul_X p i hp=> simp only [_root_.map_mul,hp]; cases i <;> simp [aftEval]
lemma Tally.constant (h:Tally p n): (constantCoeff p).IsHomogeneous n := by
   rw [remap]; simpa only [one_mul] using! IsHomogeneous.aeval (n:=1) h (Sum.elim (0:V→TypeR I) X) (fun i=> by cases i <;> simp [isHomogeneous_zero,isHomogeneous_X])
lemma Tally.step (h:Tally p n)(i:V): Tally (pderiv i p) (n-1):= by
   have he:(sumAlgEquiv ℝ V I).symm (pderiv i p)=pderiv (Sum.inl i) ((sumAlgEquiv ℝ V I).symm p):= by apply (sumAlgEquiv _ _ _).injective; simp [← pderiv_sumAlgEquiv]
   unfold Tally; rw [he]; exact IsHomogeneous.pderiv h
lemma divide_coeff {p:Pairs V I}(i:V)(d: V →₀ ℕ): coeff (d+Finsupp.single i 1) p=C (((d i+1:ℕ):ℝ)⁻¹)*coeff d (pderiv i p):= by
   rw [coeff_pderiv,←Nat.cast_succ, ←_root_.map_natCast C (d i+1),mul_left_comm, ← _root_.map_mul,inv_mul_cancel₀ (by exact_mod_cast (by omega : d i+1≠0)),_root_.map_one,mul_one]
lemma Tally.active {p:Pairs V I}(h:Tally p n)(d: V →₀ ℕ): IsHomogeneous (coeff d p) (n-d.degree):= by
   suffices H: ∀ k (d: V →₀ ℕ) (n) (p:Pairs V I),Tally p n → d.degree≤k→ IsHomogeneous (coeff d p) (n-d.degree) from H _ _ _ _ h le_rfl
   intro k; induction k using Nat.strong_induction_on with
   | _ k ih=>
     intro d n p h he
     by_cases hz:d=0
     · subst d; simpa only [_root_.map_zero,tsub_zero] using! Tally.constant h
     obtain ⟨i,d,rfl⟩:=pin_drop d hz; rw [_root_.map_add,Finsupp.degree_single] at he; rw [divide_coeff i d,_root_.map_add,Finsupp.degree_single,show n-(Finsupp.degree d+1)=n-1-Finsupp.degree d by omega]; exact IsHomogeneous.C_mul (ih d.degree (by omega) d (n-1) (pderiv i p) (h.step i) le_rfl) _

-- vanish active grades
lemma graded_price (S:Finset T)(f:T→TypeR I)(h:∀ i∈S,totalDegree (f i)≤k): totalDegree (∑ i∈ S,f i)≤ k:= by
   induction S using Finset.induction_on with
   | empty=>simp
   | insert i s hi ih=> rw [Finset.sum_insert hi]; exact (totalDegree_add ..).trans (max_le (h i (by simp)) (ih (fun j hj=> h j (Finset.mem_insert_of_mem hj))))

def Rental (p:Pairs V I)(n:ℕ):= ∀ d,totalDegree (coeff d p)≤n
lemma Rental.add (h:Rental p n)(hx:Rental q n): Rental (p+q) n:= by intro d; rw [coeff_add]; exact (totalDegree_add ..).trans (max_le (h d) (hx d))
lemma Rental.mul (h:Rental p n)(hx:Rental q k): Rental (p*q) (n+k):= by intro d; rw [coeff_mul]; apply graded_price; intro i _; exact (totalDegree_mul ..).trans (add_le_add (h _) (hx _))
lemma Rental.money (h:Rental p n)(hx:n≤k): Rental p k:= fun d=> (h d).trans hx
lemma Rental.C (p:TypeR I)(h:p.totalDegree≤k): Rental (V:=V) (MvPolynomial.C p) k:= by
   intro d; by_cases hz:d=0 <;> simp [*,coeff_C,eq_comm]
lemma Tally.vanishLe (h:Tally p n)(hp:∀ (d: V →₀ ℕ),d.degree<m→ coeff d p=0): Rental p (n-m):= by
   intro d; by_cases hz:d.degree<m
   · simp [hp d hz]
   exact ((h.active d).totalDegree_le).trans (by omega)
lemma Tally.centers (h:Tally p n): Rental (p-C (constantCoeff p)) (n-1):= (h.sub (Tally.base h.constant)).vanishLe (fun d hd=> by
    by_cases hz:d=0
    · subst d; change constantCoeff (p-C (constantCoeff p))=_; rw [_root_.map_sub, constantCoeff_C,sub_self]
    obtain ⟨i,w,rfl⟩:=pin_drop d hz; rw [_root_.map_add,Finsupp.degree_single] at hd; omega)
lemma tip_bottom (h:Tally p (n+3))(hp:constantCoeff p=0)
   (hx:∀ i:V,constantCoeff (pderiv i p)=0)(ht:∀ i j:V,constantCoeff (pderiv i (pderiv j p))=0): Rental p n:= by
    have hu(d: V →₀ ℕ)(hd:d.degree<3) : coeff d p=0:= by
       by_cases hz:d=0
       · subst d;exact hp
       obtain ⟨i,w,rfl⟩:=pin_drop d hz; rw [_root_.map_add,Finsupp.degree_single] at hd; rw [divide_coeff i w]; by_cases hz:w=0
       · subst w;rw [show coeff 0 _=_ from hx i,mul_zero]
       obtain ⟨j,v,rfl⟩:=pin_drop w hz;rw [_root_.map_add,Finsupp.degree_single] at hd;rw [divide_coeff j v]; by_cases he:v=0
       · subst v; rw [show coeff 0 _=_ from ht j i,mul_zero,mul_zero]
       obtain ⟨k,w,rfl⟩:=pin_drop v he;rw [_root_.map_add,Finsupp.degree_single] at hd;omega
    simpa only [Nat.add_sub_cancel] using h.vanishLe hu
end YM.FormalBulk08.Plait
