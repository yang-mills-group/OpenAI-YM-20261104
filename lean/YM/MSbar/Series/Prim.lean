import YM.MSbar.Series.Book
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Polynomial.Roots
/-! Evaluate finite power jets through a complex number, without claiming the theory converges!
Use only to polarize higher identities. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Category
open Function Finset
open scoped BigOperators Classical
variable {X Y Z : Type*} [AddCommGroup X][Module ℂ X][AddCommGroup Y][Module ℂ Y][AddCommGroup Z][Module ℂ Z] {f h: Form X} {g k:Form Y} {i j n m:ℕ}{c:ℂ}

def leaf (n:ℕ) (c:ℂ): Form X →ₗ[ℂ] X:={toFun:=fun x=>∑ i∈range (n+1), c^i • x i,map_add':=fun x y=>by simp [sum_add_distrib],map_smul':=fun u x=>by simp only [smul_sum, RingHom.id_apply,Pi.smul_apply]; apply sum_congr rfl; intro i _; apply smul_comm }
-- finite support eval
lemma leaf_eq : leaf n c f=∑ i∈ range (n+1),c^i• f i:=rfl
lemma leaflet (h:Cap i f)(hn: i≤j): leaf i c f= leaf j c f:=by rw [leaf_eq,leaf_eq]; exact sum_subset (range_mono (by omega)) (fun t ht hx=> by simp [h t (by simp at hx; omega)])
open Polynomial in -- collision funext
lemma detect (hf:Cap i f)(hh:∀ c:ℂ,leaf i c f=0): f=0:=by
    funext t; by_cases ht:t ∈ range (i+1)
    swap; exact hf t (by simp at ht; omega)
    by_contra he; obtain ⟨x,hx⟩:= Module.Projective.exists_dual_ne_zero ℂ he
    let p:= ∑ n∈ range (i+1), Polynomial.monomial n (x (f n)); have hp:p=0:=by
       apply Polynomial.funext; intro c; simp only [p,eval_finsetSum,eval_monomial,eval_zero]
       simp_rw [mul_comm (x _)]; have H:=congr_arg x (hh c); simpa only [leaf_eq,map_sum,map_smul,map_zero,smul_eq_mul] using H
    refine hx ?_; exact (show p.coeff t=x (f t) from (by simp [p,finsetSum_coeff,coeff_monomial, ht])).symm.trans (by simp [hp])
lemma direct (hf:Cap n f)(hh:Cap n h)(H:∀ c:ℂ,leaf n c f=leaf n c h): f=h:= sub_eq_zero.mp (detect (hf.sub hh) fun c=> by simp [H c])
lemma leaf_act(A:X→ₗ[ℂ] Y): leaf n c (act A f)= A (leaf n c f):=by simp [leaf_eq]
lemma leaf_sea(A:X→ₗ[ℂ] Y) : leaf (n+1) c (sea A f)=c • A (leaf n c f):=by
    simp only [leaf_eq,sum_range_succ' (f:=fun k=> c^k • sea A f k),pow_succ,sea_pos]; simp [smul_sum, mul_comm _ c, smul_smul]
lemma leaf_sea_large (A:X→ₗ[ℂ] Y)(hn: i<n)(h:Cap i f): leaf n c (sea A f)=c • A (leaf n c f) := by cases n with | zero=>omega | succ n=>rw [leaf_sea,← leaflet (h.carry (Nat.le_of_lt_succ hn)) (Nat.le_succ n)]

lemma leaf_one (x:X) (h:i≤ n) : leaf n c (Pi.single i x)=c^i • x:=by rw [leaf_eq, sum_eq_single i];simp; intro b _ H; simp [H]; intro hp; simp at hp; omega
omit [Module ℂ X] in
lemma axes (h:Cap i f): f= ∑ j∈range (i+1),Pi.single j (f j):=by
   funext v; rw [Finset.sum_apply]; by_cases he:v∈range (i+1)
   · rw [sum_eq_single v]; simp; intro b _ H; simp [H.symm]; exact fun hk=>(hk he).elim
   rw [sum_eq_zero]; exact h v (by simp at he; omega); intro j hj; simp [ne_of_mem_of_not_mem hj he|>.symm]
lemma knot_single (B:X→ₗ[ℂ] Y→ₗ[ℂ] Z) (x:X)(y:Y)(i j:ℕ): knot B (Pi.single i x) (Pi.single j y)=Pi.single (i+j) (B x y):= by
   funext l; rw [knotted]; by_cases he: i+j=l
   · subst l; rw [sum_eq_single (i,j)] <;> simp; rintro a b h H; by_cases hx:a=i; rw [hx] at h; replace h:b=j:=Nat.add_left_cancel h; exact (H hx h).elim; simp [hx]
   rw [sum_eq_zero]; simp [Ne.symm he]
   rintro ⟨u,v⟩ H; have h:u+v=l:= mem_antidiagonal.mp H; by_cases hx:u=i; have hy:v≠j:= (by omega); simp [hy]; simp [hx]
lemma leaf_knots (B:X→ₗ[ℂ] Y→ₗ[ℂ] Z)(ht:i+j≤n)(hf:Cap i f)(hg:Cap j g): leaf n c (knot B f g)=B (leaf n c f) (leaf n c g):=by
   rw [axes hf,axes hg]
   simp_rw [map_sum,LinearMap.sum_apply,map_sum]; apply sum_congr rfl; intro x hx; apply sum_congr rfl; intro y hy; rw [knot_single,leaf_one _ (by simp at hx hy; omega),leaf_one _ (by simp at hx hy; omega),leaf_one _ (by simp at hx hy; omega), map_smul,map_smul,LinearMap.smul_apply,smul_smul,pow_add,mul_comm]
end YM.MSbar.Category
