import YM.XSpace.Reservoir

/-!
# Locally finite Gaussian Laplacian.

Any symmetric covariances, even not positive, even an infinite flavor
store. Declare sufficiently many coordinates at the start. Needed in
composition e.g. when passing from raw contractions to Laplacians
built from separated directional probes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Lap
open Function Set Filter MvPolynomial Next.Rank.Normal Legs
open scoped Topology BigOperators Classical
variable {ι : Type*} (S : Finset ι) (K : Symmetric ι) {p : poly ι}
def op : Module.End ℂ (poly ι) := ∑ i∈S, (slit (K.cov i)).toLinearMap ∘ₗ (slit (choose_var i 1)).toLinearMap
lemma op_at (p : poly ι): op S K p=∑ i∈S, slit (K.cov i) (slit (choose_var i 1) p):=LinearMap.sum_apply ..
def scope (S : Finset ι): Subalgebra ℂ (poly ι):= supported ℂ (S:Set ι)
lemma in_op (h : p∈scope S): op S K p∈scope S:= by rw [op_at]; exact Subalgebra.sum_mem _ fun _ _=> split_in _ _ (split_in _ _ h)
lemma ever_op (h : p∈scope S) (n : ℕ): (op S K ^n) p∈scope S:=by
  induction n with
  | zero => exact h
  | succ n ih => rw [pow_succ']; exact in_op _ _ ih
lemma op_data (p : poly ι) (f : ι→ℂ): slit f (op S K p)=op S K (slit f p):=by
  rw [op_at,op_at,map_sum]; refine Finset.sum_congr rfl fun i _=>?_; rw [slit_slit (K.cov i) f, slit_slit (choose_var i 1) f]
lemma op_comm {j : ι} (hj : j∈ S) (h : p∈ scope S): op S K (X j*p)= X j*op S K p+(2:ℂ) • slit (K.cov j) p:=by
  rw [op_at,op_at, two_smul, Finset.mul_sum, split_sum (K.cov j) S h] -- rewrites both copies? `rw` all matches
  simp only [slit_prod,map_add, C_mul', show ∀ (x : ι) (a : ℂ), slit (K.cov x) (a • p)=a • slit (K.cov x) p from fun i a=> (slit _).map_smul a _, Finset.sum_add_distrib]
  have hu : (∑ i∈S, (choose_var i 1 j) • slit (K.cov i) p)= slit (K.cov j) p:=by
    rw [Finset.sum_eq_single_of_mem j hj, chosen_eq,one_smul]; intro i _ hi; rw [chosen_ne (Ne.symm hi),zero_smul]
  rw [hu,split_sum (K.cov j) S h]; simp_rw [show ∀ i,K.cov i j=K.cov j i from fun i=> K.symm ..]; abel
lemma op_j_pow {j : ι} (hj : j∈S) (h : p∈scope S) (n:ℕ):
    (op S K ^(n+1)) (X j*p)= X j*((op S K ^(n+1)) p)+(2*(n+1:ℕ):ℂ) • slit (K.cov j) ((op S K ^n) p):=by
  induction n with
  | zero => simpa using op_comm _ _ hj h
  | succ n ih =>
    let T:= op S K; let Q:= slit (K.cov j); let P (n:ℕ):=(T^n) p; let a (n:ℕ):=(2*(n:ℂ))
    rw [pow_succ' _ (n+1)]; change T ((T^(n+1)) _)= X j*T (P (n+1)) + a (n+1+1) • Q (P (n+1));
    rw [show (T^(n+1)) (X j*p)=X j*P (n+1) + a (n+1) • Q (P n) from ih,map_add,map_smul,
        show T (X j* P (n+1))=_ from op_comm _ _ hj (ever_op _ _ h (n+1)),show T (Q (P n))= Q (T (P n)) from (op_data ..).symm]
    have hh : P (n+1)=T (P n):= by unfold P; rw [pow_succ']; rfl
    simp_rw [← hh]; rw [add_assoc]; apply congr_arg; rw [← add_smul]; congr 1; unfold a; push_cast; ring

def wgt (n : ℕ):ℂ := ((2:ℂ)^n * n.factorial)⁻¹
def heat (m : ℕ) : Module.End ℂ (poly ι):= ∑ i∈Finset.range m,wgt i • (op S K)^i
lemma heat_value (m:ℕ) (p:poly ι): heat S K m p=∑ i∈Finset.range m,wgt i • ((op S K)^i) p:= by simp [heat,LinearMap.sum_apply]
lemma wgt_next (i : ℕ): wgt (i+1)*(2*(i+1:ℕ))=wgt i:= by unfold wgt; rw [pow_succ,Nat.factorial_succ]; push_cast; field_simp
lemma heat_more {j : ι} (hj : j∈S) (h : p∈scope S) (n : ℕ):
    heat S K (n+1) (X j*p)= X j*heat S K (n+1) p + slit (K.cov j) (heat S K n p):=by
  rw [heat_value,heat_value,Finset.sum_range_succ',Finset.sum_range_succ',mul_add]; simp only [op_j_pow _ _ hj h,smul_add,smul_smul,wgt_next,heat_value,Finset.sum_add_distrib,map_sum]
  rw [Finset.mul_sum]; simp only [(slit (K.cov j)).map_smul,mul_smul_comm,pow_zero,Module.End.one_apply]; abel
private lemma op_const (a : ℂ) (n : ℕ) : ((op S K)^(n+1)) (C a) = 0 := by rw [pow_succ]; simp [Module.End.mul_apply, op_at]
lemma thaws (h : p∈scope S): ∀ᶠ n in atTop,∀ Q : Symmetric ι, heat S Q n p=milk Q p:=by
  unfold scope at h; rw [supported_eq_range_rename,AlgHom.mem_range] at h; obtain ⟨q,rfl⟩:=h
  induction q using MvPolynomial.induction_on with
  | C a=>
    filter_upwards [eventually_gt_atTop 0] with n hn Q
    obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simp_rw [rename_C, heat_value, fine, Finset.sum_range_succ',op_const]; simp [wgt]
  | add p q h1 h2=> filter_upwards [h1,h2] with n hn hm K; rw [_root_.map_add, _root_.map_add, _root_.map_add,hn,hm]
  | mul_X q i h=>
    obtain ⟨k,h⟩:=eventually_atTop.mp h; filter_upwards [eventually_gt_atTop k] with l hl Q
    obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show l≠0 by omega)
    rw [mul_comm q,_root_.map_mul, rename_X,heat_more _ _ i.property ?_,h (n+1) hl.le,h n (by omega),feeds]; unfold scope; rw [supported_eq_range_rename]; exact AlgHom.mem_range_self ..
lemma stable (V : Submodule ℂ (poly ι)) (h : ∀ p∈V,op S K p∈V) (hP : p∈scope S) (hp : p∈V) : milk K p∈V:=by
  have he (k:ℕ): ((op S K)^k) p ∈ V:=by
    induction k with
    | zero=>exact hp
    | succ n ih=>rw [pow_succ']; exact h _ ih
  obtain ⟨n,hn⟩:=(thaws _ hP).exists; rw [← hn K,heat_value]; exact V.sum_mem fun k _=> V.smul_mem _ (he k)
end YM.XSpace.Lap
