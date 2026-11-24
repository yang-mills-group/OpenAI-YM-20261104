import YM.MatchingLedger.Books.Tokens
import Mathlib.Analysis.Analytic.IteratedFDeriv
import YM.PertExtension.Uniform

/-!
# Real finite-dimensional jets of Wilson kernels

`packet`: coefficient (incl. factorial). Evaluates on any vector in the whole sup-norm pi space,
not requiring analytic continuation of the corresponding function to those points. No claiming
measurability etc of *unnormalized* logs from this calculation. At each use derivative/tail bills
have to be supplied separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Books
open Function Filter Metric MvPolynomial
open PertExtension.Series
open scoped Classical Topology ContDiff BigOperators

section tokens
variable {ι α : Type*} [Fintype ι]

omit [Fintype ι] in
lemma read_mul (x : Field ι)(p q : Poly ι) : read x (p*q)= (read x p)*(read x q):= by simp only [read_apply,eval_mul]
omit [Fintype ι] in
lemma read_add (x : Field ι)(p q : Poly ι) : read x (p+q)= (read x p)+(read x q):=by rw [map_add]
omit [Fintype ι] in
lemma read_X (x : Field ι)(i : ι) : read x (X i)=x i:= by rw [read_apply,eval_X]
omit [Fintype ι] in
lemma read_C (x : Field ι)(a : ℝ) : read x (C a)=a:= by rw [read_apply,eval_C]

lemma smooth_read (p : Poly ι) : ContDiff ℝ ω (fun x : Field ι => read x p) := by
  induction p using MvPolynomial.induction_on with
  | C => simp_rw [read_C]; fun_prop
  | add p q hp hq => simp_rw [read_add]; exact hp.add hq
  | mul_X p i hp => simp_rw [read_mul,read_X]; exact hp.mul (contDiff_apply _ _ _)

variable [DecidableEq ι]
abbrev axis (i : ι) : Field ι:= Pi.single i 1
omit [Fintype ι] in
lemma axis_part (i j:ι) : axis i j= if j=i then 1 else 0 := Pi.single_apply ..
lemma norm_axis (i:ι) : ‖axis i‖≤1:= (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j=>by rw [axis_part]; split <;> simp
lemma sum_basis (x:Field ι): ∑ i,x i • axis i=x:= by
  ext i; simp [Finset.sum_apply,axis_part,mul_ite]

omit [Fintype ι] in
lemma read_has (p : Poly ι) (x : Field ι) (i : ι) (t : ℝ) :
    HasDerivAt (fun s : ℝ => read (x+s • axis i) p) (read (x+t • axis i) (pderiv i p)) t := by
  induction p using MvPolynomial.induction_on with
  | C a=> rw [pderiv_C,map_zero]; simp_rw [read_C]; exact hasDerivAt_const ..
  | add p q hp hq=> simp_rw [map_add]; exact hp.add hq
  | mul_X p j hp=>
    have he : HasDerivAt (fun s : ℝ => read (x+s • axis i) (X j)) (read (x+t • axis i) (pderiv i (X j))) t:=by
      simp_rw [read_X]
      by_cases h:j=i
      · subst j; rw [pderiv_X_self, read_apply]; simp only [map_one,Pi.add_apply,Pi.smul_apply,axis_part,↓reduceIte,smul_eq_mul,mul_one]; exact (hasDerivAt_id' t).const_add ..
      rw [pderiv_X_of_ne h,map_zero]; simp_rw [Pi.add_apply,Pi.smul_apply,axis_part,if_neg h,smul_zero,add_zero]; exact hasDerivAt_const ..
    simp_rw [pderiv_mul,map_add,read_mul]; exact hp.mul he

def derivative (f : Field ι → ℝ)(i : ι)(x : Field ι) := fderiv ℝ f x (axis i)

lemma read_derivative (p : Poly ι)(i : ι)(x : Field ι) :
    derivative (fun x=> read x p) i x=read x (pderiv i p) := by
  let f (z : Field ι) := read z p; let p' :ℝ→Field ι:=fun t=> x+t • axis i;
  have hx : p' 0=x:= by simp [p']
  have he : HasFDerivAt f (fderiv ℝ f x) (p' 0):= hx.symm ▸ ((smooth_read p).differentiable (by simp) x).hasFDerivAt -- fix dep types
  have hu : HasDerivAt p' (axis i) 0:=by simpa [p'] using ((ContinuousLinearMap.toSpanSingleton ℝ (axis i)).hasDerivAt (x:=0)).const_add x
  exact ((he.comp_hasDerivAt 0 hu).unique (hx.symm ▸ read_has p x i 0))

omit [DecidableEq ι] in
lemma packet_symmetric {v : Field ι → ℝ} (h : ContDiffAt ℝ ω v 0) {n:ℕ} (x : Field ι)(d : Field ι) (i j : Fin n) :
    iteratedFDeriv ℝ n v 0 (Function.update (fun _=>x) i d) = iteratedFDeriv ℝ n v 0 (Function.update (fun _=>x) j d) := by
  rw [← h.iteratedFDeriv_comp_perm (Function.update (fun _ : Fin n => x) j d) (Equiv.swap i j)]
  rw [Function.update_comp_equiv]; simp
  rfl

-- deterministic basis expression aids support tracking.
def packet (v : Field ι → ℝ) (n : ℕ) : Poly ι:=
    (n.factorial:ℝ)⁻¹ • ∑ z : Fin n → ι, (iteratedFDeriv ℝ n v 0 (axis ∘ z)) • ∏ i:Fin n, X (z i)

lemma packet_read (x : Field ι) (v : Field ι → ℝ) (n : ℕ) : read x (packet v n) = Radial.jet v n x := by
  let H:=iteratedFDeriv ℝ n v 0; change read x _=(n.factorial:ℝ)⁻¹*H _
  rw [packet,map_smul,map_sum]; simp_rw [map_smul (read ..),show ∀ z:Fin n →ι, read x (∏ i,X (z i))=∏ i,x (z i) from fun z=>by rw [read_apply]; simp]; simp only [smul_eq_mul]
  rw [show (fun _:Fin n => x)=(fun _=>∑ i:ι,x i • axis i) from _root_.funext fun i=> (sum_basis x).symm,H.map_sum (α:=fun _=>ι)]
  apply congrArg ((n.factorial:ℝ)⁻¹ * ·); apply Finset.sum_congr rfl; intro z _
  rw [ContinuousMultilinearMap.map_smul_univ H (fun i=>x (z i))]; exact mul_comm ..

lemma packet_degree (v : Field ι → ℝ)(n : ℕ): (packet v n).totalDegree≤ n:=by
  refine (totalDegree_smul_le ..).trans (totalDegree_finsetSum_le (fun i _=> (totalDegree_smul_le ..).trans ((totalDegree_finsetProd ..).trans ?_)))
  simp

lemma packet_gradient {v : Field ι → ℝ} (h : ContDiffAt ℝ ω v 0) (i k) :
    pderiv i (packet v (k+1)) = packet (derivative v i) k := by
  apply MvPolynomial.funext
  intro x
  rw [← read_apply,← read_apply,← read_derivative,packet_read]; simp_rw [packet_read]; unfold derivative
  let y : Fin (k+1)→Field ι := fun _=>x
  let z : Field ι →L[ℝ] (Fin (k+1)→Field ι):=ContinuousLinearMap.pi (fun _=>ContinuousLinearMap.id ..)
  let H:=iteratedFDeriv ℝ (k+1) v 0; let M (j:Fin (k+1)):=Function.update y j (axis i)
  let B : Fin (k+1) → Field ι:= M (Fin.last k)
  let L:= (k+1).factorial; let p:= (L:ℝ)⁻¹
  let W: (Field ι→L[ℝ]ℝ) →L[ℝ]ℝ:=ContinuousLinearMap.apply ℝ ℝ (axis i)
  have hx : z x=y:=rfl
  have hi : HasFDerivAt (Radial.jet v (k+1)) (p • ((H.linearDeriv y).comp z)) x := (((H.hasFDerivAt y).comp x z.hasFDerivAt).const_mul p)
  have hp (j:Fin k) : j.castSucc ≠ Fin.last k:= Fin.castSucc_ne_last j
  have ht : (H.linearDeriv y) (z (axis i)) = (k+1:ℝ)*H B := by
    rw [ContinuousMultilinearMap.linearDeriv_apply]; change (∑ j:Fin (k+1), H (M j))= _
    rw [Finset.sum_congr rfl (f:=fun j=>H (M j)) (g:=fun _=>H B) (fun j _=>packet_symmetric h x (axis i) j (Fin.last k))]; simp
  rw [hi.fderiv]; change p*(H.linearDeriv y (z (axis i)))= Radial.jet (W ∘ fderiv ℝ v) k x
  rw [ht, Radial.jet, W.iteratedFDeriv_comp_left (h.fderiv_right (m:=ω) le_top) (by exact le_top)]
  unfold H; rw [iteratedFDeriv_succ_apply_right]; rw [show Fin.init B=(fun _=>x) from by funext j; simp [Fin.init,B,M,hp,y],show B (Fin.last k)=axis i from Function.update_self ..]
  unfold p L; simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]; field_simp; rfl

end tokens
end YM.MatchingLedger.Books
