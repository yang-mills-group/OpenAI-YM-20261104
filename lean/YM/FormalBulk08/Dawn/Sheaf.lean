import YM.FormalBulk08.Chapel.Ago
import YM.FormalBulk08.Dawn.Sol

/-!
Ordinary factorial-normalized monomial test coordinates with address
multi-index. No extra stencil relation assumed.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dawn
open Filter Function Set Lattice Chapel Tensor Analysis
open scoped BigOperators ENNReal Topology Classical ContDiff
abbrev Seasons := Axis→ℕ
variable {D j h :ℕ}
/-- `rose p` is literally $y^p/p!$ in root units. -/
def petal (s:Axis)(j:ℕ)(x:E4):ℝ:= (j.factorial:ℝ)⁻¹*x s^j
def rose (p:Seasons)(x:E4):ℝ:=∏ i,petal i (p i) x
lemma petal_smooth (i:Axis)(j):ContDiff ℝ ω (petal i j):=contDiff_const.mul (((EuclideanSpace.proj i:E4→L[ℝ]ℝ).contDiff).pow _)
lemma rose_piece_smooth (p: Seasons)(s:Finset Axis):ContDiff ℝ ω (fun x=>∏ i∈s,petal i (p i) x):=by
   induction s using Finset.induction with
   | empty=> simp only [Finset.prod_empty]; exact contDiff_const
   | @insert i s h ih=>simp_rw [Finset.prod_insert h]; exact (petal_smooth ..).mul ih
lemma rose_smooth (p : Seasons) : ContDiff ℝ ω (rose p):=rose_piece_smooth p _
lemma unfold_add (p: Seasons)(i : Axis): p+grain i=update p i (p i+1) := by ext x;by_cases h:x=i<;> simp [grain,h]
lemma petal_derivative (i : Axis)(m:ℕ)(k:Axis) : Analysis.D (basis k) (petal i (m+1))=if k=i then petal i m else 0:= by
   ext x; unfold Analysis.D; let P:=EuclideanSpace.proj (𝕜:=ℝ) i
   have hP : petal i (m+1)= ((m+1).factorial:ℝ)⁻¹ • (fun y:E4=> P y ^ (m+1)):=rfl
   rw [hP,show fderiv ℝ _ _ = _ from ((P.hasFDerivAt (x:=x)).pow (n:=m+1) |>.const_smul (c:=( ((m+1).factorial:ℝ)⁻¹ ))).fderiv]
   simp only [_root_.smul_apply,smul_eq_mul]; change _ * (_ * P (basis k))= _
   by_cases h:k=i
   · subst k; rw [if_pos rfl,show P (basis i)=1 from by change basis i i=_;simp]; unfold petal; rw [nsmul_eq_mul]
     rw [Nat.factorial_succ,Nat.cast_mul]; field_simp; rfl
   rw [if_neg h,show P (basis k)=0 from by change basis k i=_;simp [Ne.symm h]]; rw [mul_zero,mul_zero]; rfl
lemma petal_inert (i : Axis)(j)(k:Axis)(h:k≠i): Analysis.D (basis k) (petal i j)=0:= by
   cases j
   · funext x; unfold Analysis.D petal; simp
   rw [petal_derivative,if_neg h]

lemma rose_inert (i:Axis) (p:Seasons)(s:Finset Axis)(h:i∉s) : Analysis.D (basis i) (fun x => ∏ a∈s,petal a (p a) x)=0:= by
   induction s using Finset.induction with
   | empty=> funext x; simp [Analysis.D]
   | @insert a s ha ih=>
     have hx:=ih (fun hi=> h (Finset.mem_insert_of_mem hi)); have hh:=petal_inert a (p a) i (fun hi=> h (hi ▸ Finset.mem_insert_self ..));funext x; simp_rw [Finset.prod_insert ha]; unfold Analysis.D
     rw [fderiv_fun_mul (((petal_smooth ..).differentiable (by simp) x)) (((show ContDiff ℝ ω (fun x => ∏ a∈s,petal a (p a) x) from rose_piece_smooth p s).differentiable (by simp) x))]; simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
     rw [show fderiv ℝ (fun x=>petal a _ x) _ _= _ from (show fderiv ℝ (petal a (p a)) x (basis i)=0 from congr_fun hh x), show fderiv ℝ (fun x=> ∏ a∈s,petal a (p a) x) x (basis i)=0 from congr_fun hx x,mul_zero,mul_zero,zero_add]; rfl
lemma rose_piece (p: Seasons)(i: Axis) : rose p=fun x=>petal i (p i) x* ∏ a∈Finset.univ.erase i,petal a (p a) x := by funext; exact (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
lemma rose_dead (p: Seasons)(i:Axis)(h:p i=0): Analysis.D (basis i) (rose p)=0:= by rw [rose_piece p i]; simp_rw [h,petal,Nat.factorial_zero,pow_zero,Nat.cast_one,inv_one,mul_one, one_mul];exact rose_inert i p _ (Finset.notMem_erase i Finset.univ)
lemma edge_deriv (p: Seasons)(i:Axis) : Analysis.D (basis i) (rose (p+grain i))=rose p := by
    let b (x:E4):= ∏ a∈Finset.univ.erase i,petal a (p a) x
    have he : rose (p+grain i)=fun x=> petal i (p i+1) x*b x:= by
       rw [rose_piece _ i,unfold_add,update_self]; funext x; congr 1; exact Finset.prod_congr rfl fun a ha=>by rw [update_of_ne (Finset.ne_of_mem_erase ha)]
    rw [he,rose_piece p i];funext x;change fderiv ℝ _ x (basis i)=petal i (p i) x*b x
    have hx : DifferentiableAt ℝ b x:=(show ContDiff ℝ ω b from rose_piece_smooth p _).differentiable (by simp) x
    rw [fderiv_fun_mul ((petal_smooth ..).differentiable (by simp) x) hx]
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
    rw [show fderiv ℝ b x (basis i)=0 from congr_fun (rose_inert i p _ (Finset.notMem_erase i Finset.univ)) x,show fderiv ℝ (petal i (p i+1)) x (basis i)=petal i (p i) x from (congr_fun (petal_derivative i _ i) x).trans (by rw [if_pos rfl])]; simp [mul_comm]
lemma kick (p: Seasons)(i:Axis)(hp:0<p i):∃ q : Seasons,p=q+grain i:= by
    refine ⟨update p i (p i-1),?_⟩; ext a; by_cases h:a=i
    · subst a;simp [grain];omega
    simp [grain,h]
end YM.FormalBulk08.Dawn
