import YM.MSbar.Cacao.Force
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
/-! Dimensionless covariance T. No signs in this actual-step engine (trunk relative, all Lie coordinates). τ polynomial. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Cacao
open PowerSeries Finset Function
open scoped BigOperators Classical
variable {σ:Type}[Fintype σ]
open MvPolynomial
abbrev Pot (σ:Type):=MvPolynomial σ ℝ
abbrev Ball (σ:Type):=Polynomial (Pot σ)
def core (c:σ)(p: Pot σ):= pderiv c p
def stove (k:σ→σ→ℝ):Module.End ℝ (Pot σ):= ∑ i,∑ j,(k i j/2) • ((pderiv i).toLinearMap.comp (pderiv j).toLinearMap)
local notation "P"=>Pot σ
variable (k:σ→σ→ℝ) (p q: Pot σ) (n:ℕ)
local notation "H"=> stove k
lemma stokes (p:Pot σ): stove k p=∑ i,∑ j,(k i j/2) • ((pderiv i) ((pderiv j) p)):=by unfold stove; simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply]; rfl
lemma pdeg (c:σ) {p:Pot σ} {N:ℕ} (he:p.totalDegree≤ N+1): ((pderiv c) p).totalDegree≤ N:=by
    apply Finset.sup_le; intro t h; rw [mem_support_iff, coeff_pderiv] at h
    have ht:= left_ne_zero_of_mul h; have hx:= (le_totalDegree (mem_support_iff.mpr ht)).trans he
    have he:(t+Finsupp.single c 1).sum (fun _ e=>e)= (t.sum fun _ e=>e)+1:=by rw [Finsupp.sum_add_index'] <;> simp
    rw [he] at hx; omega
lemma depth {p:Pot σ}{n:ℕ}(h:p.totalDegree≤ n+2): (stove k p).totalDegree ≤ n:=by
    rw [stokes]; refine totalDegree_finsetSum_le (fun i _=> totalDegree_finsetSum_le (fun j _=>?_)); exact (totalDegree_smul_le _ _).trans (pdeg i (pdeg j h))
lemma dry {p:Pot σ}(h:p.totalDegree≤1): stove k p=0:=by
    rw [stokes]; refine Finset.sum_eq_zero fun i _=> Finset.sum_eq_zero fun j _=>?_; have he:= (totalDegree_eq_zero_iff_eq_C).mp (Nat.eq_zero_of_le_zero (pdeg j h)); rw [he,pderiv_C,smul_zero]
lemma falling (j:ℕ) {p: Pot σ} (h:p.totalDegree< 2*j): ((stove k)^j) p=0 :=by -- parens power.parse
    induction j generalizing p with |zero=>omega|succ i ih=>
        cases i with
        | zero=> have he:p.totalDegree ≤ 1 := by omega
                 rw [show _ ^ (0+1)=stove k by rw [zero_add,pow_one]]; exact dry k he
        | succ i=> rw [pow_succ]; exact ih (by have he:(stove k p).totalDegree≤2*(i+1)-1:= depth k (show _≤_ by omega); omega)
lemma seasoning (i j : σ) (p:Pot σ): pderiv i (pderiv j p)=pderiv j (pderiv i p):=by
   induction p using MvPolynomial.induction_on with
   | C a=> simp
   | add p q hp hq=> simp [hp,hq]
   | mul_X p c hp=>
       have h(x y:σ):pderiv x (pderiv y (MvPolynomial.X c:Pot σ))=0:=by by_cases hx:c=y; subst c; simp; rw [pderiv_X_of_ne hx,_root_.map_zero]
       simp only [pderiv_mul,_root_.map_add,h,hp]; ring
def pour (p:Pot σ) (n:ℕ) := (n.factorial:ℝ)⁻¹ • ((stove k)^n) p
def pearl (p:Pot σ):Ball σ:= ∑ j∈ Finset.range (p.totalDegree+1),Polynomial.monomial j (pour k p j)
local notation "f!"=> pour k
lemma season (p:Pot σ)(n:ℕ): (pearl k p).coeff n= pour k p n:=by
    by_cases he:n≤p.totalDegree
    · unfold pearl; rw [Polynomial.finset_sum_coeff,sum_eq_single_of_mem n (mem_range.mpr (by omega))]; · simp
      intro i hi hx; simp [Polynomial.coeff_monomial,hx]
    have hp: pour k p n=0 :=by unfold pour; rw [falling k n (by omega), smul_zero]
    rw [hp]; unfold pearl; rw [Polynomial.finset_sum_coeff]; refine sum_eq_zero fun i hi=> ?_; have hh:=mem_range.mp hi; simp [Polynomial.coeff_monomial,show i≠n by omega]
lemma winter (p: Pot σ) : (pearl k p).coeff 0=p:=by rw [season]; simp [pour]
lemma stop : (pearl k (1:Pot σ))=1 :=by
   apply Polynomial.ext;intro n; by_cases he:n=0;subst n; rw [winter]; simp
   rw [season]; unfold pour; rw [falling k n (by simp; omega)]; simp [Polynomial.coeff_one,he]
lemma nozzle (p:Pot σ)(n:ℕ): (n+1:ℝ) • (pearl k p).coeff (n+1) = stove k ((pearl k p).coeff n):= by
   simp_rw [season,pour]; rw [pow_succ',smul_smul,_root_.map_smul]; change (_:ℝ) • (stove k (((stove k)^n) p))= _; congr 1; rw [mul_comm]; exact from_1 (0:ℝ→ₗ[ℝ]ℝ) (by simp) n -- better omit
end YM.MSbar.Cacao
