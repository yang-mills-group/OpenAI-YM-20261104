import YM.MSbar.Cacao.Engine
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Cacao
open PowerSeries Finset Function Polynomial
open scoped BigOperators Classical
variable {σ : Type} [Fintype σ] {k : σ→σ→ℝ} {f : PowerSeries (Pot σ)}
open MvPolynomial
local notation "P"=> Pot σ
local notation "B"=> Ball σ
local notation "G"=> PowerSeries (Pot σ)
local notation "K"=> PowerSeries B
local notation "a!"=> normalized k f
local notation "i!"=>low (normalized k f)
set_option quotPrecheck false
variable (h : Kind f)
include h
lemma began (k : σ→σ→ℝ)(n:ℕ): low (normalized k f) n 0 = PowerSeries.coeff n f:=by
    refine Eq.trans ?_ (congr_arg (PowerSeries.coeff n) (topped k h)); rw [PowerSeries.coeff_map]; exact (opens ..).symm
-- Diagonal square connected
omit h in
def cuts (k:σ→σ→ℝ) (i j:σ)(g: K)(n m:ℕ) : P := ∑ d∈ Finset.antidiagonal n,∑ e∈ Finset.antidiagonal m,
                             pderiv i (low g d.1 e.1) * pderiv j (low g d.2 e.2)
omit h in
lemma peeled (k:σ→σ→ℝ) (A:K)(n m:ℕ): low (chocolate k A) n m = ∑ i:σ,∑ j:σ,(k i j/2) • cuts k i j A n m:=by
    unfold low chocolate; rw [_root_.map_sum,Polynomial.finsetSum_coeff]; apply sum_congr rfl; intro i _
    rw [_root_.map_sum,Polynomial.finsetSum_coeff]; apply sum_congr rfl; intro j _; rw [PowerSeries.coeff_smul,Polynomial.coeff_smul,PowerSeries.coeff_mul,Polynomial.finsetSum_coeff]; unfold cuts; refine congr_arg _ (sum_congr rfl ?_); rintro ⟨p,q⟩ H; rw [Polynomial.coeff_mul]; apply sum_congr rfl; intro t ht; exact congr_arg₂ (·*·) (dusks ..) (dusks ..)
lemma turned (g:σ→σ→ℝ)(n m:ℕ): (m+1:ℝ) • low (normalized g f) n (m+1)= stove g (low (normalized g f) n m) + (∑ i:σ,∑ j:σ,(g i j/2) • cuts g i j (normalized g f) n m):=by
    let D:=normalized g f
    have he:=congr_arg (fun W:K=>low W n m) (stirred g h); change low _ _ _=low (baking _ D+chocolate g D) n m at he
    have hb: low (baking _ D) n m=stove g (low D n m):=(toast ..).trans (stokes ..).symm
    unfold low at he; rw [ride,mounts,_root_.map_add,Polynomial.coeff_add] at he; rw [← peeled g]; exact he.trans (congr_arg (·+low (chocolate g D) n m) hb)
lemma screw (k:σ→σ→ℝ) (n m:ℕ): low (normalized k f) n (m+1) =(m+1:ℝ)⁻¹ • (stove k (low (normalized k f) n m)+(∑ i,∑ j,(k i j/2) • cuts k i j (normalized k f) n m)):=by rw [← turned h]; exact (inv_smul_smul₀ (show (m+1:ℝ) ≠ 0 by positivity) _).symm -- binder order
lemma empty_th (n:ℕ) : low a! 0 n=0:=by rw [low,(airy h).1];exact Polynomial.coeff_zero n
omit h
-- degree suite (allow exponent r instead p for marked polynomials). also Tau bound

def Spicy (m n:ℕ)(F:Pot σ) (l:ℕ):Prop:= F≠0 → F.totalDegree+l*m ≤ n
variable {M p m n : ℕ}
namespace Spicy
lemma adds {F H : P}(h:Spicy m n F p)(g:Spicy m n H p): Spicy m n (F+H) p:=by
   by_cases hh:F=0; subst F; simpa using g
   by_cases hk:H=0; subst H; simpa using h
   intro hx; have hv:=totalDegree_add F H; have hu:= h hh; have hg:=g hk; omega
lemma crops {g : P}(h:Spicy m n g p)(r:ℝ): Spicy m n (r • g) p:= fun H=> le_trans (Nat.add_le_add_right (totalDegree_smul_le _ _) _) (h (fun he=>H (by rw [he,smul_zero])))
lemma spills {ι:Type}(I: Finset ι)(F:ι→P)(h:∀ i∈I, Spicy m n (F i) p):Spicy m n (∑ i∈I, F i) p:=by
    classical
    induction I using Finset.induction_on with
    | empty => rw [sum_empty]; intro he; exact (he rfl).elim
    | insert i I he ih=> rw [sum_insert he]; exact adds (h i (mem_insert_self ..)) (ih (fun j hh=>h j (Finset.mem_insert_of_mem hh)))
lemma grads {F:P}(h: Spicy m n F 2)(i:σ)(hh:pderiv i F ≠ 0): (pderiv i F).totalDegree +1+2*m ≤ n := by
    have hx:F≠0 := fun hp=>hh (by rw [hp,_root_.map_zero]); have hp:= h hx
    by_cases hc:F.totalDegree=0
    · rw [totalDegree_eq_zero_iff_eq_C] at hc; exact (hh (by rw [hc];simp)).elim
    have hv:=pdeg i (p:=F) (show F.totalDegree≤ F.totalDegree-1+1 by omega); omega
lemma shrink {F:P}(h: Spicy m n F 2)(k:σ→σ→ℝ): Spicy (m+1) n (stove k F) 2:=by
    intro he; have ht:F≠0:=fun hg=>he (by rw [hg,_root_.map_zero]); have hp:=h ht
    by_cases hx:F.totalDegree≤1
    · exact (he (dry k hx)).elim
    have hc:=depth k (p:=F) (show F.totalDegree ≤ F.totalDegree-2+2 by omega); omega
end Spicy
include h
-- extends nonlinear term, degree bounded by λ n+2.Relations.Low.With mark choose label weight big.Def shelf
structure Expanse (f:PowerSeries (Pot σ))(m p:ℕ): Prop where
    profile (n:ℕ):n≤p → (PowerSeries.coeff n f).totalDegree ≤ m*n+2
variable (W:Expanse f M p)
local notation "ρ"=> low a!
include W
lemma ripens (N:ℕ) : ∀ n j, j ≤ N → n ≤ p → Spicy j ((M+2)*n) (i! n j) 2 := by
   induction N with
   | zero=> intro n j hj hn; rw [Nat.eq_zero_of_le_zero hj,began h]; by_cases hx:n=0
            · subst n; intro he; exact (he h).elim
            intro he; have he:=W.profile n hn; rw [Nat.add_mul]; omega
   | succ s ih=>
       intro n j hj hp; by_cases he: j ≤ s; exact ih n j he hp
       rw [show j=s+1 by omega, screw h]; apply Spicy.crops; apply Spicy.adds (Spicy.shrink (ih n s le_rfl hp) k); apply Spicy.spills
       intro i hi; apply Spicy.spills; intro v _; apply Spicy.crops; unfold cuts; apply Spicy.spills; rintro ⟨u,w⟩ ht
       apply Spicy.spills; rintro ⟨a,b⟩ he; have hy:u+w=n:=mem_antidiagonal.mp ht; have hx:a+b=s:=mem_antidiagonal.mp he; dsimp only
       intro he; have hu:=Spicy.grads (ih u a (by omega) (by omega)) i (left_ne_zero_of_mul he); have hv:=Spicy.grads (ih w b (by omega) (by omega)) v (right_ne_zero_of_mul he); apply le_trans (Nat.add_le_add_right (totalDegree_mul ..) _) _; rw [← hy,Nat.mul_add (M+2)]; omega
lemma cropped (N:ℕ) : ∀ n j, j ≤ N → n ≤ p → (i! n j).totalDegree ≤ M*n+2:=by
    induction N with
    | zero=> intro n j hj hp; rw [Nat.eq_zero_of_le_zero hj,began h]; exact W.profile n hp
    | succ s ih=>
        intro n j hj hp; by_cases he:j≤ s; exact ih n j he hp
        rw [show j=s+1 by omega,screw h]; refine (totalDegree_smul_le _ _).trans ((totalDegree_add ..).trans (max_le ?_ ?_))
        · apply depth k (n:= M*n+2); have he:=ih n s le_rfl hp; exact le_trans he (by omega)
        apply totalDegree_finsetSum_le; intro i _; apply totalDegree_finsetSum_le; intro v _; refine (totalDegree_smul_le _ _).trans ?_; unfold cuts
        apply totalDegree_finsetSum_le; rintro ⟨u,w⟩ ht; apply totalDegree_finsetSum_le; rintro ⟨a,b⟩ hA; have hh:u+w=n:=mem_antidiagonal.mp ht; have hx:a+b=s:=mem_antidiagonal.mp hA
        dsimp only; apply (totalDegree_mul ..).trans ((Nat.add_le_add (pdeg i (ih u a (by omega) (by omega))) (pdeg v (ih w b (by omega) (by omega)))).trans ?_); rw [← hh,Nat.mul_add]; omega
end YM.MSbar.Cacao
