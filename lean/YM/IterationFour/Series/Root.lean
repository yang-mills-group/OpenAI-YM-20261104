import YM.IterationFour.Series.Tail

/-!
# The inverse-root in the ratio of successive couplings

Produce and cost it. D polynomial has constant 1. `root D n` has constant
1, degree ≤ n, square times D has all required Taylor coefficients (constant
1 and vanish to n in positive degree). Bills are polynomial in the mass of D
at every fixed finite n. No branch from a `Final`/trajectory used here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Series
open Function Set Polynomial Filter
open scoped Topology BigOperators

variable (D : Polynomial ℝ)
def equation (p : Polynomial ℝ) := p^2*D-1

def headError (p : Polynomial ℝ) (j : ℕ) := (- (equation D p).coeff (j+1))/2

def root : ℕ→Polynomial ℝ
  | 0 => 1
  | j+1 => let p:=root j; p + C (headError D p j)*X^(j+1)

lemma const_one (n : ℕ) : (root D n).coeff 0=1 := by
  induction n with
  | zero => exact coeff_one_zero
  | succ n ih => unfold root; dsimp only; simp [coeff_add, ih, C_mul_X_pow_eq_monomial]
lemma root_short (n : ℕ) : short (root D n) (n+1) := by
  induction n with
  | zero =>
    intro j hj; unfold root; rw [coeff_one, if_neg]; omega
  | succ n ih =>
    intro j hj; unfold root; dsimp only
    have hx: j≥n+1 := by omega
    rw [coeff_add, ih j hx, coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero, zero_add]
lemma split_sq (h : D.coeff 0=1) (n : ℕ) : cut (equation D (root D n)) (n+1) := by
  induction n with
  | zero => intro j hj; obtain rfl := (show j=0 by omega); simp [root,equation,h]
  | succ n ih =>
    let k:=n+1; let P:= root D n; let W:=root D (n+1)
    let E:= C (headError D P n)*(P+W)*D
    have hx : equation D W=equation D P+X^k*E := by
      have he : W=P+C (headError D P n)*X^k := rfl
      unfold equation E; rw [he]; ring
    intro j hj; change (equation D W).coeff j=0
    rw [hx,coeff_add]
    have hk:j≤ n+1 := by omega
    by_cases he:j=k
    · subst j
      have hk := coeff_X_pow_mul E k 0; rw [zero_add] at hk
      rw [hk, coeff_zero_eq_eval_zero E]
      dsimp only [E]; simp only [eval_mul, eval_C, eval_add, ← coeff_zero_eq_eval_zero]
      rw [h,show P.coeff 0=1 from const_one ..,show W.coeff 0=1 from const_one ..]
      unfold k headError; ring
    have ht:j<k:= by dsimp only [k] at *; omega
    rw [ih j ht,cuts _ (dvd_mul_right _ E) j ht,zero_add]

variable {D}
lemma chop {p q : Polynomial ℝ} {n : ℕ} (hp : cut p n) (hq : cut q n) : cut (p-q) n :=
    cuts _ (dvd_sub (cutoff p hp) (cutoff q hq))
/-- Forget the positive-constant term (a unit mod X). -/
lemma constant_unit {p q : Polynomial ℝ} {n : ℕ} (hq : q.coeff 0≠0) (hp : cut (q*p) n) : cut p n := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    have h:= ih (fun j hj=>hp j (by omega))
    intro j hj; have h':j≤n:= by omega
    by_cases hx:j=n
    · subst j
      obtain ⟨W,hW⟩:= cutoff _ h
      have ht := hp n hj; rw [hW,mul_left_comm] at ht
      have hi(T : Polynomial ℝ): (X^n*T).coeff n=T.coeff 0 := by
        simpa only [zero_add] using coeff_X_pow_mul T n 0
      rw [hi,coeff_zero_eq_eval_zero,eval_mul,← coeff_zero_eq_eval_zero,← coeff_zero_eq_eval_zero] at ht
      rw [hW,hi,mul_eq_zero.mp ht|>.resolve_left hq]
    exact h _ (lt_of_le_of_ne h' hx)

lemma through {n : ℕ} {p q : Polynomial ℝ} (h : D.coeff 0=1) (hp : p.coeff 0=1) (hq : q.coeff 0=1)
    (he : cut (equation D p) (n+1)) (hg : cut (equation D q) (n+1)) : cut (p-q) (n+1) := by
  have h₁:(D*(p+q)).coeff 0 = 2 := by
    rw [coeff_zero_eq_eval_zero,eval_mul,eval_add]; simp [← coeff_zero_eq_eval_zero,h,hp,hq]; norm_num
  refine constant_unit (p:=p-q) (by rw [h₁]; exact two_ne_zero) ?_
  rw [show D*(p+q)*(p-q)= equation D p-equation D q by unfold equation; ring]
  exact chop he hg
lemma onlyRoot {n : ℕ} {p : Polynomial ℝ} (h : D.coeff 0=1) (hp : p.coeff 0=1)
    (hk : short p (n+1)) (hx : cut (equation D p) (n+1)) : p=root D n := by
  refine sub_eq_zero.mp <| Polynomial.ext fun i=>?_
  by_cases he:i<n+1
  · rw [through h hp (const_one D n) hx (split_sq D h n) i he, coeff_zero]
  rw [coeff_sub,hk i (by omega),root_short D n i (by omega),coeff_zero,sub_zero]

@[simp] lemma mass_id : mass (1:Polynomial ℝ)=1 := (prices_monomial (1:ℝ) 0).trans norm_one
lemma equation_cash (p : Polynomial ℝ) : mass (equation D p) ≤ mass p^2*mass D+1 := by
  apply le_trans (mass_sub ..)
  rw [mass_id]; exact add_le_add_left ((mass_mul ..).trans (mul_le_mul_of_nonneg_right (mass_pow ..) (mass_nn _))) 1

/-- Post-coefficient alignment cost. -/
def levy (x : ℝ) : ℕ→ℝ
  | 0 => 1
  | n+1 => levy x n + (levy x n ^2*x+1)/2
lemma mass_cost {x : ℝ} (h : mass D ≤ x) (n : ℕ) : mass (root D n) ≤ levy x n := by
  induction n with
  | zero => exact mass_id.le
  | succ n ih=>
    unfold root; dsimp only
    apply (mass_add ..).trans
    rw [C_mul_X_pow_eq_monomial, prices_monomial, levy]; dsimp only [headError]
    refine add_le_add ih ?_
    rw [norm_div,norm_neg,Real.norm_ofNat]
    refine div_le_div_of_nonneg_right ?_ (by norm_num : (0:ℝ)≤2)
    exact ((mass_coeff ..).trans ((equation_cash ..).trans (add_le_add_left (mul_le_mul
      (pow_le_pow_left₀ (mass_nn _) ih _) h (mass_nn _) (sq_nonneg _)) 1)))

lemma sign {n : ℕ} {u : ℝ} (hu : 0 ≤ u) (h : u≤1) (hx : (mass (root D n)+1)*u ≤ 1/2) : 1/2 ≤ (root D n).eval u := by
  have he : cut (root D n-1) 1:= by intro j hj; rw [show j=0 by omega,coeff_sub,const_one,coeff_one_zero,sub_self]
  have hq := norm_read _ he (x:=u) (by rwa [Real.norm_of_nonneg hu]); rw [Real.norm_eq_abs,pow_one,Real.norm_of_nonneg hu,eval_sub,eval_one] at hq
  have hl : mass (root D n-1) * u ≤ (mass (root D n)+1)*u :=
    mul_le_mul_of_nonneg_right ((mass_sub ..).trans_eq (by rw [mass_id])) hu
  linarith only [(abs_le.mp (hq.trans (hl.trans hx))).1]

/-- Test root at true `u`, retaining exactly the desired truncation error.
    Denominator lower Λ here on **D.eval u** (not beta itself). -/
lemma invoice {n : ℕ} {u Λ : ℝ} (hu : 0≤u) (hx : u≤1) (h : D.coeff 0=1)
    (hk : (mass (root D n)+1)*u ≤ 1/2) (hΛ : 0 < Λ) (hD : Λ ≤ D.eval u) :
    |(root D n).eval u - (Real.sqrt (D.eval u))⁻¹| ≤
       2 / Λ * mass (equation D (root D n)) * u^(n+1) := by
  let d:=D.eval u; let v:=(root D n).eval u; let k:=(Real.sqrt d)⁻¹
  have hd : 0<d := hΛ.trans_le hD; have hz:0<k:=inv_pos.mpr (Real.sqrt_pos.2 hd)
  have hh : 1/2 ≤ v := sign hu hx hk
  have hp := norm_read _ (split_sq D h n) (x:=u) (by rwa [Real.norm_of_nonneg hu]); rw [Real.norm_eq_abs,Real.norm_of_nonneg hu] at hp
  have hK : k^2*d=1 := by dsimp only [k]; rw [inv_pow,Real.sq_sqrt hd.le,inv_mul_cancel₀ hd.ne']
  let A:= mass (equation D (root D n))
  have H : |v-k| * ((v+k)*d) ≤ A*u^(n+1) := by
    simp only [equation,eval_sub,eval_pow,eval_mul,eval_one] at hp
    rw [← abs_of_pos (show 0< (v+k)*d by positivity), ← abs_mul,
      show (v-k)*((v+k)*d)=v^2*d-1 by nlinarith only [hK]]
    exact hp
  have hZ : Λ/2 ≤ (v+k)*d := by
    have hf := mul_le_mul (show 1/2 ≤ v+k by linarith only [hh,hz]) hD hΛ.le (show 0 ≤ v+k by linarith only [hh,hz])
    linarith only [hf]
  have hf := (le_div_iff₀ (half_pos hΛ)).mpr ((mul_le_mul_of_nonneg_left hZ (abs_nonneg (v-k))).trans H)
  exact le_trans hf (Eq.le (by unfold A; ring))
end YM.IterationFour.Series
