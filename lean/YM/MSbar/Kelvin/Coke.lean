import YM.MSbar.Kelvin.Coin
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Kelvin
open Function Filter MeasureTheory Cacao PowerSeries Finset Whisk
open scoped Topology BigOperators Classical
open Lattice Matrix Push.Uniform
variable {ι σ τ: Type}[Fintype σ][Fintype ι][Fintype τ][DecidableEq σ] [DecidableEq ι]
    {n:Side} {l : σ→ Site n}{k s A C : Matrix σ σ ℝ} {B' : Matrix ι ι ℝ}
    (u:ι→σ) (g:Injective u)
local notation "ι!"=> imbed u
local notation "p!"=> pinch u k
local notation "e!"=> extendM u
local notation "w!"=> vanish u k
local notation "dp"=> (pinch u k)⁻¹
variable {a b c t B W D r:ℝ} {p x: ℕ} {v:Site n}
private lemma left (ha:0≤a) (i:σ){w:ℝ}{z :ℝ} (hz: 0 ≤ z)(he:∑ j,|A i j| *liftW a p (separation (l i) (l j)) ≤ w) (hK:LoopNet l a p C z) : ∑ j,|(A*C) i j| * liftW a p (separation (l i) (l j)) ≤ w*z :=by
     let t(i j:σ):=liftW a p (separation (l i) (l j)); let f(k j:σ):= |A i k| *t i k*(|C k j| *t k j)
     have hu(i j k:σ): t i j ≤ t i k*t k j:=(w_more (separation_triangle _ (l k) _) ha p).trans (w_triangle ..)
     have hp(i j:σ):0≤ t i j:= (wpos ..).le
     have hx(j:σ):|(A*C) i j| * t i j ≤∑ k,f k j:=by
        rw [Matrix.mul_apply]; apply (mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs ..) (hp ..)).trans; rw [sum_mul]; apply sum_le_sum; intro k _; unfold f; rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hu i j k) (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq (by ring)
     apply (sum_le_sum fun j _=> hx j).trans; rw [sum_comm]; unfold f; simp_rw [← Finset.mul_sum]; refine le_trans (sum_le_sum (fun x _=> mul_le_mul_of_nonneg_left (hK.glow x) (mul_nonneg (abs_nonneg _) (hp i x)))) ?_
     rw [← sum_mul]; exact mul_le_mul_of_nonneg_right he hz
lemma soars (ha:0 ≤ a)(he: LoopNet l a p A b)(h:LoopNet l a p C c) : LoopNet l a p (A*C) (b*c) := by
   refine ⟨mul_nonneg he.hope h.hope,fun i=> left ha _ h.hope (he.glow i) h, fun j=>?_⟩; -- edit
   have hh: LoopNet l a p A.transpose b:= he.loom; have hz: LoopNet l a p C.transpose c:=h.loom; have hp := left ha j he.hope (hz.glow j) hh; rw [mul_comm b c]; apply le_trans (le_of_eq _) hp; apply sum_congr rfl; intro i _; rw [← transpose_mul,Matrix.transpose_apply,separation_comm]
lemma turnkey : LoopNet l a p (1:Matrix σ σ ℝ) 1:=by
   refine ⟨zero_le_one,fun i=> ?_,fun i=>?_⟩
   all_goals simp [Matrix.one_apply,ite_mul, abs_ite,liftW]
lemma negSub (ha:LoopNet l a p k b)(hb:LoopNet l a p s t): LoopNet l a p (k-s) (b+t):=by
   have hi(i j): |(k-s) i j| *liftW a p (separation (l i) (l j)) ≤ |k i j| *liftW a p (separation (l i) (l j))+|s i j| *liftW a p (separation (l i) (l j)) := by simp only [←add_mul, Matrix.sub_apply]; exact mul_le_mul_of_nonneg_right (abs_sub ..) (wpos ..|>.le)
   refine ⟨add_nonneg ha.hope hb.hope,fun i=>?_ ,fun i=>?_⟩
   · refine (sum_le_sum (fun j _=> hi i j)).trans ?_; rw [sum_add_distrib]; exact add_le_add (ha.glow i) (hb.glow i)
   refine (sum_le_sum fun j _=> hi j i).trans ?_; rw [sum_add_distrib]; exact add_le_add (ha.forward i) (hb.forward i)
variable (h:k.PosDef)
include h g
lemma factor_Q (ha: 0≤ a)(hs:LoopNet l a p k b) (hB : LoopNet l a p (extendM u (pinch u k)⁻¹) c) : LoopNet l a p (vanish u k) (1+c*b):= negSub turnkey (soars ha hB hs)
omit h g in
lemma rty {i:σ} (he : 0 ≤ a)(hx:x≤separation (l i) v) (j:σ) : Real.exp (a*x) ≤ Eve a v (l j) * Eve a (l j) (l i) := (Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast ((separation_comm v _).symm ▸ hx)) he)).trans (eve_t he ..) -- i implicit
variable (S₀:∀ i:σ,i∉ Set.range u → x≤ separation (l i) v)
include S₀
lemma vanSmall (ha:0≤ B)(hc:LoopNet l (a+B) p (vanish u k) t) (i:σ) : ∑ j, |vanish u k i j| *liftW a p (separation (l i) (l j)) ≤ Eve B v (l i)* (Real.exp (-B*x)*t):=by
   let T:= v; let z:= Real.exp (B*x); let C (j):=vanish u k i j; let S(a:ℝ)(j):=liftW a p (separation (l i) (l j)); let d:= Eve B v (l i)
   have hz:0 < z:=Real.exp_pos _
   have hp(j): z* (|C j| *S a j) ≤ d*(|C j| *S (a+B) j) :=by
       by_cases hx:j∈Set.range u
       · obtain ⟨q,rfl⟩:=hx; unfold C; rw [root_out u g h]; simp
       have hi:=rty (l:=l) ha (S₀ _ hx) i; rw [mul_left_comm (d)]; unfold S; rw [← trade]; refine (mul_le_mul_of_nonneg_right hi (mul_nonneg (abs_nonneg _) (wpos ..|>.le))).trans_eq ?_; ring
   apply le_of_mul_le_mul_left (a:=z) _ hz; change z*∑ j,|C j| *S a j ≤ z*_
   rw [Finset.mul_sum]; refine (sum_le_sum (fun j _=>hp j)).trans ?_; rw [← mul_sum]; refine (mul_le_mul_of_nonneg_left (hc.glow i) (show 0 ≤ d from (Real.exp_pos _).le)).trans_eq ?_; unfold d z; rw [show -B*x=-(B*x) by ring, Real.exp_neg]; field_simp
lemma realFuel (ha:0≤ a)(hr:0≤ B)(hc:LoopNet l (a+B) p (vanish u k) t)(hp:LoopNet l a p (show Matrix σ σ ℝ from k⁻¹) c) : Dorian l v a B p (show Matrix σ σ ℝ from (k⁻¹-extendM u (pinch u k)⁻¹)) (Real.exp (-B*x)*(t*c)) :=by
    let S:=pinch u k; let d:=extendM u S⁻¹; have hd:=van_license u g h; have hz:(k⁻¹-d).transpose=k⁻¹-d:=by rw [transpose_sub,show (k⁻¹).transpose=k⁻¹ from by simpa [IsHermitian] using h.inv.1]; unfold d extendM; have ht:S.PosDef:=h.submatrix g;rw [transpose_mul,transpose_mul,transpose_transpose,show (S⁻¹).transpose=S⁻¹ from by simpa [IsHermitian] using ht.inv.1,Matrix.mul_assoc]
    let V:= Real.exp (-B*x)*(t*c); have he(j:σ) : ∑ i, |(k⁻¹-d) j i| *liftW a p (separation (l j) (l i)) ≤ Eve B v (l j)*V := by
         change ∑ i, |(k⁻¹-extendM u (pinch u k)⁻¹) j i| * liftW a p (separation (l j) (l i)) ≤ _; rw [← hd]; refine (left ha _ hp.hope (vanSmall u g h S₀ hr hc j) hp).trans_eq ?_; unfold V; ring
    refine ⟨mul_nonneg (Real.exp_pos _).le (mul_nonneg hc.hope hp.hope),he,fun j=>?_⟩; apply le_trans (le_of_eq _) (he j); exact sum_congr rfl fun i _=> congr_arg₂ (·*·) (congr_arg abs (show (k⁻¹-d) i j= (k⁻¹-d) j i from congr_arg (fun A: Matrix σ σ ℝ=> A j i) hz)) (congr_arg _ (separation_comm ..))
end YM.MSbar.Kelvin
