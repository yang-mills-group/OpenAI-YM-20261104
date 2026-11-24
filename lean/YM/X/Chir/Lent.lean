import YM.X.Chir.Ethereal
/-!
# Head cost and matrix estimates for portrait large-R; discrete for contacts and convolution.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir.Imprint
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e c:ℝ}
local notation "D"=>Interval.mass
local notation "S"=> Site n
variable (x y z w:Site n)
lemma pay_pos : 0 < D x y:= zero_lt_one.trans_le (mass_pos ..)
lemma comm : D x y=D y x := by unfold Interval.mass ticketN; rw [separation_comm]
lemma tip : D x z+1≤ D x y+D y z:= by unfold Interval.mass ticketN; exact_mod_cast (show separation x z+1+1≤ separation x y+1+(separation y z+1) from by have:= separation_triangle x y z; omega)
lemma along (u v: Site n): D u x≤D u v+ separation x v:=by
    have h:= tip u v x; rw [comm v x] at h; unfold Interval.mass ticketN at *; push_cast at *; linarith
lemma steps (i:Axis) : separation x (x+step i) ≤ 1:= by rw [separation,show x-(x+step i)= -step i by abel,pdist_neg]; simpa [separation] using pdist_step (n:=n) i -- name wrong
lemma stride (i:Axis): D x y≤ D x (y+step i)+1 ∧ D x (y+step i) ≤ D x y+1 := by
    constructor
    · apply le_trans (along y x _); gcongr; exact_mod_cast steps y i
    apply le_trans (along _ x _); rw [separation_comm (y+step i) y]; gcongr; exact_mod_cast steps y i
lemma selfD : D x x=1:= by simp [Interval.mass,ticketN]
def fund (d:ℕ)(x y:S):ℝ := (D x y)⁻¹^d
local notation "p"=> fund
lemma live : 0<p k x y:= by unfold fund; have he:=pay_pos x y; positivity
lemma funds : p k x y=p k y x:= congr_arg (fun t:ℝ=> t⁻¹^k) (comm ..)
lemma justice (c:ℝ)(h:D x y≤ c*D z w): p k z w ≤ c^k * p k x y := by
    have hh := pay_pos x y; have he:= pay_pos z w
    unfold fund; rw [← mul_pow]; gcongr; rw [← one_div, div_le_iff₀ he, ← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ hh]; linarith only [h]
lemma justice' (h:D x y≤D z w): p k z w ≤ p k x y:= by simpa using justice (k:=k) x y z w 1 (by simpa using h)
lemma enlarge (h:D x y≤ c* R)(hx:0<R) : R⁻¹^k ≤ c^k * p k x y:= by unfold fund; rw [←mul_pow]; have hv:=pay_pos x y; gcongr; rw [← one_div, div_le_iff₀ hx, ← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ hv];linarith only [h]
lemma charge(h:R ≤ c*D x y)(hx:0<R): p k x y≤ c^k * R⁻¹^k:= by unfold fund; rw [← mul_pow]; have he:= pay_pos x y; gcongr; rw [← one_div,div_le_iff₀ he, ← div_eq_mul_inv,div_mul_eq_mul_div, le_div_iff₀ hx];linarith only [h]
lemma raising : D x y * p (k+1) x y=p k x y:= by unfold fund; have hp:=pay_pos x y; rw [pow_succ]; field_simp -- cancellation formula
lemma addF : p (k+m) x y=p k x y*p m x y:= pow_add ..
lemma binaryF (s:Finset S)(A:S→Prop)(f:S→ℝ){a b:ℝ}(h:∑ i ∈ s with A i,f i≤a)(hy:∑ i∈s with ¬ A i,f i≤b):∑ i∈s,f i ≤ a+b:= by rw [← Finset.sum_filter_add_sum_filter_not s A]; exact add_le_add h hy -- decidable Pred classical; syntax
lemma restricted (s:Finset S)(N:ℕ)(h:∀ i∈s,D x i ≤ N)(hv:0<N) : (s.card:ℝ)≤(3:ℝ)^4 * (N:ℝ)^4:= by
    have he:s.card ≤ (rim x N).card:= (Finset.card_le_card fun i hi=> by have hh:= h i hi; have ht: ticketN x i≤ N:= Nat.cast_le.mp (by exact hh); exact (rim_spec ..).mpr (le_trans (Nat.le_succ _) ht)); have hp: (rim x N).card≤ (3*N)^4:= (rim_count ..).trans (pow_le_pow_left' (by omega) _); rw [←mul_pow]; exact_mod_cast (he.trans hp)
-- ∗Total bound from ann crossing N/2.* Includes zero radius.
set_option maxHeartbeats 550000 in
lemma upperCost (N:ℕ)(s:Finset S)(hx:∀ i∈s,D x i≤N): ∑ i ∈ s,p 3 x i ≤ 1500*(N:ℝ):= by
    induction N using Nat.strong_induction_on generalizing s with
    | h N H=>
       rcases Nat.eq_zero_or_pos N with h|hv; · have ht: s=∅:= Finset.eq_empty_of_forall_notMem fun i hi=> (pay_pos x i).not_ge (le_trans (hx i hi) (by simp [h])); simp [ht,h]
       let r:= N/2; have hr:r<N:= by dsimp [r]; omega
       have hh : (r:ℝ) ≤ (N:ℝ)/2:= (le_div_iff₀ (by norm_num)).2 (by exact_mod_cast (show r*2≤N from by unfold r; omega)); let t:=s.filter (fun i=>D x i≤ (r:ℝ)); let u:=s.filter (fun i=> ¬ D x i≤(r:ℝ));
       have ht: ∑ i∈u,p 3 x i ≤ (u.card:ℝ)*((2:ℝ)^3*(N:ℝ)⁻¹^3):= by
           rw [← nsmul_eq_mul,← Finset.sum_const]; refine Finset.sum_le_sum fun i hi=>?_ ; apply charge x i ?_ (by exact_mod_cast hv); have he := lt_of_not_ge (mem_filter.mp hi).2; have hy: r< ticketN x i:= Nat.cast_lt.mp he; unfold Interval.mass; exact_mod_cast (show N≤2*ticketN x i from by unfold r at *;omega)
       have hu : (u.card:ℝ)≤ (3:ℝ)^4*(N:ℝ)^4:= restricted x _ _ hx hv |>.trans' (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset ..)))
       have h1 : (3:ℝ)^4*(N:ℝ)^4*(2^3*(N:ℝ)⁻¹^3)= (648:ℝ)*N:= by field_simp;ring
       refine le_trans (binaryF s (fun i=>D x i≤(r:ℝ)) (a:= 1500*(r:ℝ)) (b:=648*(N:ℝ)) _ ?_ ?_) (by linarith only [hh]); · exact H r hr t (fun i hi=>le_trans (mem_filter.mp hi).2 le_rfl) -- not include hx other?
       rw [← h1]; exact ht.trans (mul_le_mul_of_nonneg_right hu (by positivity))
lemma head_pay (s:Finset S) (hx:∀ i∈s,D x i ≤ R)(hr:R≥0): ∑ i∈s,p 3 x i ≤ 1500*R:= by refine le_trans (upperCost x ⌊R⌋₊ s (fun i hi=> Nat.cast_le.mpr ((Nat.le_floor_iff hr).mpr (hx i hi)))) (by gcongr; exact Nat.floor_le hr)
lemma tails (s:Finset S) (h: 4<k) (hx:∀ i∈s,R ≤ D x i)(hr:R>0):∑ i∈s,p k x i ≤ (2592:ℝ)*R⁻¹^(k-4):= by
   let N:=⌈R⌉₊; have he:N>0:=Nat.ceil_pos.mpr hr; let X:=Finset.univ.filter (fun t:Site n=>N≤ticketN x t); have ht:s⊆X:= fun i hi=> mem_filter.mpr ⟨mem_univ i,Nat.ceil_le.mpr (hx i hi)⟩;
   refine (Finset.sum_le_sum_of_subset_of_nonneg ht (fun i _ _=> (live x i).le)).trans ((tail x k he h).trans ?_); rw [show (2:ℝ)^5*3^4=2592 by norm_num]; gcongr; exact Nat.le_ceil R
end YM.PositionX.Chir.Imprint
