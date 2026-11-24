import YM.Frontier6.Multi.Storage.Concentration

/-! Power expense. Paid only for renewals and leader groups. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V C O:Type}[Fintype V][DecidableEq V][Fintype O][DecidableEq O][Fintype C][DecidableEq C]
variable {G:Gauge}
lemma fib_prod {M:Type*}[CommMonoid M](π:Concentrate O C)(w:O→ M): (∏ j:C, ∏ i∈π.fiber j,w i)=∏ i:O,w i:=by
    rw [← Finset.prod_biUnion,show (univ.biUnion _) = univ from (by ext i; simp [Concentrate.fiber] : univ.biUnion π.fiber=univ)]
    exact fun x hx y hy he=> disjoint_left.mpr (fun i hi ht=>he (((mem_filter.mp hi).2).symm.trans (mem_filter.mp ht).2))

def total {M:Type*}[CommMonoid M]{O:Type}[Fintype O](w:O→M):= ∏ i:O,w i
lemma total_pos {w:O→ℝ}(h:∀ i,0<w i) :0 < total w:= prod_pos (fun i _=>h i)
def restoreRate (A:Levels G)(δ:ℕ→ℝ)(i:ℕ) :ℝ := δ i^2/(8*Real.exp (((A.budget i).supportExponent+1/2)*inscribed A i))
-- Used per input label to budget a growth event
lemma teamwork (A:Levels G)(δ:ℕ→ℝ)(w:O→ℝ)(π:Concentrate O C)(n i:ℕ){E:ℝ}(h:0<E)(hf:E ≤ 1)(ht:E ≤ restoreRate A δ i) (hp:0 < δ i)(hw:∀ i,0<w i)(he:Fintype.card O ≤ n) : E^n * total w ≤ total (fun j=> lot A i δ π (fun b=>δ i*w b) j/8):=by
    let F:= restoreRate A δ i; have hv:0 < F:= lt_of_lt_of_le h ht
    have hh(x): pence A i δ (fun b=>δ i*w b) x=8 * (F*w x):=by unfold pence F Salt.tow restoreRate; ring
    have hA:F^Fintype.card O * total w=∏ j,w j*F:=by rw [prod_mul_distrib,prod_const,card_univ]; exact mul_comm ..
    calc
      _ ≤ F^Fintype.card O * total w:= mul_le_mul_of_nonneg_right ((pow_le_pow_of_le_one h.le hf he).trans (pow_le_pow_left₀ h.le ht _)) (total_pos hw|>.le)
      _ ≤ _ := by
        unfold total lot; rw [prod_div_distrib,prod_const,fib_prod,card_univ]; simp_rw [hh,prod_mul_distrib,prod_const,card_univ]; rw [le_div_iff₀]; swap; · positivity
        refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show (1:ℝ) ≤8 by norm_num) (stable_size π)) (mul_nonneg (pow_nonneg hv.le _) (total_pos hw|>.le))) ?_; apply le_of_eq; ring

def warrant (S:Schedule)(E:ℝ)(k n j i:ℕ)(w:ℝ):ℝ:= (S.a j/S.a i)^(4*n) * (E^(n*k)*w)
lemma warrant_start (S:Schedule)(E:ℝ)(n j:ℕ)(a:ℝ): warrant S E 0 n j j a=a:=by simp [warrant,(S.a_pos _).ne']
lemma warrant_step (S:Schedule)(E:ℝ)(k n j i:ℕ)(w:ℝ): warrant S E k n j i w= (S.a (i+1)/S.a i)^(4*n)*warrant S E k n j (i+1) w:=by
   unfold warrant; rw [← mul_assoc (_^(4*n)) (_^(4*n)),← mul_pow]; have h:= S.a_pos (i+1); rw [show S.a (i+1)/S.a i*(S.a j/S.a (i+1))=S.a j/S.a i from (by field_simp)]
lemma warrant_new (S:Schedule)(E:ℝ)(k n j i:ℕ)(w:ℝ): warrant S E (k+1) n j i w= E^n*warrant S E k n j i w:= by unfold warrant; rw [mul_add,pow_add,mul_one]; ring
lemma warrant_extra (S:Schedule)(E:ℝ)(k n j i:ℕ)(w:ℝ)(k':ℕ)(h:k ≤ k')(he:0 ≤ E)(hf:E ≤ 1)(hw:0 ≤ w): warrant S E k' n j i w ≤ warrant S E k n j i w:=by
   apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one he hf (Nat.mul_le_mul_left _ h)) hw) (pow_nonneg (div_nonneg (S.a_pos _).le (S.a_pos _).le) _)
lemma worn (S:Schedule)(E:ℝ)(k n j i:ℕ)(w:ℝ)(he:0 ≤ E)(hw:0 ≤ w): warrant S E k n j i w ≤ warrant S E k n j (i+1) w:=by
   rw [warrant_step]; apply mul_le_of_le_one_left (mul_nonneg (pow_nonneg (div_nonneg (S.a_pos _).le (S.a_pos _).le) _) (mul_nonneg (pow_nonneg he _) hw)) (pow_le_one₀ (div_nonneg (S.a_pos _).le (S.a_pos _).le) ((div_le_one (S.a_pos _)).2 (pinion_age S i)))
lemma warranted (S:Schedule)(w:O→ℝ)(E:ℝ)(k n j i:ℕ)(w':ℝ)(he:Fintype.card O ≤ n)(h: warrant S E k n j (i+1) w' ≤ total w)(hw:∀ i,0<w i): warrant S E k n j i w' ≤ total (pinion S i w):=by
   rw [warrant_step]; unfold pinion total; rw [prod_mul_distrib,prod_const,card_univ,← pow_mul,mul_comm (∏ i,w i)]
   let T:= S.a (i+1)/S.a i; have ht:0 ≤ T:= div_nonneg (S.a_pos _).le (S.a_pos _).le; refine (mul_le_mul_of_nonneg_left h (pow_nonneg ht (4*n))).trans (mul_le_mul_of_nonneg_right ?_ (total_pos hw|>.le)) -- hh if requires a1 0 ≤warrant input not given
   · exact pow_le_pow_of_le_one ht ((div_le_one (S.a_pos _)).2 (pinion_age S i)) (Nat.mul_le_mul_left _ he)
end YM.MergeProof.Canopies
