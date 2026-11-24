import YM.OPE.Compatible.Tides.Dory
/-!
# Geometric power tail
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume
open scoped BigOperators Classical ContDiff
variable {j k r Q:ℕ}{a:Cover}{f:Cover→ℝ}{B:ℝ}
lemma soaking :Tendsto pod atTop atTop:=by
    apply Filter.tendsto_atTop.mpr; intro A; let n:= A.sup size; filter_upwards [eventually_ge_atTop n] with i hi p hp; exact in_pod.mpr (le_trans (Finset.le_sup (s:=A) hp) hi)
lemma rim_eq (q:ℕ) : pod (q+1)=pod q ∪ podAt (q+1):=by ext;simp only [Finset.mem_union,in_podAt,in_pod];omega
private lemma pentroof (q:ℕ):((podAt q).card:ℝ) ≤ 16*(q+1:ℝ)^3:=by
      grw [pot_card q]; push_cast; grw [show (2*(q:ℝ)+1) ≤ 2*(q+1) from by linarith]; exact le_of_eq (by ring)
-- unit boundary q+1, inverse gap. shift
lemma rim_fare (k j:ℕ)(hk:k>0)(hf:∀ x∈podAt (j+1),‖f x‖ ≤ B/(notch x:ℝ)^(k+4))(hB:0≤B):
    ∑ x∈podAt (j+1),‖f x‖ ≤ 16*B*(1/(j+1:ℝ)^k-1/(j+2:ℝ)^k):=by
       let v:ℝ:=j+2; let u:ℝ:=j+1; have hp:0<u:=by unfold u; positivity
       have hv: v=u+1:=by unfold u v; ring
       have hr: u < v:=by rw [hv]; exact lt_add_one u
       have hk':(1:ℝ)/v^(k+1) ≤ 1/u^k - 1/v^k:=by
           -- compare (v/u)^k>= v/u.; diff = (v/u−1)u.S≥ 1/v
           have ha := one_le_div hp |>.mpr hr.le
           have hh: v/u ≤ (v/u)^k:=by simpa using (pow_le_pow_right₀ ha (show 1≤ k from hk))
           have hi:1/v^k*(v/u-1) ≤ (1/u^k -1/v^k):=by
               apply le_trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hh 1) (by have hx:=hp.trans hr; positivity)) (le_of_eq ?_); rw [div_pow]; have hz:=hp.trans hr; field_simp
           apply le_trans _ hi; rw [show v/u-1=1/u from by rw [hv]; field_simp;ring, ← mul_div_assoc, mul_one, div_div, pow_succ]; gcongr
       refine (Finset.sum_le_sum (g:=fun _=> B/v^(k+4)) ?_).trans ?_; · intro x hx; apply le_trans (hf x hx); unfold notch; rw [in_podAt.mp hx, ← add_assoc,add_comm 1 j]; unfold v; push_cast;exact le_of_eq (by ring)
       have he:0 < v:=hp.trans hr; rw [Finset.sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (pentroof (j+1)) (show 0 ≤ _ from div_nonneg hB (pow_nonneg he.le _))).trans; rw [show (((j+1:ℕ):ℝ)+1)=v from by unfold v; push_cast; ring]; apply le_trans _ (mul_le_mul_of_nonneg_left hk' (mul_nonneg (by norm_num) hB)); apply le_of_eq; rw [pow_add v k 4,pow_succ]; field_simp;ring -- pow_succ pattern
lemma tail_pew (hf:∀ x,‖f x‖ ≤ B/(notch x:ℝ)^(k+4))(hk:k>0)(hB:0≤ B)(K M:ℕ)(h:K≤ M): ∑ x∈pod M,‖f x‖ -∑ x∈pod K,‖f x‖ ≤ 16*B*(1/(K+1:ℝ)^k-1/(M+1:ℝ)^k):=by
   induction M,h using Nat.le_induction with
   | base=>simp
   | succ M he ih=>
     rw [rim_eq, Finset.sum_union (Finset.disjoint_left.mpr (fun x h h' => by have hx:=in_podAt.mp h'; have hy:=in_pod.mp h; omega))]
     push_cast; have hp:=rim_fare k M hk (fun x _=>hf x) hB; rw [show (↑M:ℝ)+1+1=M+2 from by ring]; linarith only [ih,hp]
lemma fab (hf:∀ x,‖f x‖ ≤ B/(notch x:ℝ)^(k+4))(hk:k>0)(hB:0≤ B): Summable (fun x=>‖f x‖):=by
    let m:ℝ:=∑ x∈pod 0,‖f x‖; refine summable_of_sum_le (c:=m+16*B) (fun _=>norm_nonneg _) ?_
    intro u; obtain ⟨i,hi⟩:= (soaking.eventually (eventually_ge_atTop u)).exists; apply (Finset.sum_le_sum_of_subset_of_nonneg hi (fun i _ _=> norm_nonneg _)).trans; have hs:=tail_pew hf hk hB 0 i (by omega); simp only [Nat.cast_zero,zero_add,one_pow,div_one] at hs; grw [sub_le_self _ (show 0 ≤ (1:ℝ)/((i:ℝ)+1)^k from by positivity)] at hs; unfold m; linarith only [hs]
lemma stove (hf:∀ x,‖f x‖ ≤ B/(notch x:ℝ)^(k+4))(hk:k>0)(hB:0≤ B)(K):
    ‖(∑' x,f x)- ∑ x∈pod K,f x‖ ≤ 16*B/(K+1:ℝ)^k:=by
   have ht: Tendsto (fun i=>∑ x∈pod i,f x) atTop (𝓝 (∑' x,f x)):= Filter.Tendsto.comp (g:=fun i:Finset Cover=> ∑ x∈i,f x) (fab hf hk hB).of_norm.hasSum soaking
   refine le_of_tendsto ((ht.sub_const _).norm) ?_; filter_upwards [eventually_ge_atTop K] with i hi; have he:pod K ⊆ pod i:= fun x hx=>in_pod.mpr (le_trans (in_pod.mp hx) hi)
   have hx:=tail_pew hf hk hB K i hi; simp_rw [← Finset.sum_sdiff_eq_sub he] at hx ⊢; apply le_trans ((norm_sum_le ..).trans hx); grw [sub_le_self (1/((K:ℝ)+1)^k) (show 0≤1/((i:ℝ)+1)^k from by positivity)]; ring_nf; exact le_rfl
end YM.OPE.Balsam
