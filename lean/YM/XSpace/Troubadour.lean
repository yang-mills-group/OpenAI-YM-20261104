import YM.XSpace.Veneer

/-! # Native shell tariffs

 Sharp (no exponent sacrifices when locally/off-zero integrable). Else in some border
 tariffs we may buy a half exponent. Useful too to get chiral diagrams asympt with positions
 on a sphere of increasing dimensionless radius.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Octave
open Lattice Trace Sail Function Filter Set Relief Drama
open scoped Topology BigOperators
variable {n:ℕ} {D s:ℝ} {x y z:Cover}
abbrev pad := Drama.area
abbrev rate (k:ℕ)(x:Cover):= carry k (reach x)
lemma sound (n:ℕ)(x:Cover): 0<rate n x:=carry_pos ..
lemma rated (n:ℕ)(x:Cover):rate n x=(pad x)⁻¹^n:= rfl
@[simp] lemma flip_pad (x:Cover): pad (-x)=pad x:= by unfold pad Drama.area; rw [reach_neg]
lemma sym (x y:Cover):pad (x-y)=pad (y-x):=by rw [← flip_pad, neg_sub]
lemma triad (x y:Cover):pad (x+y) ≤ pad x+pad y:=by
  have ht : (↑(reach (x+y)):ℝ) ≤ ↑(reach x)+(reach y):=by exact_mod_cast Sail.tree x y
  unfold pad Drama.area; linarith
lemma trio (x y z:Cover): pad (x-y) ≤ pad (x-z)+pad (y-z):=by rw [sym y z]; exact (sub_add_sub_cancel x z y) ▸ triad (x-z) (z-y) -- ▸ test
lemma moon_le {k:ℕ} {D:ℝ} (hp:0<D)(h:D≤pad x): rate k x ≤ D⁻¹^k:=by rw [rated]; have hx:0<pad x:=included x; gcongr
lemma moon_mono (k:ℕ)(h:pad x≤pad y): rate k y≤rate k x:= moon_le (included x) h
lemma moon_mul (k j:ℕ)(x:Cover):rate k x*rate j x=rate (k+j) x:= carry_power ..
lemma moon_paid (j:ℕ)(x:Cover): pad x*rate (j+1) x=rate j x:=by simp_rw [rated]; have h:=included x; rw [pow_succ]; field_simp
lemma phase {T:Type*}{f:T→ℝ}{B:Finset T} {C E:ℝ}{p:T→Prop}(ha:∀ b⊆ B,(∀ x∈b,p x)→∑ i∈b,f i≤C)(hb:∀ b⊆ B,(∀ x∈b,¬p x)→∑ i∈b,f i≤ E): ∑ i∈B,f i≤C+E:=by
  classical rw [← Finset.sum_filter_add_sum_filter_not B p]; apply add_le_add; exact ha _ (Finset.filter_subset ..) (fun x h=> (Finset.mem_filter.mp h).2); exact hb _ (Finset.filter_subset ..) (fun x h=> (Finset.mem_filter.mp h).2)
-- sharp local integrals
lemma local_fee (r:ℕ) (h:n<4): (∑ i∈box r,rate n i) ≤ 128*(1+(r:ℝ))^(4-n) :=by
  rw [sum_shell]; set D:=1+(r:ℝ); have hD: 0<D:=by positivity
  calc
   _ ≤ ∑ k∈Finset.range (r+1), 128* D^(3-n) := ?_
   _ = _:=?_
  · apply Finset.sum_le_sum; intro k hk; have ht:k≤r:= Nat.lt_add_one_iff.mp (Finset.mem_range.mp hk); let p:=1+(k:ℝ); have hp:0<p:=(by positivity); have he : 0<(1+(k:ℝ)):=hp; have hn:((shell k).card :ℝ)≤ 128*p^3:= by dsimp [p]; exact_mod_cast volume_ring k
    calc
     _ = ((shell k).card:ℝ)* p⁻¹^n := by rw [← nsmul_eq_mul,← Finset.sum_const]; exact Finset.sum_congr rfl fun j hj=> by unfold rate; rw [(shell_rate ..).1 hj];rfl
     _ ≤ (128*p^3)*p⁻¹^n:= mul_le_mul_of_nonneg_right hn (by positivity)
     _ = 128*p^(3-n):=by
       have hh:3-n+n=3:=by omega
       apply Eq.symm; calc
        _ = 128*p^(3-n+n)*p⁻¹^n:= by rw [pow_add,inv_pow]; field_simp
        _ = _:= congr_arg (fun r:ℕ=>128*p^r*p⁻¹^n) hh
     _ ≤ _:=by dsimp [p,D]; gcongr
  · rw [show 4-n=3-n+1 by omega, Finset.sum_const,Finset.card_range,nsmul_eq_mul]; push_cast; rw [pow_succ,add_comm (r:ℝ)]; dsimp [D]; ring
lemma pay_in (h:n<4) (B:Finset Cover) (hd:0≤D) (H:∀ i∈B,pad i≤D): ∑ i∈B,rate n i≤ 128* D^(4-n):=by
  rcases Finset.eq_empty_or_nonempty B with e|p
  · subst B; rw [Finset.sum_empty]; positivity
  obtain ⟨x,hx,Hx⟩:= Finset.exists_max_image B reach p
  refine (Finset.sum_le_sum_of_subset_of_nonneg (t:=box (reach x)) (fun i hi=> (box_rate ..).2 (Hx i hi)) (fun i _ _=> (sound ..).le)).trans ((local_fee (reach x) h).trans ?_)
  change 128* pad x^(4-n)≤_; have hp:=included x; gcongr; exact H _ hx
-- sharp exterior integrals
abbrev away (r L:ℕ):= (box r).filter fun i=> L≤reach i
lemma hail (r k:ℕ): (∑ i∈shell r, rate k i) ≤ 128*(1+(r:ℝ))^3*carry k r:=by
  have hn:((shell r).card:ℝ)≤128*(1+(r:ℝ))^3:= by exact_mod_cast volume_ring r
  apply le_trans _ (mul_le_mul_of_nonneg_right hn (carry_pos k _).le); rw [← nsmul_eq_mul,← Finset.sum_const]; exact le_of_eq (Finset.sum_congr rfl fun i hi=> by unfold rate; rw [(shell_rate ..).1 hi])
-- telescope
lemma crawl (r L:ℕ): (∑ i ∈ Finset.range r, (if L≤ i then carry 2 i else 0)) ≤
  2*(1+(L:ℝ))⁻¹-2*(1+((max L r:ℕ):ℝ))⁻¹:= by -- type?
  induction r with
  | zero=> simp
  | succ r ih=>
    rw [Finset.sum_range_succ]; by_cases h:L≤r
    · rw [if_pos h,max_eq_right (by omega : L≤r+1)]; rw [max_eq_right h] at ih
      have hw : carry 2 r ≤ 2*(1+(r:ℝ))⁻¹ - 2*(1+(↑(r+1):ℝ))⁻¹ := by
        push_cast; set z:= (r:ℝ); have hz:0≤z:=(by positivity); change (1+z)⁻¹^2≤_; field_simp; nlinarith
      push_cast at hw ⊢; linarith
    rw [if_neg h]; rw [max_eq_left (by omega : r≤L)] at ih; rw [add_zero,max_eq_left (by omega : r+1≤L)]; exact ih
lemma wall (r L:ℕ): ∑ i∈ away r L,rate 5 i ≤ 256*(1+(L:ℝ))⁻¹:=by
  unfold away; rw [Finset.sum_filter,sum_shell]; have hp:0≤(L:ℝ):=by positivity
  have h(i:ℕ): (∑ x∈shell i, if L≤reach x then rate 5 x else 0)≤128*(if L≤ i then carry 2 i else 0):=by
    have he:(∑ x∈shell i, if L≤reach x then rate 5 x else 0)=∑ x∈shell i, if L≤ i then rate 5 x else 0:=Finset.sum_congr rfl fun j hj=> by rw [(shell_rate ..).1 hj] -- may also rewrite rate?
    rw [he]; split_ifs with ht
    · exact (hail i 5).trans_eq (by unfold carry; field_simp)
    simp
  calc
   _ ≤ ∑ i∈Finset.range (r+1),128*(if L≤ i then carry 2 i else 0):= Finset.sum_le_sum fun i _=>h i
   _ ≤ _:= ?_
  rw [← Finset.mul_sum]; apply le_trans (mul_le_mul_of_nonneg_left (crawl (r+1) L) (by norm_num : (0:ℝ)≤128)) _; have hx : 0≤2*(1+((max L (r+1):ℕ):ℝ))⁻¹:=(by positivity); linarith
lemma pay_out (h:4<n)(B:Finset Cover)(hd:0<D)(H:∀ i∈B,D≤pad i): ∑ i∈B,rate n i ≤256* D⁻¹^(n-4):=by
  rcases Finset.eq_empty_or_nonempty B with e|p
  · subst B; rw [Finset.sum_empty]; positivity
  obtain ⟨x,hx,h'⟩:= Finset.exists_min_image B reach p; let r:=reach x; have Hx:=H x hx
  have ht:B⊆ away (B.sup reach) r:= fun i hi=> Finset.mem_filter.mpr ⟨(box_rate ..).mpr (Finset.le_sup (f:=reach) hi), h' i hi⟩
  let f:=fun i=> rate 5 i*D⁻¹^(n-5)
  calc
    _ ≤ ∑ i∈B, rate 5 i*D⁻¹^(n-5):=by refine Finset.sum_le_sum fun i hi=>?_ ; rw [← show rate 5 i* rate (n-5) i=rate n i from by rw [moon_mul, show 5+(n-5)=n by omega]]; exact mul_le_mul_of_nonneg_left (moon_le hd (H i hi)) (sound ..).le
    _ = (∑ i∈B,rate 5 i)*D⁻¹^(n-5):= by rw [Finset.sum_mul]
    _ ≤ 256*(pad x)⁻¹*D⁻¹^(n-5):= mul_le_mul_of_nonneg_right ((Finset.sum_le_sum_of_subset_of_nonneg ht (fun i _ _=> (sound ..).le)).trans (wall ..)) (by positivity)
    _ ≤ _:= by rw [show n-4=n-5+1 by omega,pow_succ',← mul_assoc (256:ℝ) D⁻¹]; gcongr
lemma pay_mid (B:Finset Cover)(hd:1≤D)(H:∀ i∈B,pad i≤D): ∑ i∈B,rate 4 i ≤256* (Real.sqrt D):=by
  have he:= Real.sum_sqrt_mul_sqrt_le B (f:=rate 3) (g:= rate 5) (fun i=> (sound ..).le) (fun i=>(sound ..).le)
  have h:0<D:=zero_lt_one.trans_le hd
  calc
   _ ≤ Real.sqrt (∑ i∈B,rate 3 i) *Real.sqrt (∑ i∈B,rate 5 i):=by
    apply le_trans (Finset.sum_le_sum ?_) he; intro i _; rw [← Real.sqrt_mul (sound ..).le,moon_mul, ← show rate 4 i^2=rate 8 i from by rw [pow_two,moon_mul]]; rw [Real.sqrt_sq (sound ..).le]
   _ ≤ Real.sqrt (256*D)*Real.sqrt 256 := ?_
   _ = _:= ?_
  · have ht:=pay_in (n:=3) (by omega) B h.le H; have hh:=pay_out (n:=5) (by omega) B zero_lt_one (fun i _=> room i); norm_num at ht hh; gcongr; linarith
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤256)]; rw [mul_right_comm,← pow_two,Real.sq_sqrt (by norm_num : (0:ℝ)≤256)]
end YM.XSpace.Octave
