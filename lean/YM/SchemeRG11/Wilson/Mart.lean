import YM.SchemeRG11.Wilson.Round
/-! Pair all near orbital terms and pay far with as many powers as stipulated. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Acorn
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular Full Atoll Pile Align Tile
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology
variable {G: Gauge} {I : Type*}[Fintype I] {T:Itinerary} (s:Finset I)(p:I→vellum G){o:StepPath T} (t:I→ℕ→ Cover)

def poseN(k:ℕ)(l:I):Site (T.period k):= wrap _ (t l k)+o k
-- proof uses one radius for each stipulation
omit [Fintype I] in
lemma indoor (hi:Interior T o)(v: ℕ→ Cover)(hv:Medium T v) (hw:∀ i,Medium T (t i))(i j:Axis):
 Flat T (fun m=> Graft s p (poseN t (o:=o) m) i j (wrap _ (v m)+o m)-turnup s p (fun u=>t u m) i j (v m)):=by
 have he:=anchored p s t hw hi i j v hv
 simp_rw [map_mul,induced,aerial,map_prod,vapour] at he; exact he
omit [Fintype I] in
lemma localize(d:ℕ) (F:ℕ→ Cover→ℝ)(T:Itinerary) (H:∀ v:ℕ→ Cover,(∀ i,v i∈box (canter T d i))→ Flat T (fun i=>F i (v i))):
 Flat T (fun i=>∑ v∈box (canter T d i),F i v):=by
 let B i:=box (canter T d i)
 choose v hv hx using fun i:ℕ=> Finset.exists_max_image (B i) (fun u=>|F i u|) (show (B i).Nonempty from ⟨0, center_box _⟩)
 have hp := H v hv
 intro n
 have hb:= (hp (4*d+n)).norm
 simp only [zpow_neg, zpow_natCast,norm_zero] at hb ⊢
 apply tendsto_zero_iff_norm_tendsto_zero.mpr; apply squeeze_zero' (g:=fun i=> (5:ℝ)^4*‖(T.gap i ^ (4*d+n))⁻¹ * F i (v i)‖) (Eventually.of_forall fun i=>norm_nonneg _) ?_; · simpa using hb.const_mul ((5:ℝ)^4)
 filter_upwards [T.cutoff.eventually (gt_mem_nhds zero_lt_one)] with i hi
 let r:=T.gap i;have h0:0<r:= T.positive i
 have hj: |∑ w∈ B i,F i w| ≤ ((B i).card:ℝ)*|F i (v i)|:=by
   refine (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (g:=fun _=>|F i (v i)|) ?_).trans ?_); exact fun w h=>hx i w h
   rw [Finset.sum_const,nsmul_eq_mul]
 have he : ((B i).card:ℝ) ≤ (2*(canter T d i:ℝ)+1)^4 :=by exact_mod_cast (boxCost (canter T d i))
 have h':(1:ℝ) ≤ r⁻¹^d:=one_le_pow₀ (one_le_inv_iff₀.mpr ⟨h0,(show r ≤1 from hi.le)⟩)
 have hB : ((B i).card:ℝ) ≤ 5^4 * r⁻¹^(4*d) := by
   apply he.trans; have hh:5^4*r⁻¹^(4*d)=(5*r⁻¹^d)^4:=by rw [show 4*d=d*4 from by ring, pow_mul,mul_pow]
   rw [hh]; gcongr; linarith [high T d i]
 have hN : 0<T.gap i:= T.positive i
 rw [norm_mul,Real.norm_of_nonneg (by positivity : 0≤(T.gap i ^ n)⁻¹), norm_mul,Real.norm_of_nonneg (by positivity: 0≤(T.gap i ^ (4*d+n))⁻¹)]
 apply (mul_le_mul_of_nonneg_left (hj.trans (mul_le_mul_of_nonneg_right hB (abs_nonneg _))) (show 0≤(r^n)⁻¹ by positivity)).trans_eq
 change _=(5:ℝ)^4*((r^(4*d+n))⁻¹* |F i (v i)|); rw [inv_pow,pow_add]; field_simp
omit [Fintype I] in
lemma supers (hi:Interior T o)(hw:∀ i,Medium T (t i)) (i j:Axis)(d:ℕ): Flat T (fun n=> (∑ x∈box (canter T d n),Graft s p (poseN t (o:=o) n) i j (wrap _ x + o n))-∑ x∈box (canter T d n),turnup s p (fun l=>t l n) i j x):=by
 simp only [←Finset.sum_sub_distrib]; apply localize; intro v hv
 apply indoor s p _ hi v ?_ hw i j
 refine ⟨d+1,?_⟩
 filter_upwards [T.cutoff.eventually (gt_mem_nhds zero_lt_one), ceiling T d (d+1) (Nat.lt_succ_self d) 3] with n hn hz
 have hp:= T.positive n
 simp only [zpow_neg,zpow_natCast, ← inv_pow]
 have he : (diam (v n):ℝ) ≤ (canter T d n:ℝ):=by exact_mod_cast wrapcost₂ _ (hv _)
 have hv:1≤ (T.gap n)⁻¹^d:=one_le_pow₀ (one_le_inv_iff₀.mpr ⟨hp,hn.le⟩)
 linarith [high T d n]
lemma district (hw:∀ i:I,Medium T (t i)): ∃ k:ℕ,∀ᶠ n in atTop,∀ i:I, diam (t i n) ≤ canter T k n:=by
 choose k hk using hw
 let K:= Finset.univ.sup k
 refine ⟨K,?_⟩; filter_upwards [Filter.eventually_all.mpr hk,T.cutoff.eventually (gt_mem_nhds zero_lt_one)] with n hn ht i
 apply (Nat.cast_le (α:=ℝ)).mp
 have hi:= hn i; have he:=T.positive n
 apply le_trans _ (low T K n)
 calc _ ≤ (T.gap n)⁻¹^(k i):=by rw [zpow_neg,zpow_natCast,←inv_pow] at hi;linarith
      _ ≤ _:=by gcongr; exact one_le_inv_iff₀.mpr ⟨he,ht.le⟩;apply Finset.le_sup (s:=Finset.univ) <| Finset.mem_univ i
lemma reserve (T:Itinerary)(C:ℝ){U:ℕ→ℝ}(d k:ℕ)(hd:d<k)(hC: C≥0)(H:∀ᶠ i in atTop,|U i| ≤ C / (canter T k i:ℝ)^2): Tendsto (fun i=> (T.gap i)^(-(d:ℤ))*U i) atTop (𝓝 0):=by
 let w:=k*2
 obtain ⟨J,hJ⟩:= Nat.exists_eq_add_of_le (show d ≤ k*2 by omega); have hj : J≠0:=by omega
 have h0 := (T.cutoff.pow J).const_mul C
 apply tendsto_zero_iff_norm_tendsto_zero.mpr
 rw [zero_pow hj, mul_zero] at h0
 apply squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) ?_ h0
 filter_upwards [H] with i hi
 simp only [norm_mul,zpow_neg,zpow_natCast,Real.norm_eq_abs,abs_inv, abs_pow,abs_of_pos (T.positive i)]
 let a:=T.gap i; have ha:0<a:=T.positive i
 calc _ ≤ (a^d)⁻¹*(C/(a⁻¹^k)^2):= mul_le_mul_of_nonneg_left (hi.trans (div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_left₀ (by positivity) (low T k i) 2))) (by positivity)
      _ = _ :=by rw [← pow_mul,hJ,pow_add,inv_pow a,inv_pow a]; change _=C*a^J; field_simp

lemma turnover (hi:Interior T o)(hw:∀ i,Medium T (t i))(i j:Axis):
 Flat T (fun k=> (∑ x:Site (T.period k), Graft s p (poseN t (o:=o) k) i j x)- 2* ∑' x:Cover,turnup s p (fun a=>t a k) i j x):=by
 classical
 obtain ⟨m,hm⟩:=district t hw
 obtain ⟨C,hC,H⟩:=dispatch s p i j
 obtain ⟨L,hL,F⟩:=cargo s p i j
 intro d
 let K:=d+m+1; let k:=canter T K
 let G (n:ℕ)(x:Site (T.period n)):= Graft s p (poseN t (o:=o) n) i j x
 let P(n:ℕ)(x:Cover):=turnup s p (fun a=>t a n) i j x
 let Z(n:ℕ):= T.gap n ^(-(d:ℤ))
 let A (n:ℕ):= ∑ x∈box (k n),G n (wrap _ x+ o n)
 let B(n:ℕ):= ∑ x∈box (k n),P n x
 let c(n:ℕ):=(∑' x,P n x)-B n
 let g(n:ℕ):= ∑ x:Site (T.period n) with k n < orbitRank _ (o n) i j x,G n x
 have hv:∀ᶠ n in atTop,4*(canter T m n+2) ≤ k n:=by
   filter_upwards [T.cutoff.eventually (gt_mem_nhds zero_lt_one),ceiling T m K (by omega) 16] with n hn hh
   apply (Nat.cast_le (α:=ℝ)).mp
   push_cast
   apply le_trans _ (low T K n)
   have h0: 1≤ (T.gap n)⁻¹^m:=one_le_pow₀ (one_le_inv_iff₀.mpr ⟨T.positive n,hn.le⟩)
   linarith [high T m n]
 have e : Tendsto (fun n=> Z n*g n) atTop (𝓝 0):=reserve T C d K (by omega) hC.le (by filter_upwards [hv,hm] with n hN hK; exact H _ (poseN t (o:=o) n) _ (fun b=> by simpa only [poseN,add_sub_cancel_right] using (mod_le (N:=T.period n) _).trans (hK b)) _ hN)
 have e': Tendsto (fun n=>Z n*c n) atTop (𝓝 0):=reserve T L d K (by omega) hL.le (by filter_upwards [hv,hm] with n hN hK; exact (F _ _ hK (k n) hN).2)
 have ne:Tendsto (fun n=> Z n*(A n-B n)) atTop (𝓝 0):= supers s p t hi hw i j K d
 have hs := (e.add (ne.const_mul 2)).sub (e'.const_mul 2)
 rw [mul_zero, add_zero,sub_zero] at hs
 apply hs.congr'
 obtain ⟨v,hV,hϕ⟩:=hi
 filter_upwards [hugeWalk T K 1 2 (by norm_num), hugeWalk T K v 5 hV,hϕ] with n hh ho hΩ
 let y := T.period n; let u := o n
 have hp:=canter_pos T K n
 have hκ : 2*k n < y.val:= by unfold k y; exact_mod_cast (by simpa only [one_mul] using hh: 2*(canter T K n:ℝ)< (T.period n).val)
 have heν : (5:ℕ)*k n<pdist (u+u):=by exact_mod_cast lt_of_lt_of_le ho hΩ
 have ht : (∑ x:Site (T.period n),G n x) = 2*A n+g n:=hearth _ _ _ _ hκ (by change 0<k n at hp; change _< pdist (u+u); omega) (G n) (fun x=> mirror_avg ..)
 change Z n * g n + 2*(Z n*(A n-B n))-2*(Z n*c n) = Z n*(_-2*∑' x,P n x)
 rw [show ∑ x:Site (T.period n),Graft s p (poseN t n (o:=o)) i j x =_ from ht]; unfold c;ring
end YM.SchemeRG11.Acorn
