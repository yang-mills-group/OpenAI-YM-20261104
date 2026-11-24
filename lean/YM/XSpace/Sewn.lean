import YM.XSpace.Compat.Native
import YM.XSpace.Compat.NativeDifference
import YM.XSpace.Furl

/-!
# Period-DFT clip mesh accounting with pointwise costs even at far images

Includes all high-order discrete potential differences. This sets up the
unconditioned PT comparison at order-one. Estimate even at `x` close.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Sail
open YM.XSpace.Compat.KP
open Filter Set Function Lattice Bloch Laurent Complex MeasureTheory Further.FreeCovariance.KP
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable (A:List Axis) (n:Side)

def moved (p:E4):= city A (pick n p)
def clip (x:E4):= (∫ p:E4, song x (pick n p)*moved A n p)
lemma moved_ok : Integrable (moved A n):= (clip_pay n (uncirc A)).1
lemma clip_m (x:E4): Integrable (fun p=> song x (pick n p) * moved A n p) ∧
    clip A n x=(leap n)^4 • (∑ a:Site n×St, song x (lit n (pav n a))*city A (lit n (pav n a))):=by
  have h := clip_pay n (fun p=> song x p*uncirc A p); simp_rw [mul_left_comm (house _)] at h; exact h

lemma clip_scope (x:E4): spanRank n x * clip A n x=feed (moved A n) x:=by
  let t (i: Site n × St):=pav n i; let z i:= lit n (t i); let f i := city A (z i); let G (i : Site n×St):= (room n (t i)).indicator (fun p:E4=> f i)
  have hin (i:Site n×St): Integrable (G i):= (integrableOn_const ((room_paid n (t i)).2 ▸ ENNReal.ofReal_ne_top)).integrable_indicator (room_paid n (t i)).1
  have he p : moved A n p=∑ i,G i p:=by
    let w:= mark (leap n) p; change city A (lit n w)=_
    by_cases h : ∃ i,t i=w; obtain ⟨i,rfl'⟩:=h
    · rw [Finset.sum_eq_single i]
      · unfold G; rw [indicator_of_mem]; change city A (lit n w)= city A (lit n (t i)); rw [rfl']; exact Eq.symm rfl'
      · intro j _ hj; apply indicator_of_notMem; exact fun he=> hj (pav_sep n (Eq.trans (show w=t j from he).symm rfl'.symm))
      simp
    rw [city,show house (lit n w)=0 from by_contra fun he=> h (roof_hit _ he),zero_mul]; symm; refine Finset.sum_eq_zero fun i _=> indicator_of_notMem (s:=room n (t i)) (fun hh=>h ⟨i,(show w=t i from hh).symm⟩) _
  have hh (i:Site n×St): feed (G i) x= spanRank n x*((leap n)^4 • (song x (z i)* f i)):=by unfold feed; simp_rw [show ∀ p:E4,song x p*G i p=(room n (t i)).indicator (fun p=>song x p* f i) p from fun p=>by by_cases h:p∈room n (t i) <;> simp [h,G]]; rw [integral_indicator (room_paid n (t i)).1, integral_mul_const,light_cost]; unfold z; rw [real_smul]; push_cast; ring
  rw [(clip_m A n x).2]; unfold feed; simp_rw [he,Finset.mul_sum]; rw [integral_finsetSum _ (fun i _=> meal_ok (hin i) x),Finset.smul_sum,Finset.mul_sum]; exact (Finset.sum_congr rfl fun i _=>hh i).symm
lemma modulation_carry : ∃ C:ℝ,0<C∧∀ n:Side,∀ x:E4, ‖spanRank n x*clip A n x-feed (city A) x‖ ≤ C/(n.val:ℝ):=by
  obtain ⟨C,hC,H⟩:= mesh_variation A
  refine ⟨C,hC,fun n x=>?_⟩
  rw [clip_scope,feed,feed, ← integral_sub (meal_ok (moved_ok A n) x) (meal_ok (expense_city A) x)]
  apply (norm_integral_le_integral_norm ..).trans; simp_rw [← mul_sub,norm_mul,song_fee,one_mul]; exact H _
lemma ordinary_error : ∃ C:ℝ,0≤C∧∀ n:Side,∀ x:E4,‖clip A n x-feed (city A) x‖ ≤ C*(1+‖x‖)/(n.val:ℝ):=by
  obtain ⟨C,hC,H⟩:=mesh_variation A; let S:= ∫ p, ‖city A p‖; have hs : 0≤S:= integral_nonneg fun _=> norm_nonneg _
  refine ⟨C+4*Real.pi*S,by positivity,fun n x=>?_⟩
  let K:=2*leap n*‖x‖; let f:= song x; let G p:= f (pick n p)*moved A n p; let p:=fun x=> ‖city A x‖; let r p:= ‖moved A n p-city A p‖
  have hi (p:E4): ‖f (pick n p)-f p‖ ≤ K:=by
    have hi : ‖f (pick n p) - f p‖ ≤ ‖x‖ * ‖pick n p-p‖:= Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _=> (song_gradient x z).differentiableAt) (fun z _=> by rw [← norm_iteratedFDeriv_one]; simpa using song_quotes 1 x z) (convex_univ ..) (mem_univ _) (mem_univ _)
    apply hi.trans; unfold K; rw [mul_comm (2*leap n)]; gcongr; exact pick_near n p
  unfold clip feed; rw [← integral_sub (clip_m A n x).1 (meal_ok (expense_city A) x)]
  apply (norm_integral_le_integral_norm ..).trans; have ht: Integrable r:= ((moved_ok A n).sub (expense_city A)).norm; have hp : Integrable (fun x=>K*p x):=(expense_city A).norm.const_mul _
  apply le_trans (integral_mono ( ((clip_m A n x).1.sub (meal_ok (expense_city A) x)).norm) (ht.add hp) ?_); swap
  · intro u; change ‖f _*moved A n u-f u*city A u‖ ≤ r u+K*p u
    rw [show f (pick n u)*moved A n u-f u*city A u=f (pick n u)*(moved A n u-city A u)+(f (pick n u)-f u)*city A u by ring]; apply (norm_add_le ..).trans; rw [norm_mul,norm_mul,song_fee,one_mul]; apply add_le_add (_root_.le_refl _); exact mul_le_mul_of_nonneg_right (hi u) (norm_nonneg _)
  rw [integral_add' ht hp, integral_const_mul]; apply le_trans (add_le_add_left (show (∫ p,r p) ≤ _ from H n) _); change _ + K*S≤_; unfold K leap; have hb:=side_pos n; field_simp; have he : 0≤C*‖x‖:=by positivity
  nlinarith [Real.pi_pos, norm_nonneg x, mul_nonneg Real.pi_pos.le hs]

-- convert frequency samples to physical lag kernels
lemma rank_freq (p:Site n): tooth (lit n (lift p)) = Potential.q p := funext fun i=> by unfold tooth; rw [lit_mon]; exact Potential.crossed ..
lemma rank_periodic (p:Site n)(k:St): tooth (lit n (pav n (p,k)))=tooth (lit n (lift p)):=by funext i; unfold tooth Exterior.q; rw [lit_mon,paving_change,← Exterior.factor, ← Exterior.factor,mode_phase,mode_periodic,mul_one]
lemma root_period (p:Site n) (k:St): city A (lit n (pav n (p,k))) = house (lit n (pav n (p,k)))*uncirc A (lit n (lift p)):= by unfold city uncirc bill lamp spinner; simp_rw [rank_periodic]

def seen (x:Cover):=meter n * ∑ p:Site n, cell p (wrap n x) *uncirc A (lit n (lift p))
lemma exposed (x: Cover): seen A n x=tally * clip A n (rcast x):=by
  let z:= rcast x
  have h(p:Site n)(k:St): song z (lit n (pav n (p,k)))*city A (lit n (pav n (p,k)))= house (lit n (pav n (p,k)))*(cell p (wrap n x)*uncirc A (lit n (lift p))):=by rw [root_period,cell_wrap, ← cast_mode,paving_change,mode_phase,mode_periodic,mul_one]; ring
  rw [(clip_m A n (rcast x)).2,Fintype.sum_prod_type]; simp_rw [show ∀ p k,song (rcast x) (lit n (pav n (p,k)))*city A (lit n (pav n (p,k))) = _ from h, ← Finset.sum_mul, fold_door,one_mul]; unfold seen; rw [real_smul,← mul_assoc]; congr 1; unfold meter tally height leap; have hπ : (Real.pi:ℂ)≠0:=by exact_mod_cast Real.pi_ne_zero
  have hn:= side_ne n; push_cast; field_simp
@[simp] lemma seen_bare (n:Side) (x : Cover): seen [] n x=Potential.Gc n (wrap n x):= by unfold seen uncirc bill lamp spinner; simp only [rank_freq,List.map_nil,List.prod_nil,one_mul]; simp only [Potential.Gc,div_eq_mul_inv]; rfl
lemma seen_line (x : Cover): slot checkin A (Potential.Gc n ∘ wrap n) x = seen A n x:=by
  have he (S:List Axis) (i: Axis): checkin i (seen S n)=seen (S++[i]) n:=by
    funext y; unfold checkin seen; rw [← mul_sub,← Finset.sum_sub_distrib]; congr 1; refine Finset.sum_congr rfl fun p _=>?_ ; rw [map_add, cell_add, ← sub_mul]; unfold uncirc bill; rw [rank_freq,wrap_step]; simp [Potential.q]; ring
  rw [show Potential.Gc n ∘ wrap n= seen [] n from funext fun x=> (seen_bare ..).symm]; apply congr_fun _
  have hh(S):slot checkin A (seen S n)=seen (S++A) n:=by induction A generalizing S with| nil=>simp [slot]| cons a A ih=> rw [slot,he,ih]; simp
  exact hh []
end YM.XSpace.Sail
