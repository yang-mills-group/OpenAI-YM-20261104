import YM.Frontier6.Pair.CanvasStep
import YM.Frontier6.Trajectory.Transport

/-!
# Tilted lower plane at a common origin.

Prove quantitative estimates on whole string, not uniformity from a sequence
of norm-priced non-triangular maps. This part uses no claims on the continuum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Canvas
open Function Lattice Wilson RG Labels Bid Work.G08 Finset Extra.Histories MergeProof
open scoped BigOperators
variable {G:Gauge}

/-- Exponent overhead for front strings. -/
def fee (C:Levels G)(i:ℕ) := (∏ j∈range i,(C.params (j+1)).columns)^2
lemma fee_one (C:Levels G) (i:ℕ) : 1  ≤  fee C i := one_le_pow₀ (one_le_prod fun j _=> (C.params _).columns_ge)
lemma fee_succ (C:Levels G) (i:ℕ) : fee C (i+1)=fee C i*(C.params (i+1)).columns^2:= by simp only [fee,prod_range_succ,mul_pow]

variable {C:Levels G}{W:Worth} (hr:roomCost C W) (hB:Bank W C)

lemma fine_columns (hr:roomCost C W) (i:ℕ) : 2*bound C W i  ≤  (C.params (i+1)).columns ∧ 1+slope C W i  ≤  (C.params (i+1)).columns := by
    let c:= bound C W i; let p:= W.K (C.clock.J (i+1)+1)
    have he:1  ≤  c:= W.prices _; have hp:c ≤ p:=W.growth (Nat.le_succ _)
    have h : 64*p^2  ≤  _ :=hr (i+1)
    refine ⟨(room_slack he hp h).2,?_⟩; change 1+4*c^2  ≤  _; nlinarith only [he,(pow_le_pow_left₀ (zero_le_one.trans he) hp 2),h]

variable {D r p N m:ℕ} {F:Labels.Frame G D} {H:History G} {A:Source.Hol G} {P:Source.SectionData F}
variable {Z:Music F H N p} (h:Sung P H N p A W r Z)
variable (hT:∀ i:ℕ, r  ≤  i→ i  <  N→ ∃ T:Heading F, (∃ c:ℝ, Push.Local.Leading T.map.toLinearMap c) ∧ CoeffStep H p W i (Z.tone (i+1)) (Z.tone i) T)
set_option quotPrecheck false
local notation "l!"=>H.levels
local notation "C!"=>fun i:ℕ=>(H.levels.params (i+1)).columns
local notation "f"=>F.coeffSize
local notation "E!"=>fun i=>(Z.tone i).index
variable (hr':roomCost H.levels W) (hb:Bank W H.levels)(e:ℕ)(he:e < D){w:F.Coeff}
local notation "g"=>cut F e
local notation "b"=>shed F e
local notation "L!"=> fun i:ℕ=>(H.S.block i).val
local notation "F!"=>fee H.levels

include h
lemma head_index (w:F.Coeff) : E! N w=w:=by
   rw [show (Z.tone N).index w=((Z.tone N).plays w).x from (h.head.heard.currents _).symm]; exact h.head.out w -- edit
include hT hb he

lemma plane_step (hi:r ≤ m)(hm:m < N)(hv:f (b (E! (m+1) w))  ≤  slope l! W (m+1)*f (g (E! (m+1) w))) :
    (L! m : ℝ)^(D-e)* f (g (E! (m+1) w))  ≤  2*bound l! W m*f (g (E! m w)) ∧ f (b (E! m w))  ≤  slope l! W m * f (g (E! m w)) := by
    obtain ⟨T,⟨c,hc⟩,hZ⟩:= hT m hi hm
    apply descend_step l! W hb m F e (E! _ w) (E! _ w) hc hZ.costs _ he hv
    rw [show E! m w=_ from ((h.earned m hi hm.le).currents w).symm]; exact hZ.error w

lemma stays (hv:b w=0)(hi:r ≤ m)(hm:m ≤ N) : f (b (E! m w))  ≤  slope l! W m * f (g (E! m w)):= by
    induction hm using Nat.decreasingInduction with
    | self=> rw [head_index h,hv,size_zero]; exact mul_nonneg (by unfold slope; positivity) (size_nonneg ..)
    | of_succ m hm ih=> exact (plane_step h hT hb e he hi hm (ih (hi.trans m.le_succ))).2

lemma through_low {x:F.Coeff} (ht:g (E! m x)=0)(hy:b x=0)(hi:r ≤ m)(hm:m ≤ N): x=0:=by
    have hx:= stays h hT hb e he hy hi hm; rw [ht,size_zero,mul_zero] at hx; apply (E! m).injective; rw [map_zero]
    have hz:= from_shed F e (E! m x); rw [ht,zero_add,size_separates _ _ hx] at hz; exact hz.symm

lemma redecompose (w:F.Coeff)(hi:r ≤ m)(hm:m ≤ N): ∃ v:F.Coeff,b v=0 ∧ g (E! m (w-v))=0 ∧ f (E! m (w-v)) ≤  (1+slope l! W m)* f (E! m w):= by
    let K:=LinearMap.ker (shed F e); let Q:= ((g).comp (E! m).toLinearMap).restrict (p:=K) (q:=K) (fun x _ => shed_cut ..)
    have ht:Injective Q:= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (fun x hx => ?_))
    · have hx:= LinearMap.injective_iff_surjective.mp ht; obtain ⟨v,hv⟩:= hx (⟨g (E! m w),shed_cut ..⟩:K)
      have hV:g (E! m v.val)=g (E! m w):= congr_arg Subtype.val hv
      have hS:shed F e v.val=0:=v.property
      have hQ : g (E! m (w-v.val))=0:=by rw [map_sub,map_sub,hV,sub_self]
      refine ⟨v.val,hS,hQ,?_⟩
      have hy:= stays h hT hb e he hS hi hm; rw [hV] at hy
      nth_rw 1 [pair_size F e (E! m _)]
      rw [hQ,size_zero,zero_add,map_sub,map_sub]
      refine (size_sub _ _ _).trans ?_; rw [add_mul,one_mul]; exact add_le_add (price_shed ..) (hy.trans (mul_le_mul_of_nonneg_left (price_cut ..) (by unfold slope; positivity)))
    apply Subtype.ext; exact through_low h hT hb e he (show g (E! m x.val)=0 from congr_arg Subtype.val hx) (show b x.val=0 from x.property) hi hm -- anonymous binder names?

include hr'
/-- Moving backward from fixed reference (low → fine), while in this plane,
an engineering decay with exact dimension D-e. -/
lemma backwards (w:F.Coeff)(hL:b w=0)(hi:r ≤ m)(hm:m ≤ N):
   f (g (E! m w))  ≤  F! m * ((H.S.a m/H.S.a r)^(D-e)) * f (g (E! r w)):= by
   induction hi with
   | refl=> rw [div_self (H.S.a_pos _).ne',one_pow,mul_one]; exact le_mul_of_one_le_left (size_nonneg ..) (fee_one l! r)
   | step hi ih=>
       rename_i i; let u j:= f (g (E! j w)); have hu j:0  ≤  u j:=size_nonneg ..
       let L:ℝ:= L! i; let d:=D-e; let c:= C! i
       have hX:= (plane_step h hT hb e he hi hm (stays h hT hb e he hL (le_trans hi i.le_succ) hm)).1
       have hc:1 ≤ c:= (H.levels.params _).columns_ge
       have hy : L^d * u (i+1)  ≤  c^2*(F! i*(H.S.a i/H.S.a r)^d*u r):=by
          have ht : 2*bound l! W i  ≤  c^2:= (fine_columns hr' i).1.trans (le_mul_of_one_le_right (zero_le_one.trans hc) hc|>.trans_eq (pow_two _).symm)
          exact le_trans hX (le_trans (mul_le_mul_of_nonneg_right ht (hu i)) (mul_le_mul_of_nonneg_left (ih (le_trans i.le_succ hm)) (sq_nonneg _)))
       refine le_of_mul_le_mul_left (le_trans hy (le_of_eq (?_))) (pow_pos (by unfold L; positivity) d)
       change _ = L^d*(F! (i+1)*(H.S.a (i+1)/H.S.a r)^d*u r)
       rw [fee_succ]; have hL:0  <  (L! i:ℝ):=by dsimp only; positivity
       have hx : (H.S.a i/H.S.a r)^d=L^d*(H.S.a (i+1)/H.S.a r)^d:=by
           rw [← mul_pow]; congr 1; rw [H.S.a_step]; change _= L*(H.S.a i/L/_); field_simp [show L≠0 from hL.ne']
       rw [hx]; unfold c; dsimp only; ring

lemma backwards_top (w:F.Coeff)(hL:b w=0)(hN:r ≤ N) :
   f w  ≤  F! N * ((H.S.a N/H.S.a r)^(D-e)) * f (E! r w) := by
   have ht:= backwards h hT hr' hb e he w hL hN (le_refl N); rw [head_index h] at ht
   have he':g w=w:= sub_eq_zero.mp (by rw [← neg_sub]; change -(shed F e w)=0; rw [hL,neg_zero])
   rw [he'] at ht; exact ht.trans (mul_le_mul_of_nonneg_left (price_cut ..) (mul_nonneg (zero_le_one.trans (fee_one ..)) (pow_nonneg (div_nonneg (H.S.a_pos _).le (H.S.a_pos _).le) _)))

/-- Re-project at intermediate stations: no estimate on the ambient-space
map restricted to horizontal needs to transport the error. Only leading grade bound
and a tail remainder. -/
lemma adjust (w:F.Coeff)(hi:r ≤ m)(hm:m < N)(hw:g (E! (m+1) w)=0) : ∃ w', b w'=0 ∧ g (E! m (w-w'))=0 ∧
    f (E! m (w-w')) ≤ (C! m)^2*(L! m:ℝ)^(D-(e+1))*f (E! (m+1) w):= by
    obtain ⟨v,h₀,h₁,h₂⟩:= redecompose h hT hb e he w hi hm.le
    obtain ⟨T,⟨c,hc⟩,hZ⟩:= hT m hi hm
    have hx : f (E! m w)  ≤  2*bound l! W m*(L! m:ℝ)^(D-(e+1))* f (E! (m+1) w):= by
      apply transverse_step l! W hb m F e (E! _ w) (E! _ w) (fun x=> hZ.costs x) _ hw
      rw [show E! m w=_ from ((h.earned m hi hm.le).currents w).symm]; exact hZ.error w
    refine ⟨v,h₀,h₁,h₂.trans ((mul_le_mul (fine_columns hr' m).2 hx (size_nonneg F (E! m w)) (zero_le_one.trans (H.levels.params (m+1)).columns_ge)).trans ?_)⟩
    let P : ℝ:=L! m; have hp:0 ≤ P:=by unfold P; positivity
    have ht:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (fine_columns hr' m).1 (zero_le_one.trans (H.levels.params (m+1)).columns_ge)) (pow_nonneg hp (D-(e+1)))) (size_nonneg F (E! (m+1) w)); change C! m * (2*bound l! W m * P^(D-(e+1))*_) ≤ (C! m)^2*P^_*_; linarith only [ht]

lemma carry_above (w:F.Coeff)(hi:r ≤ m)(hm:m ≤ N)(hw:g (E! m w)=0): ∃ v:F.Coeff, b v=0 ∧
    f (E! r (w-v))  ≤  F! m *((H.S.a r/H.S.a m)^(D-(e+1)))*f (E! m w):= by
   induction hi generalizing w with
   | refl=>
       refine ⟨0,map_zero _,?_⟩; rw [sub_zero,div_self (H.S.a_pos _).ne',one_pow,mul_one]; exact le_mul_of_one_le_left (size_nonneg ..) (fee_one ..)
   | step hi ih=>
       rename_i i; let k:=D-(e+1); obtain ⟨x,hx,hX,h'⟩:= adjust h hT hr' hb e he w hi hm hw
       obtain ⟨v,hv,hq⟩:=ih (w-x) (le_trans i.le_succ hm) hX -- order
       refine ⟨x+v,by rw [map_add,hx,hv,add_zero],?_⟩; rw [← sub_sub]
       refine hq.trans ((mul_le_mul_of_nonneg_left h' (mul_nonneg (zero_le_one.trans (fee_one ..)) (pow_nonneg (div_nonneg (H.S.a_pos _).le (H.S.a_pos _).le) _))).trans_eq ?_)
       rw [fee_succ,H.S.a_step]; dsimp only; rw [div_div_eq_mul_div]; rw [show H.S.a r*(L! i:ℝ)/H.S.a i=H.S.a r/H.S.a i*(L! i:ℝ) by ring]; rw [mul_pow]; ring

lemma yield_plane (w:F.Coeff)(hi:r ≤ m)(hm:m ≤ N): ∃ v:F.Coeff, b v=0 ∧
    f (E! r (w-v))  ≤  (F! m *((H.S.a r/H.S.a m)^(D-(e+1)))*(C! m))* f (E! m w):=by
   obtain ⟨x,hx,hX,hc⟩:= redecompose h hT hb e he w hi hm
   obtain ⟨v,hv,hq⟩:= carry_above h hT hr' hb e he (w-x) hi hm hX
   have ht:= hc.trans (mul_le_mul_of_nonneg_right (fine_columns hr' m).2 (size_nonneg ..))
   refine ⟨x+v,by rw [map_add,hx,hv,add_zero],?_⟩; rw [← sub_sub]; exact hq.trans ((mul_le_mul_of_nonneg_left ht (mul_nonneg (zero_le_one.trans (fee_one ..)) (pow_nonneg (div_nonneg (H.S.a_pos _).le (H.S.a_pos _).le) _))).trans_eq (mul_assoc ..).symm)
end YM.Frontier6.Canvas
