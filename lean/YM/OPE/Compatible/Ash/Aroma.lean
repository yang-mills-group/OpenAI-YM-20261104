import YM.OPE.Compatible.Ash.Husk
import YM.Next.FREE_KERNELS.Traffic
/-! # Uniform off-band bound and compact image cost -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Pert.Band Pert.Full Laurent
open scoped BigOperators Classical ContDiff
variable {n m:Side}
lemma peek (x:Site n):∃ k:Axis,(Lattice.lift x k).natAbs=pdist x:=by
    obtain ⟨k,_,h⟩:=Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i=>(Lattice.lift x i).natAbs); exact ⟨k,h.symm⟩
lemma starcast (x:Site n): ∃ i:Axis, (pdist x:ℝ)*dew n ≤ ‖char (step i) x-1‖:=by
   have he:=dew_pos n; obtain ⟨i,H⟩:= signal x _ he; have hh : ((n.val:ℝ)*dew n)⁻¹=1:=by rw [show ((n.val:ℝ)*dew n)=1 from mul_inv_cancel₀ (val_pos _).ne',inv_one]
   rw [hh, mul_one] at H
   obtain ⟨k,hk⟩:=peek x; have hh := (coordinate_le (incVec (dew n) (Lattice.lift x)) k); refine ⟨i, ?_⟩; rw [←hk]; apply le_trans _ (hh.trans H); apply le_of_eq; rw [incVec_apply, abs_mul,abs_of_pos he,← Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast,mul_comm]
lemma roof_peck (r:ℝ)(hr:0<r)(D:List Axis):∃ C≥0,∃ M:ℕ,∀ n:Side, M≤ n.val→ ∀ z:Site n,r≤ (pdist z:ℝ)*dew n→ ‖mildX D z‖≤C*dew n^(D.length+2):=by
   let m:=D.length+2+1; let s:=turn*((m:ℝ)+1); have hs:0<s:=by dsimp only [s]; positivity
   obtain ⟨B,hB,hx⟩:=steel hr zero_lt_one D; have hm :=((((((tendsto_inv_atTop_zero (𝕜:=ℝ)).comp tendsto_natCast_atTop_atTop).const_mul turn).mul_const (m:ℝ))|>.eventually (ge_mem_nhds (show turn*0*m < 1/2 from by simp))))
   obtain ⟨M,hM⟩:=eventually_atTop.mp (hm.and ((tendsto_inv_atTop_zero (𝕜:=ℝ)|>.comp tendsto_natCast_atTop_atTop |>.mul_const s).eventually (ge_mem_nhds (show 0*s < 1 from by simp))))
   refine ⟨Pert.Band.purse*s^(D.length+2)+B/s,add_nonneg (by unfold purse; positivity) (by positivity),M,fun n h z hh=>?_⟩; obtain ⟨hi,hp⟩:=hM n.val h; change turn*dew n*(m:ℝ) ≤ 1/2 at hi; rw [← show mesh n*(m:ℝ)= _ from congrArg (· * (m:ℝ)) (mesh_tick n)] at hi -- mesh /= not defeq
   have hu := dew_pos n; obtain ⟨k,hk⟩:=starcast z
   rw [full_X _ _ _ hu,norm_mul,Real.norm_of_nonneg (pow_nonneg hu.le _)]; grw [show ‖(joint (dew n) D z).re‖ ≤ ‖joint (dew n) D z‖ from Complex.abs_re_le_norm _,clear_joint _ s,norm_add_le]
   have hv:=add_le_add (lower (dew n) s hs hu (show dew n*s≤2 from le_trans (show dew n*s ≤ 1 from hp) one_le_two) z D) (hx n s hs le_rfl hp hi k z (le_trans hh hk)); rw [pow_one] at hv; rw [mul_comm (_+_)]; exact mul_le_mul_of_nonneg_left hv (pow_nonneg hu.le _)
private lemma barn_size (g:Ratio n m)(p:Site g.count)(hp:p≠0) : n.val ≤ pdist ((rye g).embed p) :=by -- g binder
   have he : Lattice.lift p≠ 0:=fun hx=> hp (by rw [←wrap_lift p,hx,map_zero]); obtain ⟨i,hi⟩:∃ i, (Lattice.lift p i).natAbs≥1:=by
       by_contra! hh; apply he; funext i; change _= (0:ℤ); have ht:= hh i; omega
   apply le_trans _ (component_le ((rye g).embed p) i); rw [(rye g).lift_embed, Pi.smul_apply,nsmul_eq_mul, Int.natAbs_mul,Int.natAbs_natCast]; change n.val≤ n.val*_ ; exact Nat.le_mul_of_pos_right _ hi
abbrev seam (D:List Axis)(n:Side)(x:Cover):ℝ:=mildX D (wrap n x)-hull D x
lemma image_peck (D:List Axis):∃ C≥0,∃ M:ℕ,∀ n:Side,M≤ n.val→∀ (m)(g:Ratio n m),g.count.val=2→∀ x:Cover,2*size x≤ n.val→
    ‖mildX D (wrap n x)-mildX D (wrap m x)‖ ≤ C*dew n^(D.length+2):=by
   obtain ⟨C,hC,M,h⟩:=roof_peck (4:ℝ)⁻¹ (by norm_num) D; refine ⟨(((2:ℝ))^ (4:ℕ))*C,by positivity,M,fun n hn m g hg x hx =>?_⟩
   have he:m.val=n.val*2:=by rw [g.exact_size,hg]
   have hu:= Finset.card_le_card (show (Finset.univ.erase (0:Site g.count)) ⊆Finset.univ from Finset.subset_univ _); rw [Finset.card_univ,site_card] at hu; have hV:=hu.trans_eq (congrArg (fun x:ℕ=>x^4) hg)
   rw [aliasX g,← Finset.sum_erase_add _ _ (a:=0) (by simp), show (rye g).embed 0=0 from (rye g).root.map_zero,zero_add,add_sub_cancel_right]
   let s:=Finset.univ.erase (0:Site g.count); let F(i):= (rye g).embed i+wrap m x
   have hs(p)(hp:p∈s): (4:ℝ)⁻¹ ≤ (pdist (F p):ℝ)*dew m:=by
       have hb : m.val ≤ pdist (F p)*4:=by have H:= (Next.Free.within_size x m); have hk:=pdist_triangle (F p) (-wrap m x); rw [show F p + -wrap m x=(rye g).embed p from by unfold F;abel,pdist_neg] at hk; have := barn_size g p (Finset.mem_erase.mp hp).1; omega
       rw [dew,←div_eq_mul_inv,le_div_iff₀ (val_pos _)]; apply le_of_mul_le_mul_left (a:=4) _ (show 0<(4:ℝ) from by norm_num); change 4*(4⁻¹*(m.val:ℝ)) ≤ 4*pdist (F p); ring_nf; exact_mod_cast hb
   let t:= C*dew n^(D.length+2); have ht(p)(hp:p∈s):‖mildX D (F p)‖ ≤ t:=by
      have hx:=dew_pos m; apply le_trans (h m (by omega) _ (hs p hp)); unfold t; gcongr; unfold dew; gcongr; unfold sizeR; exact_mod_cast (show n.val≤ m.val from by omega)
   apply le_trans ((norm_sum_le ..).trans (Finset.sum_le_sum (g:=fun (_:Site g.count)=> t) ht)); rw [Finset.sum_const,nsmul_eq_mul, mul_assoc]; have hx:=dew_pos n; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hV) (show 0≤t from by unfold t; positivity)
end YM.OPE.Balsam
