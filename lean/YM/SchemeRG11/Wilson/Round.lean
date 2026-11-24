import YM.SchemeRG11.Wilson.Wharf
/-! Fixed-order precision at schedules T. Each computation separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Acorn
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular Full Atoll Pile Align Tile
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology
variable {G: Gauge} {I : Type*} {N:Side}(T:Itinerary)

def canter (d i:ℕ) : ℕ:= ⌈(T.gap i)⁻¹^d⌉₊
lemma canter_pos (d i:ℕ): 0< canter T d i:= Nat.ceil_pos.mpr (by have := T.positive i; positivity)
lemma low(d i:ℕ):(T.gap i)⁻¹^d ≤ (canter T d i:ℝ):= Nat.le_ceil _
lemma high(d i:ℕ): (canter T d i:ℝ) ≤ (T.gap i)⁻¹^d+1:=(Nat.ceil_lt_add_one (show 0≤(T.gap i)⁻¹^d by have := T.positive i; positivity)).le
lemma ceiling (d k:ℕ) (hd:k>d)(C:ℝ):∀ᶠ i in atTop,C*((T.gap i)⁻¹)^d ≤ ((T.gap i)⁻¹)^k:=by
 let f i:=(T.gap i)⁻¹
 have h : Tendsto f atTop atTop:=tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨T.cutoff, Eventually.of_forall T.positive⟩)
 obtain ⟨q,hq⟩:=Nat.exists_eq_add_of_le hd.le
 have hx:= tendsto_pow_atTop (α:=ℝ) (show q≠0 by omega)
 filter_upwards [(hx.comp h).eventually (eventually_ge_atTop C)] with i hi
 rw [hq,pow_add,mul_comm C]; exact mul_le_mul_of_nonneg_left hi (show 0≤ f i^d by unfold f; have := T.positive i; positivity)
lemma hugeWalk (d:ℕ)(C r:ℝ)(hC:C>0) :∀ᶠ i in atTop,r*canter T d i < C*(T.period i).val:=by
 let p:=max r 1
 have hP:p>0:=zero_lt_one.trans_le (le_max_right ..)
 filter_upwards [T.cutoff.eventually (gt_mem_nhds zero_lt_one), (T.huge d).eventually (eventually_gt_atTop (2*p/C))] with i hh ht
 let a:=T.gap i; have hp:0<a:= T.positive i; let k:=canter T d i; let N:= (T.period i).val
 have hv: (k:ℝ) ≤ 2*(a⁻¹^d):=by
   have hf:=high T d i
   have hz:1≤ a⁻¹^d:=one_le_pow₀ (one_le_inv_iff₀.mpr ⟨hp,hh.le⟩); linarith only [hf,hz]
 apply lt_of_le_of_lt (mul_le_mul (show r ≤ p from le_max_left ..) hv (Nat.cast_nonneg k) hP.le)
 have hr := (div_lt_iff₀ hC).mp ht
 rw [inv_pow,←mul_assoc p,← div_eq_mul_inv, div_lt_iff₀ (pow_pos hp _)]; linarith only [hr]
omit T in
lemma hearth (o:Site N)(k:ℕ)(i j:Axis)(hk: 2*k < N.val)(hp: 2*k+2< pdist (o+o))(F: Site N→ℝ) (H:∀ x,F (mirror i j x)=F x):
 (∑ x:Site N,F x)= 2*(∑ a∈box k,F (wrap N a+o))+(∑ x : Site N with k< orbitRank N o i j x,F x):=by
 classical
 let B:=(box k); let f (a:Cover):=wrap N a+o; let S:= B.image f; let K:=mirror (N:=N) i j; let U:=S.image K
 have hu(a:Site N):pdist (a-o)≤k ↔ a∈ S:=by
   constructor
   · intro ha; refine Finset.mem_image.mpr ⟨lift (a-o), wrapcost _ ((Eq.symm (diam_lift ..)) ▸ ha),?_⟩; unfold f; rw [wrap_lift, sub_add_cancel]
   rintro hw; obtain ⟨b,hb,rfl⟩:= Finset.mem_image.mp hw; simpa only [f,add_sub_cancel_right] using (show pdist (wrap N b)≤k from Work.E01.pdist_wrap_le hb)
 have hv(a:Site N):orbitRank N o i j a≤k ↔ a∈ S∪U:=by
   unfold orbitRank; rw [min_le_iff,hu,hu, Finset.mem_union]; apply or_congr Iff.rfl
   constructor
   · intro ha; apply Finset.mem_image.mpr ⟨K a,ha,mirror_inv i j a⟩
   intro ha; obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp ha; rw [show mirror i j (K b)=b from mirror_inv i j b]; exact hb
 have hi : Disjoint S U:=Finset.disjoint_left.mpr (by
   intro a ha he
   obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp he
   replace ha:=(hu _).mpr ha; replace hb:=(hu _).mpr hb
   let u:= K b-o; let v:= b-o
   have hx:pdist (o+o)≤k+k+1+1:=by
     rw [show o+o=-(u+v+step i+step j) from by unfold u K v mirror; abel,pdist_neg]
     have he₁:=pdist_triangle u v; have he₂:=pdist_triangle (u+v) (step i); have he₃:=pdist_triangle (u+v+step i) (step j)
     change pdist u ≤ k at ha; change pdist v ≤ k at hb
     have hs : pdist (step i:Site N)≤1:=stepP i; have hs' : pdist (step j:Site N)≤1:=stepP j;omega
   omega)
 have hf:Set.InjOn f B:=by
   intro a ha b hb h
   have hu (w:Cover)(hw:w∈B) : lift (wrap N w)=w:= lift_eq_iff.mpr ⟨rfl,fun i=> by have h1:=(box_test.mp hw).1 i; have h2:=(box_test.mp hw).2 i;omega⟩
   rw [← hu a ha, ← hu b hb,add_right_cancel h]
 calc _ = (∑ x∈S∪U,F x) + ∑ x∈Finset.univ \ (S∪U),F x:= Eq.symm (Finset.sum_add_sum_compl ..)
      _ = _:=by
        rw [show Finset.univ \(S∪U)=Finset.univ.filter (fun x: Site N=> k<orbitRank N o i j x) from Finset.ext fun x=>by simp only [Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ, true_and,← hv x,not_le], Finset.sum_union hi, show (∑ x∈U,F x) = ∑ x∈S,F x by unfold U; rw [Finset.sum_image (mirror_inv i j (N:=N) |>.injective.injOn (s:=S))]; exact Finset.sum_congr rfl fun x _=>H x]
        unfold S; rw [Finset.sum_image hf,two_mul]
end YM.SchemeRG11.Acorn
