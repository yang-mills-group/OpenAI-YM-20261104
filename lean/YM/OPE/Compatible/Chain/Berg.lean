import YM.OPE.Compatible.Chain.Dew
/-!
# summing up native mantles. Prices in KP regulators
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset Metric
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP GaussianScore Work.F06
local notation "M" => TypeFace 1
variable {C:KernelChoices}{r:ℕ}
lemma stall (q:Site n): pdist q ≤ n.val∧ (pdist q=0↔q=0):=by
   constructor
   · apply Finset.sup_le;intro i _; have he:=lift_centers q i;omega
   constructor
   · intro e; have hh: lift q=0:=by funext i; have h:=component_le q i; change lift q i=0; omega
     rw [← wrap_lift q,hh,map_zero]
   rintro rfl;simp [pdist,lift]
lemma plunge (k:ℕ): (box k).card=(2*k+1)^4:=by
      rw [show box k= Fintype.piFinset (fun _ : Axis=> Lattice.layers k) from Finset.ext fun x=>by rw [box_iff_layers, Fintype.mem_piFinset],Fintype.card_piFinset]; simp [card_layers]
lemma mantel (k:ℕ): ((@univ (Site n) _).filter (fun x:Site n=>pdist x=k+1)).card ≤ 512*(k+1)^3:=by
     let S:Finset (Site n):= univ.filter fun x:Site n=> pdist x=k+1; let C:= box (k+1) \ box k
     have hv(m:ℕ)(x:Site n): lift x∈box m ↔ pdist x ≤ m:=by
          rw [box_test,pdist,Finset.sup_le_iff]; constructor
          · rintro ⟨h,hx⟩ i -; specialize h i; specialize hx i; omega
          intro h; simp only [mem_univ,true_implies] at h; constructor<;>intro i<;> specialize h i <;> omega
     have he:S.image lift ⊆ C:=by intro y h; obtain ⟨x,hhq,rfl⟩:= mem_image.mp h; have hh: pdist x=k+1:= (mem_filter.mp hhq).2; simp [C,hv,hh]
     have hp(m:ℕ) : box m ⊆ box (m+1):=by
          intro y h; rw [box_test] at h ⊢; obtain ⟨hx,h⟩:=h; constructor; · intro i; specialize hx i;omega
          intro i; specialize h i;omega
     rw [show (univ.filter _)=S from rfl,← card_image_of_injective S (show Injective (lift (n:=n)) from fun x y h=> by rw [← wrap_lift x,← wrap_lift y,h])]
     refine (card_le_card he).trans ?_; rw [show C.card=_ from card_sdiff_of_subset (hp k), plunge,plunge,tsub_le_iff_right]; ring_nf;nlinarith only [show 0≤k from Nat.zero_le _] -- tSub?
lemma mantle_bill {k:ℕ}(h:1≤ k)(hr:k≤3): ∃ C:ℝ,0≤ C ∧ ∀ n:Side,(∑ p:Site n,(win p)^(- (k:ℤ))) ≤ C *(n.val:ℝ)^4:=by
      let a:ℝ:= 2*Real.pi; have ha:0<a:=mul_pos (by norm_num) Real.pi_pos
      let D:=512/(a^k); have hd:0≤D:= div_nonneg (by positivity) (pow_nonneg ha.le _)
      refine ⟨D,hd,fun n=>?_⟩; let f(p:Site n) := (win p)^(- (k:ℤ))
      let l:=leap n; let v:ℝ:=n.val; have hz:0<v:=side_pos _; have hl:= leap_pos n
      let g(m):=∑ p∈ univ.filter (fun p:Site n=> pdist p=m), f p
      have he(x:ℕ)(hx:x∈range n.val): g (x+1) ≤ D*v^3:=by
           let S:= univ.filter (fun p:Site n=>pdist p=x+1); let u:ℝ:=((x+1:ℕ):ℝ); have hu:0<u:=by unfold u; positivity
           have hs: (S.card:ℝ)≤512*u^3:=by unfold S u;exact_mod_cast mantel (n:=n) x
           have ht(p:Site n)(hp:p∈S): f p ≤ (l*u) ^ (-(k:ℤ)):=by
                have hhQ:pdist p=x+1:=(mem_filter.mp hp).2; have hv:l*u≤win p:= (by unfold u; rw [← hhQ]; exact win_gap p); unfold f; rw [_root_.zpow_neg,_root_.zpow_neg,zpow_natCast,zpow_natCast]; exact inv_anti₀ (pow_pos (mul_pos hl hu) _) (pow_le_pow_left₀ (mul_pos hl hu).le hv _)
           calc
               g (x+1) ≤ (∑ p ∈ S,(l*u)^(- (k:ℤ))):=sum_le_sum ht
               _ = (S.card:ℝ)*(l*u)^(- (k:ℤ)):=by simp
               _ ≤ 512*u^3*(l*u)^(- (k:ℤ)):=mul_le_mul_of_nonneg_right hs (by positivity)
               _ = D*v^k*(u^(3-k)):=by
                     rw [show l=a/v from rfl, _root_.zpow_neg,zpow_natCast]; unfold D
                     rw (occs:=.pos [1]) [show u^3=u^k*u^(3-k) from by rw [←pow_add]; congr 1;omega]; field_simp; ring_nf; rw [mul_assoc _ (v^k),← mul_pow v, mul_inv_cancel₀ hz.ne',one_pow,mul_one]
               _ ≤ D*v^k*v^(3-k):=by gcongr; unfold u v; exact_mod_cast (show x+1 ≤ n.val from mem_range.mp hx)
               _ = D*v^3:= by rw [mul_assoc, ← pow_add]; rw [show k+(3-k)=3 from by omega]
      change (∑ p:Site n,f p)≤D*v^4; rw [← sum_fiberwise_of_maps_to (show Set.MapsTo pdist _ ((range (n.val+1)):Set _) from fun i _=> mem_range.mpr (Nat.lt_succ_of_le (stall i).1)) f] -- f:= name?
      change ∑ i∈ range (n.val+1),g i ≤ _; rw [sum_range_succ',show g 0=0 from ?_,add_zero]
      · apply (sum_le_sum he).trans; simp [v]; ring_nf; exact le_rfl
      refine sum_eq_zero fun i hi=>?_ ; have ht: i=0:= (stall i).2.mp (mem_filter.mp hi).2
      unfold f; simp [ht,win,lit,lift, _root_.zpow_neg, rcast,show k≠0 by omega,hl.ne']; rfl
end YM.OPE.Cascade.Terp
