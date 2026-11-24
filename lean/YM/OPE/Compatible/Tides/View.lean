import YM.OPE.Compatible.Tides.Local
/-!
# Winding annulus price
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open Pert.Full (incVec)
open Next.Rank.Radian
open scoped BigOperators Classical ContDiff
variable {s:ℝ}{f:Cover→ℝ}{F:E4→ℝ}
def anise (s:ℝ)(n:Side)(f:Cover→ℝ):ℝ:=∑' p:Cover, annA s (addr n p)*f p
private lemma stalk(n:Side)(x:Cover): mark n (addr n x)=x:=by
   funext i; unfold mark; rw [Pert.Band.reads_wrap,show (↑(x i) / (n.val:ℝ)) / (n.val:ℝ)⁻¹=(x i:ℝ) from by field_simp]; simp
lemma gridX (n:Side)(p): addr n p=incVec (dew n) p:=rfl
lemma cutdown (t:ℝ)(x:E4): ‖cutA t x‖≤1:=by rw [Real.norm_of_nonneg (show 0 ≤ cutA t _ from Pert.Band.disk.nonneg)]; exact Pert.Band.disk.le_one
lemma straight (h:Quip 4 f F):∃ C≥0,∀ x,‖f x‖ ≤ C/(notch x:ℝ)^ (4:ℕ):=by
    obtain ⟨C,hC,hp⟩:=Quip_cash h; refine ⟨C,hC,fun x=>?_⟩; apply le_trans (hp x) (le_of_eq ?_); rw [div_eq_mul_inv,zpow_neg,zpow_ofNat]
lemma turn_view (hs:0<s)(n:ℕ→Side)(hc:Tendsto (fun i=>(n i).val) atTop atTop)(h:Quip 4 f F): Tendsto (fun i=>anise s (n i) f) atTop (𝓝 (fineI s F)):=by
   let S:=annA s; let p(i:ℕ)(x:E4):= mark (n i) x; let f'(i:ℕ)(a:Cover):= quilting 4 f (n i) a; let z(i:ℕ)(a:Cover):= addr (n i) a; let G(i:ℕ)(x:E4):ℂ:=↑(S (z i (p i x))*f' i (p i x):ℝ)
   obtain ⟨m,hm⟩:∃ m:ℕ, max 1 s⁻¹ +4 < (m:ℝ):=exists_nat_gt _
   have ht(x:E4)(hv:max 1 s⁻¹ ≤ ‖x‖): S x=0:=by unfold S annA; rw [Pi.sub_apply,romp hs (le_trans (le_max_right ..) hv), romp (s:=1) zero_lt_one (by rw [inv_one]; exact le_trans (le_max_left ..) hv),sub_self]
   have hr(n:Side)(x:E4): ‖x‖ ≤ ‖addr n (mark n x)‖+4:=by
       let y:= addr n (mark n x); have hu: ‖x‖ ≤ ‖x-y‖+‖y‖:=by simpa only [sub_add_cancel] using norm_add_le (x-y) y
       rw [← dist_eq_norm,dist_comm] at hu; have hx:=rock (c:=n) x; change _≤ ‖y‖+_; have hv:((n.val:ℝ))⁻¹≤1:=inv_le_one_of_one_le₀ (by exact_mod_cast n.pos); linarith only [hu,hx,hv]
   have H (i):eventP m (G i):=fun x hx=> by unfold G; rw [ht]; simp; have hv:= hr (n i) x; linarith only [hv,hm,hx]
   obtain ⟨ε,hε,hv⟩:= (Metric.mem_nhds_iff).1 (coldA (s:=s)) -- type-set
   obtain ⟨C,hC,hq⟩:= straight h
   let Q:= 2*C/(ε/2)^ (4:ℕ)
   have hp(i)(x):‖G i x‖ ≤ Q:=by
       unfold G; rw [Complex.norm_real,norm_mul]; let a:=p i x
       by_cases hZ:S (z i a)=0
       · rw [show S (z i (p i x))=0 from hZ,norm_zero,zero_mul]; dsimp [Q]; positivity
       let t:=dew (n i); have ht:=dew_pos (n i); have hw:t/1=t:= div_one t
       have hb:ε ≤ ‖z i a‖ := le_of_not_gt fun hy=> hZ <| hv (show dist _ (0:E4)< ε from by rwa [dist_zero_right])
       have he:=twice_bead a _ ht.le; rw [← gridX] at he;
       have hy:(ε/2)^ (4:ℕ) ≤ ((notch a:ℝ))^4*t^4:=by
           rw [←mul_pow]; apply pow_le_pow_left₀ (by linarith only [hε]) _; have hy: size a ≤ notch a:=Nat.le_add_left ..; have he₀: (size a:ℝ)*t ≤ (notch a:ℝ)*t:= mul_le_mul_of_nonneg_right (by exact_mod_cast hy) ht.le; linarith only [he,hb,he₀]
       have hu:‖S (z i a)‖ ≤ 2:= le_trans (norm_sub_le ..) (le_trans (add_le_add (cutdown s _) (cutdown 1 _)) (le_of_eq (by ring))) -- annot
       have ht': ‖f' i a‖ ≤ C/(ε/2)^ (4:ℕ):=by
           apply le_trans _ (div_le_div_of_nonneg_left hC (by positivity) hy); dsimp only [f']; rw [quilting,zpow_neg,zpow_ofNat,norm_mul,Real.norm_of_nonneg (by positivity)]; apply le_trans (mul_le_mul_of_nonneg_left (hq a) (by positivity)) (le_of_eq ?_); unfold t; rw [inv_mul_eq_div,div_div]
       change ‖S (z i a)‖ * ‖f' i a‖≤ Q; unfold Q; rw [mul_div_assoc]; grw [hu,ht']
   have hT:=Pert.Band.moving_grid n hc m (F:=G) (g:=fun x=>((S x*F x : ℝ):ℂ)) (.of_forall H) ⟨Q,(show 0 ≤ Q from norm_nonneg _ |>.trans (hp 0 0)),.of_forall hp⟩ (fun y q hq=>?_); rotate_left -- have _ ordering
   · let A(i):=z i (p i (q i)); have he':Tendsto (fun i=>( (n i).val:ℝ)⁻¹) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hc); have hx:Tendsto A atTop (𝓝 y):=by
          have he:Tendsto (fun i=>dist (A i) (q i)) atTop (𝓝 0):=by simpa only[mul_zero] using! squeeze_zero (fun _=>dist_nonneg) (fun i=>rock (c:=n i) (q i)) (show Tendsto (fun i=>_) _ _ from (by simpa only[mul_zero] using! (he'.const_mul 4)))
          -- triangular
          rw [Metric.tendsto_nhds]; intro r hr; have hp:0<r/2:=by positivity
          filter_upwards [he.eventually (gt_mem_nhds hp),Metric.tendsto_nhds.mp hq _ hp] with i hi hi'; apply lt_of_le_of_lt (dist_triangle _ (q i) _); linarith only [hi,hi']
     by_cases h0:y=0
     · subst y; rw [show S 0=0 from coldA.self_of_nhds,zero_mul]; apply Tendsto.congr' _ tendsto_const_nhds; filter_upwards [hx.eventually coldA] with i hi; exact (show G i (q i)=_ from congrArg Complex.ofReal (mul_eq_zero_of_left (show S (A i)=0 from hi) _)).symm
     have he:= h n (fun i=>p i (q i)) hc y h0 (show Tendsto A _ _ from hx); exact Complex.continuous_ofReal.continuousAt.tendsto.comp ((((ann_ray s).continuous.continuousAt.tendsto.comp hx).mul he)) -- change
   rw [integral_complex_ofReal] at hT
   have hy:= Complex.continuous_re.continuousAt.tendsto.comp hT; refine Filter.Tendsto.congr ?_ hy; intro i
   change Complex.re (scansP (n i) (G i) m)= _; unfold scansP anise; rw [Complex.smul_re,Complex.re_sum,tsum_eq_sum (s:=room (n i) m)]; swap
   · intro b hb; change S _*_=0; rw [ht (addr (n i) b),zero_mul]; apply le_trans _ (show (m:ℝ) ≤ ‖addr (n i) b‖ from le_of_not_ge fun he=>hb (addressBW _ _ he)); linarith
   rw [smul_eq_mul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro a ha; dsimp only [G,p]; rw [stalk,Complex.ofReal_re]; unfold f' quilting; dsimp only [z,S]; rw [zpow_neg,zpow_ofNat]; unfold dew sizeR; field_simp
end YM.OPE.Balsam
