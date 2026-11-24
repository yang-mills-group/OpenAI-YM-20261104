import YM.X.Charting.Heap
/-!
Wick contractions at finite inversion orbit horizon agree to all orders in volume estimates at degree one in bare series. Along joint placements departing at polynomial native distance. Includes estimate for pushed leading counterterm differences.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Hinge
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Next.Rank Normal MvPolynomial Finsupp
open Feyn Gauge LatticePT PertExtension.Orb Chart Stems PertExtension.Series.Tested Finset Interval Size Asymptotics
open Pert.Orb (positiveLinks wilson Potential)
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {n:Side} {q:ℕ+}(hq:1<q.val)
local notation "K"=> (atTop:Filter ℕ)
variable {α β V:Type*}
variable (A:α→Beam q)(v:Beam q)(p : PlaqAxes)(P:poly (α×Hair G))(hw:Away v (-v))(h:∀ i,Near v (A i))(d:ℕ)

def rimX (k): Finset (Native q k):= (heap d v p false k)ᶜ
lemma rimX_spec (k:ℕ)(z): z∈rimX v p d k ↔ ticketN (v k) z≤ border q d k:= by simp [rimX,Hinge.heap,minmass]
lemma rimX_near (z:Beam q)(hz: ∀ᶠ k in K,z k∈rimX v p d k): Near v z:= by
   refine ⟨d,Ripe.eventual (B:=1) ?_⟩; filter_upwards [hz] with k hk; rw [raysD,Real.norm_of_nonneg (by positivity),one_mul,at_border];exact Nat.cast_le.mpr ((show _≤ticketN _ _ from Nat.le_succ _).trans ((rimX_spec ..).1 hk))
lemma rimX_cost : Charged q (fun k=>(↑(rimX v p d k).card:ℝ)):= by
    let k(i):= border q d i; refine ⟨(d*4:ℕ),Ripe.eventual (B:=3^4) ?_⟩; apply Eventually.of_forall; intro i; rw [Real.norm_of_nonneg (by positivity),ticket_nat, pow_mul,← cost_border]; let x:= k i; have hh : rimX v p d i⊆ rim (v i) x:=fun z hz=> (rim_spec ..).mpr ((show _≤ticketN _ _ from Nat.le_succ _).trans ((rimX_spec ..).1 hz))
    apply (Nat.cast_le.mpr ((Finset.card_le_card hh).trans (rim_count _ _))).trans; push_cast; rw [← mul_pow]; gcongr; change (x:ℝ)+x+1≤ 3*x; have hx:=(show (1:ℝ) ≤ x from Nat.one_le_cast.mpr (border_pos ..)); linarith

include hq hw
lemma peel_eyes : ∀ᶠ k in K, Disjoint (rimX v p d k) ((rimX v p d k).image (second p)):= by
   let f (i):= ((side q i).val:ℝ)⁻¹; let W (i):= (border q d i:ℝ); obtain ⟨c,hc,H⟩:=hw
   have hw' : Vanished q (fun i=>(W i)*f i) := Vanished.right (g:=f) ⟨(d:ℤ), by simpa only [Ripe,W, funext (at_border q d)|>.symm] using! isBigO_refl (ticket q (d:ℤ)) K ⟩ (Vanished.side_small hq) -- repair
   have hw(i:ℕ)(x:Native q i) : separation (-x) (second p x) ≤2:= by unfold second separation; rw [show -x - (-x-step p.val.1-step p.val.2)=step p.val.1+step p.val.2 by abel]; exact le_trans (pdist_triangle ..) (Nat.add_le_add (pdist_step _) (pdist_step _))
   filter_upwards [ ((hw'.goes hq).eventually (gt_mem_nhds (show 0<c/4 from by linarith))), H] with k hk hK; let D:=(side q k).val; have hv : (0:ℝ)<D:= by unfold D; positivity
   refine Finset.disjoint_left.mpr (fun x hx ht=>?_); obtain ⟨y,hy,rfl⟩:= mem_image.mp ht
   replace hx:= (rimX_spec ..).1 hx; replace hy:= (rimX_spec ..).1 hy
   have he : separation (v k) (-v k)< 4*border q d k:= by
     have he:=separation_triangle (v k) (second p y) (-v k); have ht:= separation_triangle (second p y) (-y) (-v k)
     have h2 : separation (-y) (-(v k))=separation (v k) y:= by simp [separation, sub_neg_eq_add, sub_eq_add_neg,add_comm]
     have hf := hw k y; rw [separation_comm (second p y) (-y), h2] at ht; unfold ticketN at *; have hL := border_pos q d k; omega
   change c* (D:ℝ)≤(separation (v k) (-(v k)):ℝ) at hK
   have hh := hK.trans_lt (show (separation (v k) (-v k):ℝ) < 4 * W k by unfold W; exact_mod_cast he)
   change W k/(D:ℝ)<_ at hk; rw [div_lt_iff₀ hv] at hk; linarith

lemma eyes (k:ℕ): (heap d v p true k)ᶜ=rimX v p d k ∪ (rimX v p d k).image (second p):= by
    ext x; rw [Finset.mem_compl, Finset.mem_union, Finset.mem_image,rimX_spec]; unfold heap; simp only [Finset.mem_filter,rimX_spec, Finset.mem_univ,true_and,minmass, if_true,not_lt,min_le_iff]; apply or_congr_right; constructor
    · intro h; exact ⟨_,h, second₂ p _⟩
    rintro ⟨y,hy,rfl⟩; rw [second₂];exact hy

section blend
include h
lemma stepUV : Vanished q (fun k=> mean (rename (stageAt (fun i=> A i k)) P)-shock sale (rename (stageAt (fun i=> A i k)) P)):= by
   change Vanished q (fun k=> shock water _-shock sale _); simp_rw [← remaps]; apply blendsOf
   · intro i j; simp_rw [remap_cov]; exact buoy hq true _ _
   · intro i j; simp_rw [remap_cov]; exact buoy hq false _ _
   intro i j; simp_rw [remap_cov]; exact minus_fee hq (A i.1) (A j.1) _ _ hw (h _) (h _) -- remap_cov
lemma stepV (z:Beam q)(hz:Near v z) (f:Curly G): Vanished q (fun k=> fees (fun i=> A i k) water P f (z k)-fees (fun i=>A i k) sale P f (z k)) := by
    unfold fees; simp_rw [← align (fun i=>A i _)]; apply blendsOf
    · intro i j; simp_rw [alignment,remap_cov]; exact buoy hq true _ _
    · intro i j; simp_rw [alignment,remap_cov]; exact buoy hq false _ _
    rintro (i|i) (j|j); all_goals (simp_rw [alignment,remap_cov]; first| exact minus_fee hq (A i.1) (A j.1) _ _ hw (h _) (h _)| exact minus_fee hq z (A j.1) i _ hw hz (h _)|exact minus_fee hq (A i.1) z _ j hw (h _) hz|exact minus_fee hq z z i j hw hz hz)
lemma localPay : Vanished q (fun k=> ∑ x∈rimX v p d k,(summate A p true P k x-summate A p false P k x)) := by
    let s (k):= rimX v p d k; have hs (k:ℕ): (s k).Nonempty:= ⟨v k, (rimX_spec ..).2 (by simp only [ticketN, separation_self,zero_add]; exact border_pos ..)⟩
    let f(k)(x:Native q k):= summate A p true P k x-summate A p false P k x; choose z hz hZ using fun k=> Finset.exists_max_image (s k) (fun z=>‖f k z‖) (hs k)
    have H:Vanished q (fun k=> f k (z k)):= stepV hq A v P hw h z (rimX_near v p d z (Eventually.of_forall hz)) (vertex p)
    have hCost : Vanished q (fun k=>(s k).card*‖f k (z k)‖) := Vanished.right (rimX_cost v p d) (fun i=>(H i).norm_left)
    apply Vanished.previous (IsBigO.of_norm_eventuallyLE _) hCost; apply Eventually.of_forall; intro k; change ‖∑ x∈s k, f k x‖≤ _; exact (norm_sum_le ..).trans ((Finset.sum_le_sum (hZ k)).trans_eq (by rw [Finset.sum_const,nsmul_eq_mul]))
variable [Finite α] -- needed common H From formula

def foot (a:Bool)(i:ℕ):=∑ y:Native q i, summate A p a P i y
lemma dissent : Vanished q (fun k=> foot A p P true k-2*foot A p P false k) := by
   apply Vanished.all; intro j; obtain ⟨d,H,hD,hJ⟩:= ((eventually_all.mpr fun u=> near_capt hq (h u)).and ((eventually_gt_atTop 0).and (eventually_ge_atTop j))).exists
   let s (k):= rimX v p d k; let f a(k):=summate A p a P k; let x a:=foot A p P a; let p' a:=separated A v d p a P; let u:= x true- (fun k=>2*x false k); let Q(k):ℂ:= ∑ i∈s k,(f true k i-f false k i)
   have Hs a:Ripe q (p' a) (- (j:ℤ)):= Ripe.enlarge (fit_high hq A v d hD p a P H ) (by omega) -- fill
   have hg:Ripe q (p' true - (2:ℂ) • p' false + (2:ℂ) • Q) (- (j:ℤ)):= ((Hs true).sub ((Hs false).const_smul_left _)).add (supreme (2:ℂ) (localPay hq A v p P hw h d) (- (j:ℤ))) -- order check
   refine (hg.congr' ?_ (EventuallyEq.refl ..) : Ripe q u (- (j:ℤ)))
   filter_upwards [peel_eyes hq v p hw d] with k hk; let S a:=heap d v p a k
   have ht (a:Bool): x a k = p' a k +∑ i∈ (S a)ᶜ, f a k i:= Eq.symm (sum_add_sum_compl ..)
   have hi : ∑ i∈ (S true)ᶜ, f true k i=2*(∑ i∈s k,f true k i):= by
        change ∑ i∈ (heap d v p true k)ᶜ, f true k i=_; rw [eyes hq v p hw d,Finset.sum_union hk,Finset.sum_image,two_mul]; · exact congr_arg (_+·) (Finset.sum_congr rfl (fun i _=> show f true k (second p i)= f true k i from faces p i _))
        intro i _ j _ hi; exact (Function.LeftInverse.injective (second₂ p)) hi
   change p' true k-(2:ℂ)*p' false k+(2:ℂ)*Q k=x true k-2*x false k; rw [ht,ht,hi]; unfold Q; rw [Finset.sum_sub_distrib]; change _ = _-2*(p' false k+ ∑ i∈s k,f false k i); ring
end blend
end YM.PositionX.Hinge
