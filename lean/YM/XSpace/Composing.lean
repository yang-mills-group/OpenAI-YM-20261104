import YM.XSpace.Coffers
/-!
# Symbolic triangle price levels
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Graph3
open Function Set Filter Lattice Trace Chart2 Maxwell Maxwell.Free Foundation Shade JetGauge Outline MvPolynomial Structure1 Chiral Finsupp Mu Normalize Next.Rank.Normal Stall Pages Furlough Contraction
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge}(W:Initialize G)(g:G.Simple) (c:Shade.Cut)(a:ℝ)(z x y:Cover)
local notation "A" => b_w W z
local notation "L" => u_w W x
local notation "M" => u_w W y
local notation "K" => base a
lemma excludes (q:PlaqAxes): Summable (fun i:Cover=> F3 (Vb W z (i,q)) L M):=by
  have he := Structure1.sums W 1 (trip z x y) q (token G); simp_rw [canon] at he; simpa [base] using he
lemma rfs (p:HP G 6) : Trace.volume z (σP W c a p) ∈ DegZ (UnitIndex G) 3:= by unfold Trace.volume σP; apply name_charge; rw [rf,LinearMap.comp_apply]; exact P0_cap W (repair W c 6 a p)
include g in
lemma red_lights : F3 A (versus W c a x (Ufield G)) M=F3 A (u_1 W x) M:=by
  apply sub_eq_zero.mp; rw [f3_last A (versus ..), f3_last A (u_1 ..),F3,F3,← clasp,← clasp,← map_sub,← map_sub,clasp]; apply Eq.trans _ (lower2 W g z y (versus W c a x (Ufield G)-u_1 W x) ?_); apply f3_last
  unfold versus; rw [sub_right_comm]; exact Submodule.sub_mem _ (allowsU ..) (name_charge (P0_cap W (repair W c 4 a (Ufield G))) _)
lemma red_beam : upper W g x y (versus W c a z (Bfield G)) = upper W g x y (b_1 W z) :=by apply sub_eq_zero.mp; rw [← map_sub]; unfold versus; rw [sub_right_comm]; exact slaughter W g x y _ (Submodule.sub_mem _ (allowsB ..) (rfs W c a z (Bfield G)))
def tribute := Trace.volume z (compensate W c 6 a (Bfield G))
lemma halves (v: PlaqAxes)(w:Cover): Vb W z (z+w,v)= Trace.volume z (Uptown.spirit (W.surveys 6) (Bfield G) v w):=by unfold Vb Uptown.spirit; rw [← Mu.bring,show V3 G (z+w,v)=Trace.volume z (V3 G (w,v)) from by rw [encoded w,encoded (z+w),stroll]]; rfl -- rw direction?
lemma tribute_work (T:Module.Dual ℂ (Stamp G)): T (tribute W c a z) = T (versus W c a z (Bfield G)) - ∑ v:PlaqAxes,∑' i: Cover,pace c a (i-z)*T (Vb W z (i,v)):=by
  let p(v):=Shade.measure c a (Uptown.spirit (W.surveys 6) (Bfield G) v); have he(v): T (Trace.volume z (p v))=∑' i:Cover, pace c a (i-z)*T (Vb W z (i,v)):=by
    rw [← Equiv.tsum_eq (Equiv.addLeft z)]; simp_rw [Equiv.coe_addLeft, halves,add_sub_cancel_left]; unfold p; rw [tsum_eq_sum (s:=(outfit c a).support), quick_sum,map_sum,map_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,map_smul];rfl
    intro b hb; rw [← outfit_eq,Finsupp.notMem_support_iff.mp hb,zero_mul]
  change T (Trace.volume z (Prelude.fuse (W.surveys 6) (Bfield G) c a-σP W c a (Bfield G)))=_; rw [Uptown.drama];
  unfold versus stars; simp only [_root_.map_sub,_root_.map_sum]; change _ -(∑ i,T (Trace.volume z (p i))) -_=_; simp_rw [he]; abel
lemma V_votes (v:Face ℤ): Pages.Hom (V3 G v) 3:= by
  suffices throne G 3 4 ≤ rank 3 _ from this (stationed v); unfold throne; apply Submodule.span_le.mpr; intro p hp; obtain ⟨l,h,rfl⟩:= hp; change story l ∈ rank 3 _; rw [← show l.length=3 from h.1]; apply words
where words (l:Mu.Word G):Pages.Hom (story l) l.length:=by induction l with | nil=> exact isWeightedHomogeneous_one ..| cons i l IH=> rw [List.length_cons,add_comm,read_word]; exact (strongs _).mul IH

def supply := ups W g z x y + ups W g z y x

def mainPlay := playAll W g z x y (station W g z x y)+ playAll W g z y x (station W g z y x)
abbrev fund (P:Face ℤ):= bottom W g x y (Vb W z P)
abbrev outer (P:Face ℤ):= (1-pace c a (P.1-z))*fund W g z x y P
def mainQ (P:Face ℤ):= playAll W g z x y (internal W g z x y (V3 G P))
def state (P: Face ℤ):= outer W g c a z x y P+mainQ W g z x y P
lemma vote_adv (P:Face ℤ):state W g c a z x y P= F3 (Vb W z P) L M-pace c a (P.1-z)*fund W g z x y P:=by rw [state,outer,mainQ,color_mix W g,fund,← wall W g _ _ _ (V3 G P) (V_votes P)]; ring -- defeq
lemma fusion_adv (q:PlaqAxes): Summable fun i:Cover=> pace c a (i-z)*fund W g z x y (i,q):=by
  apply (Equiv.addRight z).summable_iff.mp; apply summable_of_ne_finset_zero (s:=(outfit c a).support); intro i hi; unfold Function.comp; rw [Equiv.coe_addRight]; dsimp only; rw [add_sub_cancel_right,← outfit_eq, Finsupp.notMem_support_iff.mp hi,zero_mul]
lemma voice_adv (q:PlaqAxes): Summable fun i:Cover=> state W g c a z x y (i,q):=by simp_rw [ vote_adv]; exact Summable.sub (excludes W z x y q) (fusion_adv ..)
def receipt := K^14* (upper W g x y (b_1 W z) + bottom W g x y (tribute W c a z) + supply W g z x y + mainPlay W g z x y -∑ q:PlaqAxes, ∑' i:Cover,state W g c a z x y (i,q))
lemma costing (ha:0<a): adequate W (Structure1.ready W c a 6) a (trip z x y) (token G) = receipt W g c a z x y:=by
  rw [adequate,replied,_root_.sub_apply,_root_.sub_apply,sub_right_comm]; change shifts W c a (trip z x y) (token G)-(∑ q:PlaqAxes,integralPart W a (trip z x y) 6 q) (token G)=_
  rw [pillars _ _ _ _ _ _ ha,_root_.sum_apply]; unfold integralPart; simp only [MultilinearMap.mk'_apply, canon, tsum_mul_left,← Finset.mul_sum]; rw [receipt,← mul_sub]; apply congr_arg; simp_rw [vote_adv]; unfold spell supply mainPlay
  have ht(q:PlaqAxes):=(excludes W z x y q).tsum_sub (fusion_adv W g c a z x y q); simp_rw [ht]; rw [Finset.sum_sub_distrib,color_mix W g x y (versus ..), red_beam, red_lights W g c a z x y, f3_last A L,red_lights W g c a z y x, completionU W g, completionU W g, tribute_work]; unfold fund; abel
end YM.XSpace.Graph3
