import YM.SchemeConversionRG11.FirstW.Trice.Bridge
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open scoped Topology ContDiff BigOperators Classical
variable {T:Itinerary}{c:ℕ→Side}{n:Side}{G:Gauge}{x:Nodes}{W:Wash}{R ρ r :ℝ}
private lemma symP (A:Sky G (Per n))(u v w:FullT G n)(hx:∀ a b c,A a b c=A b a c)(hv:∀ a b c,A a b c=A a c b): 6 * A u v w=A (u+v+w) (u+v+w) (u+v+w)-A (u+v) (u+v) (u+v)-A (u+w) (u+w) (u+w)-A (v+w) (v+w) (v+w)+A u u u + A v v v + A w w w:=by
 simp only [map_add,LinearMap.add_apply]; rw [show A v u w=A u v w from hx ..,show A v w u=A u v w from (hv ..).trans (hx ..),show A w u v=A u v w from (hx ..).trans (hv ..), show A u w v=A u v w from hv ..,show A w v u=A u v w from (hv ..).trans ((hx ..).trans (hv ..))]; ring
private lemma sided (A B C : FullT G n) : lapSky G n A B C=8*(∑ x, ∑ i:Axis,∑ j:Axis, if i< j then tower G x (Lattice.square i j) A B C else 0) := by
 have ht(x y:Site n)(i j:Walk)(e:∀ a:FullT G n, tower G x i a a a=tower G y j a a a): tower G x i A B C=tower G y j A B C:= by
   have hv(x:Site n)(i:Walk) := symP (tower G x i) A B C (fun a b c=> tower_sym ..) (fun a b c=>tower_cross ..); apply mul_left_cancel₀ (show (6:ℝ)≠0 by norm_num); rw [hv,hv];simp_rw [e]
 rw [lap_shield]; apply wheel_rate
 · intro x i j; apply ht; intro a; simp_rw [peaks]; simp_rw [swipe_swap _ x i j]
 · intro x i j; apply ht; intro a; simp_rw [peaks]; simp_rw [swipe_flip _ x i j]
 intro x i; rw [tower_eq]; simp_rw [frontRail,lifted_curl, Orb.cur_expand]; simp -- errors
lemma face_stride (T:Itinerary)(A B C:Sight T G)(i j:Axis)(k:ℕ)(x:Site (T.period k)):
   inner ℝ (rail x (Lattice.square i j) (nativeM T A k)) (spire G x (Lattice.square i j) (nativeM T B k) (nativeM T C k)) = T.gap k ^4 *(ack T A B C i j i j k x-ack T A B C j i i j k x):= by
   simp only [nativeM,map_smul, LinearMap.smul_apply, real_inner_smul_left,real_inner_smul_right,ack, claw,← inner_sub_left]
   rw [show ray i (stalkH T A j) k x-ray j (stalkH T A i) k x=(T.gap k)⁻¹ • rail x (Lattice.square i j) (A k) from ?_, real_inner_smul_left]; field_simp [(T.positive k).ne']
   rw [frontRail]; simp only [Bare.wideCurl,ray,surface,combine,up,stalkH, List.length_singleton,pow_one, Pi.smul_apply,← smul_sub]; congr 1; abel
lemma fir (T:Itinerary)(A:P→ Sight T G)(k:ℕ)(x:Site (T.period k))(i j:Axis):
  6*(8*tower G x (Lattice.square i j) (nativeM T (A 0) k) (nativeM T (A 1) k) (nativeM T (A 2) k)) = -(T.gap k)^4 * ∑ t:P, (ack T (A t) (A (foreL t)) (A (aft t)) i j i j k x-ack T (A t) (A (foreL t)) (A (aft t)) j i i j k x):= by
 rw [tower_eq]; simp_rw [face_stride]; -- P use fin_sum
 let f(t:P):= ack T (A t) (A (foreL t)) (A (aft t)) i j i j k x-ack T (A t) (A (foreL t)) (A (aft t)) j i i j k x
 rw [show (∑ t:P,f t)=f 0+f 1+f 2 from by simp [P, Fin.sum_univ_succ]; abel] -- unfold
 have e0: Triad.lag 0=2:=by decide
 have hw : Triad.lag 1=0:=by decide
 have he : Triad.lag 2=1:=by decide
 unfold f foreL aft; rw [e0,hw,he,show Triad.slide 0=1 from by decide, show Triad.slide 1=2 from by decide,show Triad.slide 2=0 from by decide]; ring
-- regret weighting
abbrev tagV (T:Itinerary)(A:P→ Sight T G)(k:ℕ):= lapSky G (T.period k) (nativeM T (A 0) k) (nativeM T (A 1) k) (nativeM T (A 2) k)
def firstQ (T:Itinerary)(A:P→ Sight T G)(m:P)(i j:Axis):= (MinusUnit T (ack T (A m) (A (foreL m)) (A (aft m)) i j i j)-MinusUnit T (ack T (A m) (A (foreL m)) (A (aft m)) j i i j))
lemma spiral (T:Itinerary)(A:P→Sight T G)(k:ℕ): 6*tagV T A k= - (∑ i: Axis,∑ j:Axis,if i< j then ∑ m:P, firstQ T A m i j k else 0) := by
 have hw(i j:Axis): ∑ m:P, firstQ T A m i j k= T.gap k^4 * ∑ x:Site (T.period k),∑ t:P, (ack T (A t) (A (foreL t)) (A (aft t)) i j i j k x - ack T (A t) (A (foreL t)) (A (aft t)) j i i j k x):=by
   unfold firstQ; simp_rw [Pi.sub_apply,MinusUnit, ← mul_sub, ← Finset.sum_sub_distrib,←Finset.mul_sum]; congr 1; rw [Finset.sum_comm]
 rw [tagV,sided]; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
 rw [←Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm, ←Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; rw [hw]; split_ifs with h
 · simp only [fir,neg_mul,Finset.sum_neg_distrib,←Finset.mul_sum] -- exponent parsing `-t^4`
 simp
end YM.RG11.FirstW.Branch
