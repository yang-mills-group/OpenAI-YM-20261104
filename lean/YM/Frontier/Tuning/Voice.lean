import YM.Frontier.Tuning.LocalContour
import Mathlib.Analysis.Complex.Liouville

/-! Value-price reserve for the actual support-podium contour. Capture exactly the extra
shape for tilt and leave the seed marks/polynomials. Per component scalar holomorphic
continuation tools, NOT yet continuation in spatial OR vacuum norms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.Voice
open Function Filter Set Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Bid Reserves Ursell Trees
open ConnectedActivityE6 Shell Channel SliceRows Control Window Census Mask Pulse Itinerary Coat
open Packets Presented Sector Raw ProbabilityTheory Poll Pond ComplexVertex GaussContour LocalContour
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal
variable {G : Gauge} {P : Teller G} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {α t e d g : ℝ} {ι : Type*}

/- ### Reserve for the modulus of a tilted marginal -/
section
variable (X : ι → Support c) {B : ℕ} (w a p : ι→ℝ) (hw:∀ i,0≤w i)(hp:∀ i,0≤a i) {ε α γ δ q : ℝ}
local notation "price" => setPrice X B a
include hw
lemma ready_exp (h:Trees.Ready X B (tariff w a p ε) (α+2*ε) γ δ q) (he:0≤α) x (s:Finset ι) :
    rooted X B w x α s * Real.exp (2*ε*price s + ∑ i∈s,p i) ≤
       touches X B (tariff w a p ε) (α+2*ε) x s:=by
  rw [set_exchange]; apply mul_le_mul_of_nonneg_right _ (by positivity)
  unfold rooted touches;split
  next hh=> 
    unfold Trees.currency
    simp only [prod_mul_distrib, ← Real.exp_sum,← mul_sum];exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast Ac.cover X B hh.1) he)) (prod_nonneg fun i _=>hw _)
  rfl

include hp
lemma halfSets (h:Trees.Ready X B (tariff w a p ε) (α+2*ε) γ δ q) (he:0≤α) (hε:0<ε) (x:Site c) (m k:ℕ)
    (Q: Finset ι→Prop)[DecidablePred Q] {T U : ℝ} (hq:∀ s, m ≤ s.card-1→ Ac.Spark X s→x∈s.biUnion X→Q s→ T≤price s ∧ U≤∑ i∈s,p i):
    SumBudget (fun s=> if Q s ∧ m ≤ s.card-1 then rooted X B w x α s * Real.exp (ε * price s) * (1+price s)^k else 0)
         (extract (ε/2) k T U*treeYield γ q m):=by
   let f s:= if m≤ #s-1 then rooted X B w x α s * Real.exp (ε*price s) else 0
   have hf : SumBudget (fun s=> f s * Real.exp (2*(ε/2)*price s + ∑ i∈s,p i)) (treeYield γ q m):=by
      refine budget_mono (touch_tail X B h x m) ?_ (fun s=> ?_)
      · intro s;unfold f rooted;split_ifs; exact mul_nonneg (mul_nonneg (mul_nonneg (prod_nonneg fun i _=> hw i) (Real.exp_pos _).le) (Real.exp_pos _).le) (Real.exp_pos _).le
        all_goals simp only [zero_mul,le_refl]
      unfold f;split_ifs
      · rw [mul_assoc,← Real.exp_add, show ε*price s+_=2*ε*price s+∑ i∈s,p i by ring]; exact ready_exp X w a p hw h he x s
      all_goals simp only [zero_mul, le_refl, if_false, reduceCtorEq]
   convert reserve_tail f price (fun s=>∑ i∈s,p i) (fun i=> nonneg_of_mul_nonneg_left (hf.1 i) (Real.exp_pos _)) (fun s=> sum_nonneg fun i _=> add_nonneg (Nat.cast_nonneg _) (hp i)) (half_pos hε) hf k Q (fun s ht hZ=> ?_H) using 1
   case _H=>
     unfold f rooted at ht; split_ifs at ht
     · apply hq s <;> tauto
     all_goals simp only [zero_mul, ne_eq, not_true_eq_false] at ht
   funext s;unfold f; by_cases ht : Q s <;> by_cases hK : m ≤ s.card-1 <;> simp only [ht,hK,and_self,false_and,true_and,and_false, if_pos,if_neg,zero_mul,not_false_eq_true]
end

-- explicit args instead
def hotSelection (S : StepData c f) (l B) (b:Mixed.Costs) (X:ι→Support c)(a w:ι→ℝ)(p:Stores S→ℝ)(m k r:ℕ)(T:ℝ) (s:Finset (Mixed.Alphabet S ι)):=
    if Mixed.Allowed S l B b X a m r T s then Mixed.Price S l B b X w a p k s * Real.exp (b.reservePoly * Mixed.charges S l B X b a s) else 0
lemma heatHit (S : StepData c f) (l B) (b: Mixed.Costs) (X:ι→Support c) (w a:ι→ℝ) (p:Stores S→ℝ)
   (hb:b.Buy S.patch.L l B) (h:Mixed.Accounts S l B b X w a p) (m k r:ℕ)(T:ℝ):
    Ac.Hit (fun s:Finset (Mixed.Alphabet S ι)=> s.biUnion (Mixed.foot S l B X)) B (hotSelection S l B b X a w p m k r T) b.exponent
      (extract (b.reservePoly/2) k T (b.markSeed*r) * treeYield b.rootHit b.q m):=by
   intro x
   have hd := Mixed.ready_vertices S l B b X w a p hb h
   have ht: ∀ i, 0≤Mixed.lengths S b a i:=by rintro (j|j); exact mul_nonneg hb.extra (Nat.cast_nonneg _); exact h.extra _
   have hw: ∀ i,0≤ Mixed.costs S l B p w i:=by
     rintro (j|j)
     · unfold Mixed.costs; dsimp; split_ifs with hv; exact (h.packetBound j hv).1; rfl
     exact h.holds _
   convert halfSets _ _ _ _ hw ht hd hb.price hb.eps x m k (Mixed.Allowed S l B b X a m r T) (U:=b.markSeed*r) ?_H using 1
   case _H=> intro s _ _ _ hs; exact ⟨hs.2.2.2,by unfold Mixed.stamp; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs.2.2.1) hb.marked⟩
   funext s; by_cases hp : Mixed.Allowed S l B b X a m r T s ∧ x∈s.biUnion (Mixed.foot S l B X)
   · simp only [hotSelection,hp.1,hp.1.1,hp.1.2.1, hp.2,and_self,if_true, rooted]; unfold Mixed.Price Mixed.charges
     unfold Trees.currency; ring
   simp only [hotSelection,rooted];by_cases ht': Mixed.Allowed S l B b X a m r T s
   · have hz : x∉s.biUnion (Mixed.foot S l B X) := fun h=>hp ⟨ht',h⟩
     simp only [ht',hz,false_and,true_and,and_false,if_false,if_true,zero_mul,ite_self]
   simp only [ht',false_and,if_false,zero_mul,ite_self]

variable {R : Rep G f} {L : Side} {Ñ : ChartRatio G} {Q: YM.ConnectedActivityE6.Target G P}{x W μ C : ℝ}{o : Target.Order G W}
variable {B : ℝ}

def resetBeta (R:Rep G f)(β:ℝ): Rep G f := { R with beta:=β }
lemma intakeBeta (hh:Intake P T x R) {β:ℝ} (h:betaF G x S.patch.L/2≤β ∧ β≤2*betaF G x S.patch.L):Intake P T x (resetBeta R β) where
   ready:= hh.ready
   received:= ⟨hh.received.path,hh.received.clip,hh.received.temp⟩
   cap:=⟨hh.cap.paths,hh.cap.labels⟩
   exponent:= hh.exponent
   height:= hh.height
   sizes:= hh.sizes
   window:= h
lemma reset_aligned (β): Aligned R (R':=resetBeta R β) := ⟨rfl,rfl,rfl,rfl,rfl⟩
section Pricing
variable {v l : Payload G f}

/-- Quota for logarithmic and forced vertices; warning probability-price and fronts
are invoiced separately below. The pure part is in fixed displacement units. -/
structure Critical (R : Rep G f) (T : Tube G S)(b a θ:ℝ)(Ñ:ChartRatio G) (ve:LogIndex c f→ℝ)(vk:ℕ→ℝ) (sE sK : ℕ→ℝ): Prop where
  positive :0<b
  pure_1 {F:Forest S.ratio} (X:Coat T F) (hz: X.x=x) (hw:X.width=θ)(hm:X.manifest) i w : |ComplexVertex.pureLog X R Ñ a w i b|≤ve i
  pure_2 {F:Forest S.ratio} (X:Coat T F) (hz:X.x=x) (hw:X.width=θ)(hm:X.manifest) i w : |ComplexVertex.pureLog X R Ñ a w i (b/2)|≤ve i
  small i : 13*ve i+  (ComplexVertex.eTagD sE i) ≤1
  pays i : 0 ≤ sK i
def logPrice (ve : LogIndex c f→ℝ)(sE:ℕ→ℝ)(i : LogIndex c f):=2*(13*ve i+ ComplexVertex.eTagD sE i)
def BoundAt (R:Rep G f)(v l:Payload G f) (sE sK : ℕ→ℝ):Prop:= ∀ i, ∀ y, ‖hiddenC R.p.threshold (R.activities.reg i).support (v i) y‖ ≤ sE i ∧ ‖l i y‖ ≤ sK i
lemma Critical.logBound {A a t : ℝ} (X : Coat T F) {ve vk de dk} (h : Critical (x:=x) R T A a t Ñ ve vk de dk) (hx:X.x=x)(ht:X.width=t) (hp:X.manifest){w i}{z:ℂ} (hz:‖z‖ ≤ 2*A)(hF:BoundAt R v l de dk): ‖Complex.exp (ComplexVertex.farLogC X R v a Ñ z w i)-1‖ ≤ logPrice ve de i:=by
   exact ComplexVertex.exp_pay X R Ñ a i w (s:=1) (fun k y=> by simpa only [one_mul] using (hF k y).1) h.positive hz (h.pure_1 X hx ht hp i w) (h.pure_2 X hx ht hp i w) (by rw [one_mul]; exact h.small i) |>.trans_eq (by rw [one_mul]; rfl) -- style
lemma linearZ_scaled (X : Coat T F){v : ℝ→ℝ} (h : ∃ a b:ℝ, ∀ t:ℝ,0<t→v t=a+t*b) {β:ℝ} (ht:0<β) (z:ℂ):
    linearZ v z=(v β:ℂ)+(z-β)/(β/2:ℝ)*((v β:ℂ)-v (β/2)) :=by
   obtain ⟨a,b,hh⟩:=h
   unfold linearZ; rw [hh 1 zero_lt_one,hh β ht,hh _ (half_pos ht),hh 4 (by norm_num)]; push_cast; field_simp [Complex.ofReal_ne_zero.mpr ht.ne']; ring
lemma pure_bound (X:Coat T F) (i w) {Y E' v a:ℝ} (hv :0<v)
   (hh: |X.farLog (resetBeta R v) a Ñ (heat v w) i|≤ Y)
   (hE : ‖Epart X R (fun i y=> (R.activities.E i y:ℂ)) a w i‖≤ E'):
   |ComplexVertex.pureLog X R Ñ a w i v|≤Y+E':=by
   rw [← Real.norm_eq_abs,← Complex.norm_real]
   refine le_trans ?_ (add_le_add (show ‖((X.farLog (resetBeta R v) a Ñ (heat v w) i:ℝ):ℂ)‖ ≤ Y from ?_Y) hE)
   case _Y => simpa only [Complex.norm_real,Real.norm_eq_abs] using hh
   have h:= far_real X (R:=R) (reset_aligned v) (fun i y => (R.activities.E i y:ℂ)) (fun _ _=>rfl) a Ñ w i rfl hv
   change farLogC X R (fun i y=> (R.activities.E i y:ℂ)) a Ñ (v:ℂ) w i = _ at h

   rw [farLogC,linearZ_scaled X (far_affine X R i ..) hv ((v:ℝ):ℂ),sub_self, zero_div,zero_mul,add_zero] at h
   rw [show (pureLog X R Ñ a w i v:ℂ) = (X.farLog (resetBeta R v) a Ñ (heat v w) i:ℝ) + Epart X R (fun i y=> (R.activities.E i y:ℂ)) a w i from eq_add_of_sub_eq h]
   exact norm_add_le ..

variable (b' : Mixed.Costs) (H : Cash W x μ L Q o C T R)
local notation "regions" => Mixed.foot S Q.halo (radiusB x) (footprints T R Q.halo (radiusB x))
--
-- rate field cannot depend on H if b' changed. Precise formula per geometry before ceilings.
def strainG (G : Gauge) (L : Side)(x:ℝ):= (Animals.ballCost (radiusB x) * Itinerary.density L * Fintype.card G.ColorIndex : ℝ)
private lemma pens_cost (X:Coat T F)(A:Stores S) (hx: 0<X.B) (ha:500≤Q.halo) :
    (X.pens A).card ≤ (A.dome (Q.halo*X.B)).card * Itinerary.density S.patch.L:=by
   have he := (show ∀ t:Support c, #(univ.filter (fun i:Bond f=>atEdge S i∈t)) ≤ _ from ConnectedActivityE6.Census.perch S)
   refine (Finset.card_le_card (show X.pens A⊆ Finset.filter (fun i:Bond f=> atEdge S i∈A.dome (Q.halo*X.B)) univ from ?_)).trans (he _)
   intro i hi; apply mem_filter.mpr ⟨mem_univ _, ?_⟩
   apply Corona.halo_mono (show 10*X.B+1≤ Q.halo*X.B by have ht:=Nat.mul_le_mul_right X.B ha; omega) ?_ (lives_in i A (mem_filter.mp (mem_of_mem_filter _ hi)).2); exact Finset.Subset.refl _ -- halo_mono namespace?
lemma gain_sum (X : Coat T F) (p : Molecule S) (hx:X.x=x)(hp:0<X.B) :
    let P:= podium S G (H.unionP p) X.B
    (∑ i∈p.toLeft, massPower X i) + (P.card:ℝ)/2 ≤ H.shapeW p*strainG G S.patch.L x:=by
   intro P; unfold strainG; let B:=radiusB x; let Y v:= (H.supportP v).card
   have hE: X.B=B:=congr_arg radiusB hx; rw [hE] at hp
   have hd'n A: (X.pens A).card ≤ Y (.inl A)*Itinerary.density S.patch.L:=by
     have hY: Y (.inl A)= #(A.dome (Q.halo*X.B)):= by rw [hE]; rfl
     rw [hY]; exact pens_cost (Q:=Q) X A (hE ▸ hp) Q.buys
   have hd A: massPower X A ≤ (Y (.inl A) * Itinerary.density S.patch.L * Fintype.card G.ColorIndex / 2:ℝ) := by
     unfold massPower; have hg: 0≤ (Fintype.card G.ColorIndex:ℝ):= Nat.cast_nonneg _
     have hv := mul_le_mul_of_nonneg_left (show #(X.pens A) ≤ (Y (.inl A):ℝ)*(Itinerary.density S.patch.L:ℝ) from by exact_mod_cast hd'n A) hg; linarith only [hv]
   have hp0: (∑ i∈p,(Y i:ℝ)) ≤ H.shapeW p*(Animals.ballCost B:ℝ):=by
     unfold Cash.shapeW Mixed.charges Reserves.setPrice; rw [sum_mul]; apply sum_le_sum; intro i hi
     have hN: (Y i:ℝ) ≤ (coverNumber B (H.supportP i):ℝ)*(Animals.ballCost B:ℝ):=by exact_mod_cast Blaze.brood (H.supportP i) B
     have hw:0≤ Mixed.lengths S H.faresP (ConnectedActivityE6.lengths T R) i:=by rcases i with i|i; exact mul_nonneg H.laws.acquired.extra (Nat.cast_nonneg _); exact Nat.cast_nonneg _
     exact hN.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hw) (Nat.cast_nonneg _))
   have hp1: (∑ i∈p.toLeft,(Y (.inl i):ℝ)) ≤ ∑ i∈p,(Y i:ℝ):=by
     exact (le_add_of_nonneg_right (sum_nonneg (s:=p.toRight) fun i _=> (Nat.cast_nonneg _:(0:ℝ)≤Y (.inr i)))).trans_eq (by rw [← Finset.sum_disjSum p.toLeft p.toRight (fun i=> (Y i:ℝ)), Finset.toLeft_disjSum_toRight])
   have hd' := sum_le_sum (s:=p.toLeft) (fun i _=> hd i)
   have he' := calc
      (∑ i∈p.toLeft,massPower X i) ≤ _ := hd'
      _ = (∑ i∈p.toLeft,(Y (.inl i):ℝ)) * (Itinerary.density S.patch.L * (Fintype.card G.ColorIndex/2:ℝ):ℝ) := by rw [sum_mul]; apply sum_congr rfl; intros; ring
   have hm:= Blaze.Flux.crewsC H p
   have hP : P = (Blaze.Flux.edgesM S (H.unionP p) B) ×ˢ Finset.univ:=by change podium S G (H.unionP p) X.B= _; rw [hE,← Blaze.Flux.chargedU]; rfl
   rw [hP,card_product,card_univ]; push_cast
   have hc := mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg (Fintype.card G.ColorIndex): (0:ℝ)≤_) ; change _ ≤ _ at hc
   have ht := mul_le_mul_of_nonneg_right (hp1.trans hp0) (show (0:ℝ)≤Itinerary.density S.patch.L * (Fintype.card G.ColorIndex/2:ℝ) from by positivity)
   dsimp [B] at *; nlinarith only [he', hc, ht]
end Pricing
end YM.Frontier.Tuning.Voice
