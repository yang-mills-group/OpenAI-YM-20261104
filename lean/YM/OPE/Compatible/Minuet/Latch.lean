import YM.OPE.Compatible.Minuet.Hold
/-!
 # Weighted kernel with exterior bits. Identity without dividing signed component. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T: Tube G S} {R : Rep G f}
    {p : BudgetPoint} {m n: ℕ} {W a r t σ E Λ μ x κ C w ε D b B: ℝ}
variable {F:Forest S.ratio} {I J:Seats F}{X Y Z:Support f}{q:Support c}
def dazed (j:I ⊆ J)(A B:ℝ)(x:World F J G):Prop:= Shelter I B (fun i=> x ⟨_,j i.property⟩)∧∀ i:↥J,i.val∉ I → G.chord (x i)≤ A
lemma dawning (j:I ⊆ J)(A B:ℝ):MeasurableSet {p:World F J G|dazed j A B p}:=by
   refine MeasurableSet.inter (s₁:= {p:World F J G| Shelter I B (fun i=> p ⟨_,j i.property⟩)}) (?_) ?_; swap
   · change MeasurableSet {p:World F J G| ∀ i:↥J, i.val∉I → G.chord (p i)≤ A};rw [Set.setOf_forall]; apply MeasurableSet.iInter; intro i
     by_cases h:i.val∈I
     · simp [h]
     simp only [h,not_false_eq_true,forall_true_left]; exact measurableSet_le (G.continuous_chord.measurable.comp (measurable_pi_apply i)) measurable_const
   apply (measurable_pi_lambda _ ?_) (hut (F:=F) I B);exact fun i=> measurable_pi_apply _
lemma faction (j:I⊆J)(A B:ℝ)(u:World F I G)(x:Rim G I): dazed j A B (curveF F J (Wind I u x)) ↔ Shelter I B u∧∀ k:↥(J\ I), G.chord (x ⟨k.val,(mem_sdiff.mp k.property).2⟩)≤ A:=by
   unfold dazed; rw [show (fun i:↥I=> curveF F J (Wind I u x) ⟨i.val,j i.property⟩)= u from interior_e I u x]; refine and_congr_right fun _=>?_ ; constructor
   · intro h k; let y :{j:F.Free//j∉I}:=⟨k.val,(mem_sdiff.mp k.property).2⟩; change G.chord (x y)≤ A; rw [← exterior_e I u x y]; exact h ⟨y.val,(mem_sdiff.mp k.property).1⟩ y.property
   intro h i hi; let y: {j:F.Free//j∉I}:=⟨i.val,hi⟩; change G.chord (Wind I u x y.val)≤_; rw [exterior_e]; exact h ⟨y.val,mem_sdiff.mpr ⟨i.property,hi⟩⟩
lemma dazzling (hi:I⊆J)(p:F.Slice G)(ha:a ≤ B)(hx:dazed hi a B (curveF F J p)): lights J p B:=by
   obtain ⟨h,hp⟩:=hx; intro i hj
   by_cases hv:i∈ I
   · exact h ⟨_,hv⟩
   exact (hp ⟨i,hj⟩ hv).trans ha
variable (H:Primacy F I J Y X Z q R.p.B n) (P: S.patch.Branches S.kernel G)(hR:R.Lawful σ C Λ E w)(V:Config G c)(k:S.Choices)
variable (f':World F I G→ℝ)(hf:Envelope f'){A:ℝ}(hw:∀ w,‖f' w‖≤A)
def trawl (I J:Seats F)(R:Rep G f)(V:Config G c)(m:ℕ)(k:S.Choices)(a B:ℝ)(j:I⊆J)(f:World F I G→ℝ)(x:World F J G) := if dazed j a B x then f (fun i=> x ⟨_, j i.property⟩)- report I J R V m k B f x else 0
def allege (I J:Seats F)(R:Rep G f)(V:Config G c)(m:ℕ)(k:S.Choices)(a B:ℝ)(j:I⊆J)(f₀:World F I G→ℝ): Config G f→ℝ:= trawl I J R V m k a B j f₀ ∘ chant F J
include H P hR hf hw
lemma allegation : Paced R X S (allege I J R V m k a B H.nested f') (2*A):=by
   have hp :0≤A:=(norm_nonneg _).trans (hw 1)
   refine crease H.broad (Measurable.ite (dawning H.nested _ _) ((hf.meas.comp (measurable_pi_lambda (fun x:World F J G=> fun i:↥I=> x ⟨_,H.nested i.property⟩) (fun i=> measurable_pi_apply _))).sub (reports_x I P hR V m k _ f' hf J)) measurable_const) ?_
   intro v; unfold trawl;split; exact (norm_sub_le ..).trans ((add_le_add (hw _) (atReport I P hR V m k B f' hf hw v|>.1)).trans_eq (two_mul _|>.symm)); rw [norm_zero];positivity
variable (hD:WilsonStartup.Decent R.clip R.p)(hy:Geo.Width R.p R.clip σ)(hk:m ≤ R.p.B)(hN:∀ U:Config G f,naked S q n U B→ ordFrame S (halo 1 q) U ∧ ordBest S q U)(hb:4*B≤ R.p.threshold)(ha:a ≤ B)(hC:0≤B)
local notation "fL"=> allege I J R V m k a B H.nested f'
include hD hy hk hN hb ha hC
omit hf hw in
lemma vows (x:Rim G I) (hu:∀ i: ↥(J\I), G.chord (x ⟨i.val,(mem_sdiff.mp i.property).2⟩)≤ a) (p:World F I G):
    let W:= F.drape (Wind I p x);let z:= F.drape (Wind I 1 x); let r:=cinnamon R m I
    S.density R.beta W V*mellow R X W*Real.exp (r W)* fL W= S.density R.beta z V*mellow R X z * (ballotY I R V m k B (intoN I J x) p*(f' p-report I J R V m k B f' (intoN I J x))):=by
       intro g z r
       let j := curveF F J (Wind I p x); have he : chant F J g=j:= chant_eq _ _ _
       obtain ⟨h1,h2⟩:= couponSt I J p x
       by_cases hp: Shelter I B p; swap
       · have h' : ¬ dazed H.nested a B j:=mt (faction H.nested a B p x|>.mp) fun h=> hp h.1
         have hv : fL g=0:=by unfold allege trawl; simp only [Function.comp_apply,he, if_neg h']
         rw [hv, mul_zero, ballotY, if_neg hp,zero_mul,mul_zero]
       let a₀:=dazed (G:=G) H.nested a B;have ht:a₀ j:=(faction H.nested a B p x).2 ⟨hp,hu⟩
       have hg : lights J (Wind I p x) B := dazzling H.nested _ ha ht
       have hj:a₀ (curveF F J (Wind I p (ald I J j))):= h2 ▸ ht
       have hG := dazzling H.nested _ ha hj
       have hs:S.density R.beta g V*mellow R X g*Real.exp (r g)=S.density R.beta z V *mellow R X z * Ruin R V m I k (F.drape (Wind I p (ald I J (intoN I J x)))):=by
           rw [h1,← H.linked P hR hD hy hk V k (Wind I p x) _ hC hb h2 hg hG]; have hv:= H.soma P hR hD hy hk V k (Wind I p x) hC hb hN hg; rw [resetting] at hv; exact hv
       have hv (p:World F I G): ballotY I R V m k B j p = ballotY I R V m k B (intoN I J x) p :=by unfold ballotY; rw [h1]
       have he':report I J R V m k B f' j=report I J R V m k B f' (intoN I J x):=by unfold report; rw [funext hv]
       rw [hs,allege,Function.comp_apply,he,trawl,if_pos ht,he',ballotY,if_pos hp]; rw [show (fun i:↥I=> j ⟨i.val,H.nested i.property⟩)=p from interior_e I p x,mul_assoc (S.density R.beta z V * mellow R X z)]
end YM.PhysicalNext.Repeat.Aroma
