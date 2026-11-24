import YM.RG12.Burst.Thin
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Sparks
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Revenue
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy.Charity.RG12
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters Blaze.March
variable (M:Leaf R) (H:Cash W x μ L Q o C T R)
    {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)
local notation "d0" => jewelDebt M Q L x
local notation "Z" => N.conduit
local notation "cR" => Q.costs L μ R.beta x q

-- rescaled ingress readiness. Before θ.W. uniform in call-world.
open PhysicalNext.Repeat.Height
local notation "Ξ" => N.conduit
abbrev sign11 : Head S→ℕ := Sum.elim (fun _ : Stores S=>0) Silica.horn
local notation "sf" => grow G L x
local notation "wo" => Q.mark L μ x
def mail11 :ℝ:=(grow G L x)^sign11 (M.turn.badge S) -- χ radius for the mark itself.Nodeflow.S
local notation "m11" => mail11 (S:=S) (L:=L) (x:=x) M
/-- RISK combined, ALL optional and packet penalties through both tree currencies. Not claiming magnitude of true costs grows when stance of one barcode occurs. Some purposes(residual E projection effects) need additional spatial costs appended. This currency asks just on \sup criterion & projections. -/
def risk (g:Molecule S):ℝ:=sf^pins S g*Height.gust S wo s g
set_option quotPrecheck false
local notation "R11" g => risk (S:=S) (Q:=Q) (L:=L) (μ:=μ) (x:=x) (s:=s) g
lemma mintN (hg:1≤ grow G L x) : 1≤ m11:= one_le_pow₀ hg
lemma riskN (hs:1≤ s)(hg:1≤grow G L x)(hw:0≤ Q.mark L μ x) (g:Molecule S):1≤ (R11 g) := by
   unfold risk Height.gust; exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hg) (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hs) (Real.one_le_exp (mul_nonneg hw (Nat.cast_nonneg _))))
lemma scent {S:StepData c f} (s t g:ℝ) (i:Head S→ℝ) (m:Molecule S):
    ∏ v∈m,Height.gale S t s (fun v=>g^sign11 v*i v) v= g^pins S m*Height.gust S t s m*(∏ v∈m,i v) :=by
   unfold gale gust pins Cash.numP sign11; simp only [prod_mul_distrib,prod_const,prod_pow_eq_pow_sum,Nat.cast_sum,mul_sum,Real.exp_sum]; ring

-- apply abstract Ready to sterling upper envelope w * D^horns. We don't pay twice for sails.
lemma set11 (w e : Head S → ℝ) (hw:∀ i,0≤w i)(he:∀ i,0≤e i)(B:Costs)
    (hr:Ready H.supportP (radiusB x) (Reserves.tariff (fun i=> sf^sign11 i*w i) e (Mixed.stamp S B) Q.ε) (Q.exp+2*Q.ε) B.rootHit Q.δ B.q)
    (hs:1≤ s)(hg:1≤grow G L x)(hpay:degreePrice (radiusB x) (s*B.rootHit) Q.δ≤1/2)
    (hm:B.markSeed= Q.mark L μ x) (hx:∀ i,H.shapeW i= Reserves.setPrice H.supportP (radiusB x) e i) (k:ℕ):
    Ac.Hit H.unionP (radiusB x) (fun i=> (R11 i)*(if H.ticketsP 0 0 0 i then (∏ i∈i,w i)*(1+H.shapeW i)^k else 0)) Q.exp (Reserves.extract Q.ε k 0 0 * Reserves.treeYield (s*B.rootHit) (1/2) 0):=by
   let f i:= sf^sign11 i*w i; let V:=Height.gale S wo s f; let z:Head S→ℝ:=0; let B':=radiusB x
   have hz:Reserves.tariff V e z Q.ε = fun i=> s*Reserves.tariff f e (Mixed.stamp S B) Q.ε i:=by
      funext i; unfold Reserves.tariff V Height.gale Mixed.stamp; rw [hm,Real.exp_add,show z i=0 from rfl,Real.exp_zero,Real.exp_add]; ring
   have hy:= Mixed.Coupons.inflate H.supportP B' (Reserves.tariff f e (Mixed.stamp S B) Q.ε) hr (zero_lt_one.trans_le hs) hpay (by norm_num); rw [← hz] at hy
   have hV i : 0≤ V i:=by unfold V Height.gale f; have hm:= hw i; positivity
   intro y; have hq:= Reserves.sets H.supportP B' V e z hV he Q.usable Q.bound hy 0 k y (fun i=>H.ticketsP 0 0 0 i) (T:=0) (U:=0) (fun i _ _ _ _=> ⟨hx i ▸ H.positive_volume i,by simp [z]⟩)
   convert! hq using 2; rename_i i; unfold Reserves.rooted; dsimp only
   by_cases hl:H.ticketsP 0 0 0 i; swap
   · simp only [hl, ↓reduceIte,mul_zero,zero_mul,false_and]; split <;> rfl
   by_cases hv:y∈H.unionP i
   · have hf:Ac.Spark H.supportP i:=(H.attends i).1 hl
     have hx':y∈i.biUnion H.supportP:=hv
     rw [if_pos hl,if_pos hv,if_pos ⟨hl,Nat.zero_le _⟩,if_pos ⟨hf,hx'⟩,←hx i,show (∏ j∈i,V j)=_ from scent s wo sf w i]; unfold risk currency; rw [show Finset.biUnion i H.supportP=H.unionP i from rfl]; unfold B'; change _ = (_*_)*_; ring -- maybe currency reduces to coverNumber H.unionP (defeq)
   rw [if_neg hv,if_pos ⟨hl,Nat.zero_le _⟩,if_neg (show ¬(Ac.Spark H.supportP i∧ y∈i.biUnion H.supportP) from fun h=> hv (show y∈H.unionP i from h.2)), zero_mul]
variable (hvy:Silica.Heavy N.conduit)(hg:1≤grow G L x)(hs:1≤ s)
    (h1:degreePrice (radiusB x) (s*(Q.costs L μ 1 x 0).rootHit) Q.δ≤1/2)
include hvy hg hs h1
lemma clearer11 (k:ℕ):Ac.Hit H.smallAt (radiusB x) (fun i=> (R11 i.val)*(Ξ).meant i.val k) Q.exp (white Q L μ x s k):=by
   let g (i:ConnectedActivityE6.Alphabet c f):= sf^Silica.horn i*(Ξ).flair i
   let X := Q.costs L μ R.beta x q; let p:=steamP S X; let e:=Mixed.lengths S X (ConnectedActivityE6.lengths T R)
   have hr : Ready _ _ _ (Q.exp+2*Q.ε) _ _ _:=(Mixed.ready_vertices S Q.halo (radiusB x) X H.birth g _ p (Ξ).lives ⟨(Ξ).accrues.packetBound,hvy.nonneg,(Ξ).accrues.extra,hvy.hit⟩)
   have hh:Mixed.costs S Q.halo (radiusB x) p g= fun i:Head S=> sf^sign11 i*(Ξ).fare i:=by
      funext i; rcases i with i|i; · unfold sign11; simp; rfl
      rfl
   rw [hh] at hr
   have he i:0≤e i:=by rcases i with i | i; exact mul_nonneg (Ξ).lives.extra (Nat.cast_nonneg _); exact Nat.cast_nonneg _
   intro i; exact budget_pull (fun i:H.ThinP=>Subtype.val i) Subtype.val_injective (set11 H _ _ (Ξ).fares he _ hr hs hg h1 rfl (fun _=>rfl) k i)
omit h1
variable (h2:degreePrice (radiusB x) (s*(swing Q L μ 1 x 0).rootHit) Q.δ≤1/2) (hv:Bikes Q L μ x a E B j n)(hF:foam Q L)
include h2 hv hF
/-- To buy combined retention for the Marked cluster part, the marker consumes a THINNER
share. It spends on assembly separately. Covers touch & marked numerical gains. Doesn't classify non-sharing occupations. -/
lemma keeper11 (k:ℕ): Ac.Hit H.smallAt (radiusB x) (fun i=> ((R11 i.val)*persona M H q N.conduit.flair 0 k 0 i.val)/m11) Q.exp (black Q L μ x s k):=by
   let r : ConnectedActivityE6.Alphabet c f→ℝ:=fun i=> sf^Silica.horn i*(Ξ).flair i
   let X:=Q.costs L μ R.beta x q; let Y:=swing Q L μ R.beta x q; let f':= steamP S X; let d:=ConnectedActivityE6.lengths T R
   have hE:Accounts S Q.halo (radiusB x) X H.birth r d f':= ⟨(Ξ).accrues.packetBound,hvy.nonneg,(Ξ).accrues.extra,hvy.hit⟩
   have hV:=H.laws.data.funds.length_eq
   have hZ : R.p.B ≤ 2*radiusB x:=by rw [H.laws.intake.sizes,hV]; exact hv.covers
   have hn:= coco M H hF hZ r f' q hE
   let g:=colly r M Q L x; have hR : Y.Buy S.patch.L Q.halo (radiusB x):=by rw [hV]; exact hv.rev _ _ (hV ▸ (Ξ).lives)
   let u :=Mixed.costs S Q.halo (radiusB x) f' g
   let e:=Mixed.lengths S Y d
   have hr:Ready _ _ (Reserves.tariff u e _ _) _ _ _ _:= Mixed.ready_vertices S Q.halo (radiusB x) Y H.birth g d f' hR hn
   let l:=M.turn.badge S; let b:=needle M H q (Ξ).flair; let W (i):= if i=l then b i/m11 else b i
   have hX0:= zero_lt_one.trans_le (mintN M (S:=S) hg)
   have hf : u= fun i=> sf^sign11 i*W i:=by
       funext i; unfold u W; by_cases hh : i=l
       · subst i; rw [if_pos rfl,show sf^sign11 l=m11 from rfl, mul_div_cancel₀ _ hX0.ne']; change needle M H q r l=b l; unfold l b; rw [nose,nose]
       rw [if_neg hh]; unfold b; rw [sleeve M H q _ i hh]
       rcases i with i|i
       · unfold sign11; simp; rfl
       change (if i=sparkling c f M.turn then _ else r i)=_; rw [if_neg (fun ht=> hh (Eq.trans (congr_arg Sum.inr ht) (sparkPath M.turn S)))]; rfl
   have he i:0≤e i:=by rcases i with i|i; exact mul_nonneg hR.extra (Nat.cast_nonneg _); exact Nat.cast_nonneg _
   have h0 i:0≤ W i:=by have hx:=earns M H q (Ξ).flair i (Ξ).fares; unfold W; split; exact div_nonneg hx hX0.le; exact hx
   rw [hf] at hr
   intro i; have hx:= set11 H W e h0 he Y hr hs hg h2 rfl (fun _=>rfl) k i
   refine budget_mono (budget_pull (fun i:H.ThinP=>Subtype.val i) Subtype.val_injective hx) (fun p=>?_) (fun p=> ?_)
   · split; exact mul_nonneg (div_nonneg (mul_nonneg (zero_le_one.trans (riskN hs hg (Ξ).lives.marked _)) (earned M H q (Ξ).flair (Ξ).fares ..)) hX0.le) (Real.exp_pos _).le; rfl
   split
   next h=>
     dsimp only; rw [if_pos (show i∈H.unionP _ from h)]; unfold persona
     by_cases ht:H.ticketsP 0 0 0 p.val
     · rw [if_pos ht]; split
       next hv=>
         have hz:=hv.2; change (R11 p.val)*( ((∏ i∈p.val,b i)*_)) /m11* _ ≤ (R11 p.val)*((∏i∈p.val,W i)*_)*_
         rw [← mul_prod_erase _ b hz,←mul_prod_erase _ W hz]; unfold W; rw [if_pos rfl,show (∏ i∈p.val.erase l,(if i=l then b i/m11 else b i))=∏ i∈p.val.erase l,b i from prod_congr rfl fun i hi=> if_neg (ne_of_mem_erase hi)]
         apply le_of_eq; unfold l Cash.smallAt; ring -- maybe
       rw [mul_zero,zero_div,zero_mul]; exact mul_nonneg (mul_nonneg (zero_le_one.trans (riskN hs hg (Ξ).lives.marked _)) (mul_nonneg (prod_nonneg fun _ _=>h0 _) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume p.val)) _))) (Real.exp_pos _).le
     rw [if_neg ht,if_neg (show ¬ (H.ticketsP 0 0 0 p.val ∧ _) from fun h=>ht h.1)]; simp
   next h=> exact (budget_pull _ Subtype.val_injective hx).1 p
include h1
def Zoe1 (i:H.ThinP):ℝ:=2^(j+2)*(momentS H N i+2*(sip M H N i/m11))
def blue (g:H.ThinP):ℝ:= (R11 g.val)*Zoe1 M H N g
lemma bright11 {a:ℝ} (hV:a ≤ Q.exp): Ac.Hit H.smallAt (radiusB x) (blue M H N (s:=s)) a (value10 Q L μ x s B j n):=by
  intro x0
  have he:= clearer11 H N hvy hg hs h1 n x0
  have ht:= keeper11 M H N hvy hg hs h2 hv hF n x0
  have hh:=budget_scale (show 0 ≤ (2:ℝ)^(j+2) from by positivity) (budget_plus (budget_scale N.balance he) (budget_scale zero_le_two (budget_scale N.balance ht)))
  have hm:=zero_lt_one.trans_le (mintN M (S:=S) hg)
  have hb (i:H.ThinP):0≤ blue M H N (s:=s) i:=by
     have ht:= right H N i; have h0:= rise M H N i; have he:= riskN (S:=S) (μ:=μ) (Q:=Q) hs hg H.laws.acquired.marked i.val
     unfold blue Zoe1; positivity
  refine budget_mono hh (fun i=> ?_) (fun i=> ?_)
  · split; exact mul_nonneg (hb _) (Real.exp_pos _).le; rfl
  dsimp only; split
  next h=>
    apply (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hV (Nat.cast_nonneg _))) (hb _)).trans_eq
    unfold blue Zoe1 sip momentS; ring
  simp
local notation "t!" => Q.goal L x+ value10 Q L μ x s B j n
lemma honey (h3:degreePrice (radiusB x) t! E ≤ 1/2) : Ready H.smallAt (radiusB x) (blue M H N (s:=s)) (a+E) t! E (1/2):=by
  have hh:= bright11 M H N hvy hg hs h1 h2 hv hF hv.win
  refine ⟨add_pos_of_pos_of_nonneg (arable H) (budget_nonneg (hh 0)),hv.allow,h3,(by norm_num),fun i=>?_ ,fun x=> budget_loosen (hh x) (le_add_of_nonneg_left (arable H).le)⟩
  obtain ⟨i',hi⟩:=i.property.1; have he:=(hh i').1 i; dsimp only at he; rw [if_pos (show i'∈H.smallAt i from hi)] at he; exact nonneg_of_mul_nonneg_left he (Real.exp_pos _)
end YM.PhysicalNext.Repeat.Daisy.Charity.RG12
