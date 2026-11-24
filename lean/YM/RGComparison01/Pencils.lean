import YM.RGComparison01.Bonus
import YM.RGComparison01.Ciudad

/-!
# Actual model log through Taylor at AUX, before matching/Pk

 yield analogue of franchised low budget from the TRUE log here via Pushed; add
 base and model comparisons from the generating prescription to be
 supplied through finite jets. Keep values over star Burns. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pencils
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage AuxBeam AuxSpell AuxJets AuxStage
open Spline Tensor WilsonStartup Boulevard
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} {c f : Side} {S:StepData c f} {k n j m w w' M : ℕ} {α β C Λ σ J K d H M' i' : ℝ}
variable (T : Tube G S) (B B' : BudgetPoint)
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "b" => gStep β

lemma blue (P : BudgetPoint) : (1:Config G c) ∈ sunny P:= fun i=> by simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using P.threshold_pos
lemma created : (Boulevard.actual (0:Xs))=1:= by unfold actual; rw [map_zero]; exact link_one

/-- This auxiliary vacuum spouse keeps exactly clipped action terms
 and masked extras, no K even abroad. Not the physical R at real scale. -/
def Mate (R : RG.Rep G f) (e : Config G f → ℝ) (β:ℝ):= R.beta=β ∧ R.eval=(Pane.virgin T B β).eval * gross e 1
lemma on_mate (R : RG.Rep G f) (e : Config G f→ℝ)
    (he : R.clip=T.high) (ht:R.path=T.up) (hp:R.p=B) (hq:R.v=0)
    (hb:∀ V,R.activities.gas B V= (if flags B.threshold V=∅ then 1 else 0))
    (hw:∀ V,flags B.threshold V=∅ → R.activities.additive B V= -e V) :
    Mate T B R e R.beta := by
  refine ⟨rfl,funext fun V=>?_⟩; by_cases hx: flags B.threshold V=∅
  · rw [Pi.mul_apply,Pane.sparkling,if_pos hx]; unfold RG.Rep.eval RG.Rep.exponent; rw [he,ht,hp,hq,hb V,if_pos hx,hw V hx,sub_neg_eq_add,zero_mul,zero_sub,mul_one]; rw [Pane.crystalline _ _ _ _ _ hx, Real.exp_add]; simp [gross]
  rw [Pi.mul_apply,Pane.sparkling,if_neg hx]; unfold RG.Rep.eval; rw [zero_mul,hp,hb V,if_neg hx,mul_zero]

def metricA (α : ℝ) (R:RG.Rep G f) (V:Config G c):= Real.log (S.push R.beta R.eval V)+Bonus.ember T α R.beta V

-- Points plus base. not including final f here
variable (A:ChartRatio G) (F:Forest S.ratio) (ρ:Bid.Dir G c→AxisChart G F)
  (i:S.Choices) (R:RG.Rep G f) (e: Config G f→ℝ)
  (E:Poll.Body (Precision.Key F G) → ℝ × Positions (Uniform.Primary c G) → ℝ)
def aperture (α : ℝ) (q n : ℕ): AuxStage.Co Xs:= Spline.centred (AuxBeam.logVia A T F ρ i E q n)+Bonus.baseP T α
-- PROPER fields use before post-Hessian α relative term. scalar tracked. -
lemma parsed (he: Mate T B R e β) : stillA (metricA T α R) ∘ Boulevard.actual = centre (givenLog A T F ρ i B β e) + centre (Bonus.ember T α β ∘ Boulevard.actual):= by
  funext V; unfold stillA metricA; simp only [he.1,he.2,centre,givenLog,AuxBeam.weighLess, AuxWeigh.weighed,Function.comp_apply,actual, Pi.add_apply,map_zero,link_one]; ring

def bounder (k q : ℕ) := ((k+(0+q*k))*k + (k+2))+(k+2)
lemma records (k q : ℕ) : Spline.Field (bounder k q) k (aperture T A F ρ i E α q k) := by
  apply Spline.Field.add; swap
  · apply Spline.Field.add
    · exact Spline.Field.weaken (Spline.Field.ritualP _ _ _) (by unfold bounder; omega)
    exact Spline.Field.weaken (Spline.Field.ritualP _ _ _) (by unfold bounder; omega)
  apply Spline.Field.centred
  apply Spline.Field.add
  · exact Spline.Field.weaken ((Spline.Field.Laced (Lapis.gram F T.up T.high ρ i 0)⁻¹ (shot A F T ρ i) E 1 k q 0).pacify Real.log 1 k) (by unfold bounder; omega)
  apply Spline.Field.smul; exact (Spline.Field.add (Spline.Field.weaken (Spline.Field.ritualP _ 2 k) (by unfold bounder; omega)) (Spline.Field.weaken (Spline.Field.ritualP _ 0 k) (by unfold bounder; omega)))

/-- Fₖ producer also nominates a *finite real-path stencil* for each extra/drop render (T here f). Aggregate at anchor and move mask if needed with costs (RG03). Can truncate infinite path multiplicities before; this consumer is on nominated stencils. No mask change on failed Sunny without attachments. Gluing jet cert will be on total candidate in `frothP`, before period offer transfer. -/
structure Exposition (V : Trio.Offer G c) (f : ℝ × Positions (Uniform.Primary c G) → ℝ) (β : ℝ) (w k : ℕ) (r v : ℝ) : Prop where
  price (y : ℝ × Positions (Uniform.Primary c G)) (hy : y ∈ ball 0 r) : Brush k v 1 f y
  flat : FlatAt w f 0
  active (y:Positions (Uniform.Primary c G)) (hy: ‖y‖ < r) (hv : Boulevard.actual y∈sunny (G:=G) B') :
    stillA (Trio.froth V) (Boulevard.actual y) = (gStep β)⁻¹^w * f (gStep β,y)

lemma operation (V : Trio.Offer G c) (f : ℝ × Positions (Uniform.Primary c G) → ℝ)
    (h : Exposition B' V f β w k (d*gStep β) K) (hb : 0 < β) (hd : 1 < d) (ht:d*gStep β ≤ 1)
    (hr:n+w<k) (hx:j ≤ k) (y:Xs) (hy : ‖y‖ < d*b) (hu: Boulevard.actual y ∈ sunny B') :
    AuxStage.Points (ritual_fee w n K 0 d) ((d*b)⁻¹) b n j (stillA (Trio.froth V) ∘ Boulevard.actual) y (ritual f w) := by
  have hp:=Fare.gS β hb; have hz := h.price 0 (mem_ball_self (mul_pos (zero_lt_one.trans hd) hp.1))
  apply (ritual_P hr hx (hz.smaller hr.le).smooth h.flat hp.1 hd ht hy h.price (u:=0) (by rw [sub_self,zero_mul]; exact AuxCurtain.constant (u:=0) zero_le_one norm_zero.le)).adjust
  have hv: Continuous (fun x:Xs=> Boulevard.actual x) := by
    exact continuous_pi (fun i=> ((show Continuous (fun x:Bid.Dir G c=> represent x i) from (by unfold represent increment Exterior.collect; simp only [Pi.one_apply,mul_one]; exact G.lieExp_cont.comp (continuous_apply _)))).comp (ContinuousLinearEquiv.continuous _))
  refine Eventually.mono (inter_mem (hv.continuousAt.preimage_mem_nhds ((sky B').mem_nhds hu)) (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hy))) (fun y he=> h.active _ (mem_ball_zero_iff.mp he.2) he.1)

-- congruence test for RG02 producer (not itself WilsonX coefficients). test with exact β along step in Aux w. or produce via stronger flat covariances after winding. centred *both* sides.
def answer (α:ℝ) (q n : ℕ) (f':ℝ × Xs → ℝ) (w:ℕ):= aperture T A F ρ i E α q n+ritual f' w
lemma shelves (q n w : ℕ) (f' : ℝ × Xs→ℝ) : Spline.Field (bounder n q+n+w) n (answer T A F ρ i E α q n f' w):= Spline.Field.add (Spline.Field.weaken (records T A F ρ i E n q) (by omega)) (Spline.Field.weaken (Spline.Field.ritualP _ _ _) (by omega))

variable (f' : ℝ × Positions (Uniform.Primary c G) → ℝ)
-- Spline already stationary weighted. Cost Knee can buy average p_geo if includes all star sides.
def Certificate (q α' w n:ℕ) (α β u d:ℝ) :=
    let f := answer T A F ρ i E α q n f' w
    ∀ j ≤ n, ∀ i ≤ α', normJ i (headAt f (gStep β) j) 0 *(d*gStep β)^i ≤ u*gStep β^(n+1)

-- Proof core
lemma powers (α : ℝ) (hb : 0<β) (V : Trio.Offer G c)
    (h : Exposition B' V f' β w k (d*gStep β) K)
    (hq : Mate T B R e β) (hn: n+2<k) (hk: n+w < k) (hj:j ≤ k)
    (Y : BareRates.pre G σ C k) (hY:T.down.Bounds T.low σ C Λ) (hs : 1 ≤ M') (he : (Fintype.card (Uniform.Primary c G):ℝ)≤ M')
    (hd:1 < d) (ht : d*gStep β≤1)
    (hg : Certificate T A F ρ i E f' M (bounder n M + n + w) w n α β i' d)
    (x : Xs) (hx : ‖x‖ < d*gStep β) (hv : Boulevard.actual x ∈ sunny B')
    (h0 : Pushed A T F i ρ B β e E n k j M ((d*gStep β)⁻¹) J H 0)
    (hu : Pushed A T F i ρ B β e E n k j M ((d*gStep β)⁻¹) J H x) :
    Brush j (((2*H+ Bonus.baseFee Y T.low M' Λ |α| d n + ritual_fee w n K 0 d)+(n+1:ℕ)*(bounder n M + n + w+1:ℕ)*i') *b^(n+1)) ((d*b)⁻¹) (stillA (metricA T α R+Trio.froth V) ∘ Boulevard.actual) x:= by
  let W:=answer T A F ρ i E α M n f' w; let y:=gStep β; let z:=d*y
  have hM: stillA (metricA T α R+Trio.froth V) ∘ Boulevard.actual = stillA (metricA T α R) ∘ Boulevard.actual+ (stillA (Trio.froth V) ∘ Boulevard.actual) := by ext x; simp only [Function.comp_apply,Boulevard.stillA, Pi.add_apply]; ring
  rw [hM, parsed T B A F ρ i R e hq]
  have h := ((Spline.points_centred (hu.center) h0.center).add (Bonus.pricing T Y hY hs he hn α hb hd ht hj x hx)).add (operation B' V f' h hb hd ht hk hj x hx hv)
  let S' := centre (givenLog A T F ρ i B β e) + centre (Bonus.ember T α β ∘ Boulevard.actual) + (stillA (Trio.froth V) ∘ Boulevard.actual)
  have ht : Spline.Field (bounder n M+n+w) n W:= shelves T A F ρ i E M n w f'
  let b' : ℝ:= (bounder n M+n+w+1:ℕ)*(i'*b^(n+1))
  have hh i (he : i≤ n) : Brush j b' z⁻¹ (headAt W (gStep β) i) x:= by
    let L:= y⁻¹ • ContinuousLinearMap.id ℝ Xs
    apply Spline.all_taxes (f:=headAt W _ i) (n:=bounder n M+n+w) _ _ hx ‹_› (hg i he)
    exact Spline.smul ((ht i he).through L) (y^i)
  have hB := (Brush.spree (Finset.range (n+1)) _ _ h.pos (fun i hi=> hh i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))))
  rw [Finset.sum_const,nsmul_eq_mul,Finset.card_range] at hB
  let C₀ :ℝ:= 2*H+Bonus.baseFee Y T.low M' Λ |α| d n+ ritual_fee w n K 0 d
  have hP := (h.tail).gathering hB; apply hP.climb (le_of_eq ?_) le_rfl|>.shimmy _
  · change C₀*b^(n+1)+_=(C₀+_)*_; unfold b'; push_cast; ring
  exact Eventually.of_forall (fun k' : Xs=> (sub_add_cancel (S' k') (AuxStage.price W y n k')).symm)
end YM.RGComparison01.Pencils
