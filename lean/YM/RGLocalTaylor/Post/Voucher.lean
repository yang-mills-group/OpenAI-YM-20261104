import YM.RGLocalTaylor.Post.Lease
import YM.RGLocalTaylor.Post.Law
import YM.RGLocalTaylor.Consumer.Power
/-! # Actual coupled-stage post-reset costs

The coefficient recipe's `M` effective-exponent power oversampling ratio
8 units buys 7 g-powers (mod internal loss). (See theorem: 7*(M-2)≥8*p.)
SPECIFIC POST-BLOCK BILL: in comparison to May1/Cash local prices, E support
costs from full E6 → Trio reconstruction, turnFee incl rotations, scalar,
also the final projection & kinetic estimator (even return beta difference
before multiplying by g²), bought from three more powers of radius. Keep
any other fixed-power loss in choosing this integer. Threshold independent
of cutoff & volume; not asserting it can be polynomial in M etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Post.Leasing
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {k : ℕ} {Q: YM.ConnectedActivityE6.Target G P}
open Mallow Daisy.Charity.RG12 Read.Pane
set_option quotPrecheck false
variable (G) (X : RG.Stage) (j : ℕ) (b : ℝ)

-- Locator fee before purchases
def orientPrice := (∑ i:Stars,|Slide.ray i| * (((2:ℝ)^X.order*(1+(Trio.base j (radiusB b):ℝ))^(X.power*X.order)) *
    (2*(Fintype.card (Site (Trio.fence j (radiusB b) i)):ℝ))))*Real.exp ((Trio.stout X)*coverTicket j)
lemma orientExact {p : BudgetPoint} (hA : Time.Same X p) (hb : p.B=radiusB b) (v : ℝ):
    Read.Pane.locator j p v= orientPrice X j b*v:= by
  unfold Read.Pane.locator orientPrice preExponent Trio.oroW Trio.tilt Trio.stout; simp_rw [site_card]; rw [hA.1,hA.2.1,hA.2.2,hb]; rw [mul_right_comm (∑ u,_:ℝ),sum_mul _ _ v]; apply congr_arg₂ _ _ rfl; exact sum_congr rfl (fun i _=> by ring)
lemma orientNonneg : 0≤orientPrice X j b:= by unfold orientPrice; positivity

def licensePrice := 1 + Height.away X * orientPrice X j b

def regulator := (1+b) * licensePrice X j b + (ballCost (Meadow.studio j (radiusB b)):ℝ)+ VerifiedReset.Time.base G X * licensePrice X j b
lemma immune : 0≤ licensePrice X j b:= by
  unfold licensePrice; have hv:= orientNonneg X j b; have hP: 0≤ Height.away X:= by unfold Height.away Push.Local.turnCost; positivity
  positivity

variable (L)
lemma times : ∀ᶠ x in atTop, (regulator G X j x) ≤ (Mayer.arcRadius G L x)^ (3:ℕ):= by
  have he: Rate G L 0 (fun y=> (2:ℝ)^X.order*(1+(Trio.base j (radiusB y):ℝ))^(X.power*X.order)):= by
    simpa only [zero_mul] using! (((Rate.const (1:ℝ)).add (Trio.rows G L j).2.2.1.uses |>.pow (X.power*X.order)).mul_left _)
  have hQ': Rate G L 0 (orientPrice X j):= Rate.mul_right (w:=_) (c:=_) (Trio.sparks G L (f:=fun i x=> |Slide.ray i| *(( (2:ℝ)^X.order*(1+(Trio.base j (radiusB x):ℝ))^(X.power*X.order)) * (2*(Fintype.card (Site (Trio.fence j (radiusB x) i)):ℝ)))) (fun i=>by simpa only [zero_add] using! ((he.mul ((Trio.feeStars G L j i).mul_left 2)).mul_left _)))
  have hP: Rate G L 0 (licensePrice X j):=(Rate.const 1).add (hQ'.mul_left _)
  let v:=-G.slopeConstant*Real.log L.val; have hQ: Rate G L 1 (fun x=>x):= by
    apply Rate.congr (Rate.hat (G:=G) (L:=L)|>.add ((Rate.const v).weaken zero_le_one)); filter_upwards with x; unfold betaF v; ring
  have hν : Rate G L 1 (regulator G X j):= Rate.add (Rate.add (by simpa only [add_zero] using! ((((Rate.const 1).weaken zero_le_one).add hQ).mul hP)) ((Trio.balls G L (Trio.rows G L j).1).weaken zero_le_one)) ((hP.mul_left _).weaken zero_le_one)
  filter_upwards [(Work.E09.betaF_growth G L).eventually_gt_atTop 0,hν (Mayer.height * ↑(3:ℕ)) (by norm_num [Mayer.height])] with x hx he
  unfold Mayer.arcRadius; rw [← Real.rpow_mul_natCast hx.le]; exact (le_abs_self _).trans he

def dial : Decal G where
  rub _P Q _ L _ _ _ h _ x:= 0 < x ∧ (regulator G h Q.halo x) ≤ (Mayer.arcRadius G L x)^ (3:ℕ)
  good _P Q _R:= ⟨0,fun L _ _ _ _ h _ _ _ _ => (eventually_gt_atTop _).and (times G L h Q.halo)⟩

def receipt (G:Gauge):Decal G:= (Mayer.decal G).paired (dial G)
variable {X j b G}
lemma projectionFee (p:BudgetPoint) (hA : VerifiedReset.Time.Same X p) (u:ℝ) : regularNeed G p X.clip X.width X.paths 0 u= VerifiedReset.Time.base G X*u := by
  rw [Time.table G X hA]; ring_nf
private lemma eff_beta (hb : 0<b) : (Pressure.temp b ^ 2)⁻¹ ≤ b := by
  unfold Pressure.temp; let y:= Real.sqrt b; let f:= Real.exp ((Real.log (Real.log b))^2); have hF:1≤f:= Real.one_le_exp (sq_nonneg _)
  have hy:0<y:=Real.sqrt_pos.mpr hb
  simp only [mul_pow,inv_pow, inv_inv, Real.sq_sqrt hb.le,mul_inv_rev]
  exact mul_le_of_le_one_left hb.le (by apply inv_le_one_of_one_le₀; exact one_le_pow₀ hF)
-- dial consequences
variable (G) (X j b)
lemma settles {p : BudgetPoint} (hA:Time.Same X p)(ht:p.threshold=Pressure.temp b)(hk:p.B=radiusB b)(hw:turnFee p=Height.away X)(hb:0<b)
    (hl: regulator G X j b ≤ (Mayer.arcRadius G L b)^ (3:ℕ)) :
    licensePrice X j b=(1+turnFee p*Read.Pane.locator j p 1) ∧
      (p.threshold^2)⁻¹*licensePrice X j b ≤ (Mayer.arcRadius G L b)^(3:ℕ) ∧
      (ballCost (Meadow.studio j (radiusB b)):ℝ)+ licensePrice X j b ≤ (Mayer.arcRadius G L b)^(3:ℕ) ∧
      VerifiedReset.Time.base G X * licensePrice X j b ≤ (Mayer.arcRadius G L b)^ (3:ℕ) := by
  have hr: 0≤ licensePrice X j b := immune X j b
  have h:= Time.base_nonneg G X|>.1; have hz:= Nat.cast_nonneg (α:=ℝ) (ballCost (Meadow.studio j (radiusB b)))
  unfold regulator at hl; rw [orientExact X j b hA hk,ht,mul_one,hw]; refine ⟨rfl,(mul_le_mul_of_nonneg_right (eff_beta hb) hr).trans ?_,?_,?_⟩ <;> nlinarith only [hl,mul_nonneg h hr,hz,mul_nonneg hb.le hr,hr]
end YM.RGLocalTaylor.Post.Leasing
