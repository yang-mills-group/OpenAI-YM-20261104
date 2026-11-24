import YM.LocalTaylorR2.Capstone.Ground
/-!
 # Numerical budget after full re-expression

 Stage-polynomial cost pinned by Decal. Control both *error* parts of
 Regular rung (`all Emit` and `Bouquet`--additional geometry charged).
 BEFORE clover projection and with later projection/reclosure costs reserved.
 Need user P+1 error only eventually in A.g; parameter ε arbitrary in (0,1].
 Note Recoil.Rail consumes p.clock.Stage; charge a negligible factor there or
 use the combined tariff here.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Capstone
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide Marlin Trio Lantern
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

variable {G : Gauge} (L : Side) (b : ℕ) (T : RG.Stage) (x : ℝ) (f : ℝ) (B:BudgetPoint)
local notation "Y" => Trio.fence b (radiusB x)
local notation "z"=> Trio.base b (radiusB x)
open CalendarStep Daisy.Charity.RG12 Recoil
open Time Tail

def stamps (i:Stars) := (2*(Fintype.card (Site (Y i)):ℝ))
def wagon:= Trio.oroW (Time.probe T) z (stamps b x)
def fare := 1+turnFee (Time.probe T)*(wagon b T x*Real.exp ((preExponent (Time.probe T))*coverTicket b))
variable (h: Time.Same T B) (u:ℝ)
include h
lemma tariff :
    f+turnFee B*(oroW B z (fun i=>2*(Fintype.card (Site (Y i)):ℝ)*f) * Real.exp (preExponent B*coverTicket b))= fare b T x*f:=by
  have hu: preExponent B=preExponent (Time.probe T):= by unfold preExponent Time.probe; dsimp only []; rw [h.2.2]
  have ht: turnFee B=turnFee (Time.probe T):= by unfold turnFee Time.probe; dsimp only []; rw [h.1,h.2.1]
  have hx: Trio.tilt B z=Trio.tilt (Time.probe T) z:=by unfold Trio.tilt Time.probe; dsimp only []; rw [h.1,h.2.1]
  have hp: oroW B z (fun i=>2*(Fintype.card (Site (Y i)):ℝ)*f)=wagon b T x*f:=by
    unfold wagon oroW; rw [Finset.sum_mul]; refine sum_congr rfl (fun i _=>?_); rw [hx]; unfold stamps; ring
  rw [hp,ht,hu]; unfold fare; ring
omit h
lemma waving : Rate G L 0 (wagon b T):=by
    let B:=Time.probe T; let hv:ℝ:=(2:ℝ)^B.order; have hp: Rate G L 0 (fun x=>Trio.tilt B (Trio.base b (radiusB x))):= (Bolt.times (Bolt.still hv) (Bolt.nod (Bolt.joins (Bolt.still 1) ((Trio.rows G L b).2.2.1)) _)).uses
    apply Trio.sparks G L (f:=fun i x=> |Slide.ray i| *(Trio.tilt B (Trio.base b (radiusB x))*stamps b x i)); intro i; simpa only [zero_add] using! ((hp.mul ((feeStars G L b i).mul_left 2)).mul_left |Slide.ray i|)
lemma fair : Rate G L 0 (Capstone.fare b T) := (Rate.const 1).add (((waving L b T (G:=G)).mul_right _).mul_left _)
lemma fare_pos : 0 ≤ Capstone.fare b T x:=by
   have h:0 ≤ wagon b T x:=by
     unfold wagon oroW; apply sum_nonneg; intro i _; unfold Trio.tilt stamps; positivity
   unfold fare; have h₀:= turnFee_pos (Time.probe T); positivity
-- include soft loss (threshold^-1) SOOT separately through Rail. and regular reset. two Q resets not needed? pay w=combined *base≤ ... log.
def fA (G:Gauge)(T:RG.Stage):ℝ:=1+Time.base G T
structure Errands (G:Gauge)(L:Side)(b:ℕ)(T:RG.Stage)(x ε:ℝ) : Prop where
    horizon : fA G T * Capstone.fare b T x ≤ betaF G x L ^ ε
    small : betaF G x L ^ (-(3/2):ℝ) ≤ (δE x)/2


lemma upkeep : ∀ᶠ x in atTop, betaF G x L ^ (-(3/2):ℝ) ≤ (δE x)/2:=by
   have hx : (∀ᶠ x:ℝ in atTop, (2:ℝ) ≤ betaF G x L ^ (3/2-11/10:ℝ)) := ((Rate.const (G:=G) (L:=L) 2) (3/2-11/10:ℝ) (by norm_num)).mono fun i h=>by simpa using h
   filter_upwards [eventually_gt_atTop (0:ℝ),hx,(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hx hz hy
   have h0 : 0 < betaF G x L:= zero_lt_one.trans_le hy
   have hh: δE x=x^(-(11/10):ℝ):=by unfold δE Clock.gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hx.le,← Real.rpow_mul hx.le]; norm_num
   rw [hh,le_div_iff₀ zero_lt_two]
   calc _ ≤ betaF G x L ^(-(3/2):ℝ) * betaF G x L ^(3/2-11/10:ℝ) := mul_le_mul_of_nonneg_left hz (Real.rpow_nonneg h0.le _)
        _ ≤ _:= by rw [← Real.rpow_add h0]; norm_num; exact Real.rpow_le_rpow_of_nonpos hx (le_add_of_nonneg_right (YM.Work.E04.shift_nonneg G L)) (by norm_num)

def checkD (G:Gauge): Daisy.Charity.RG12.Decal G where
   rub P Q E L W μ o U i x:= Errands G L Q.halo U x (CalendarStep.loss i)
   good P Q E:= by
     refine ⟨0,fun L _ _ _ _ U j _ _ _=>?_⟩
     have hv:Rate G L 0 (fun x=> fA G U*Capstone.fare Q.halo U x) := (Capstone.fair L Q.halo U (G:=G)).mul_left _
     filter_upwards [hv (CalendarStep.loss j) (by unfold CalendarStep.loss; positivity),upkeep (G:=G) L] with x hx h; exact ⟨(le_abs_self _).trans hx,h⟩
lemma limiting (H: Errands G L b T x u)(hu : Time.Same T B)(hy:1≤betaF G x L)(hv: 3*u ≤ f)(l:ℕ) :
    let g:=Capstone.fare b T x * betaF G x L ^ (requested (l+1) u)
    (g≤ betaF G x L ^ requested (l+1) f ∧ regularNeed G B T.clip T.width T.paths 0 g ≤ betaF G x L ^ requested (l+1) f) ∧
    (3 ≤ l → f ≤ 1 → betaF G x L ^ requested (l+1) f ≤ δE x / 2):=by
   intro g; let U:=betaF G x L; have h:=zero_lt_one.trans_le hy
   have hg:0≤g:= mul_nonneg (Capstone.fare_pos b T x) (Real.rpow_nonneg h.le _); have hr:= (Time.base_nonneg G T).1
   have ht : fA G T*g ≤ U^requested (l+1) f:=by
     unfold g; rw [← mul_assoc]; apply (mul_le_mul_of_nonneg_right H.horizon (Real.rpow_nonneg h.le _)).trans; rw [← Real.rpow_add h]; apply Real.rpow_le_rpow_of_exponent_le hy; unfold requested; linarith
   refine ⟨⟨?_,?_⟩,?_⟩
   · exact (le_mul_of_one_le_left hg (show 1≤fA G T from by unfold fA; linarith)).trans ht
   · rw [Time.table G T hu, abs_zero,zero_mul,mul_zero,add_zero]; exact (mul_le_mul_of_nonneg_right (show Time.base G T≤fA G T from by unfold fA; linarith) hg).trans ht
   intro hl hh; apply le_trans _ H.small; apply Real.rpow_le_rpow_of_exponent_le hy; unfold requested; push_cast; linarith only [hh, show (3:ℝ)≤l from by exact_mod_cast hl] -- price ~ χ^(-l/?)
end YM.LocalTaylorR2.Capstone
