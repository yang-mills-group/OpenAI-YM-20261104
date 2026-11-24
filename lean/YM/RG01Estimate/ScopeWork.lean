import YM.RG01Estimate.ScopeFees
/-!
 # Purchases for aligned main sets. Rate hypotheses only for spent (non-η) buys.
 All else Cookie (outputs willing to retain sharper).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Award
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Animals PhysicalNext.Repeat.Fare Sienna Conditioning Token Office Courtyard RealTaylor
open Laplace Laplace.Stellar Series Boulevard Blaze.Frond Exterior Abacus Slide Trio Promise
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Geo Footprint Finset
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{L:Side} (p R: ℕ)(N:RG.Stage)

-- permitted volumes in geometry bill; maximum by tiler (r-studio)
local notation "r₀" => fun i=> (Meadow.studio p (radiusB i))
local notation "z₀" => fun i=> Trio.base p (radiusB i)
local notation "k₀" => fun i=> 2*z₀ i
local notation "Y" => fun i=> Trio.fence p (radiusB i)
local notation "Q" => coverTicket p
-- loose mass o(g^??) only burns Hit. input mSet preset. 
lemma cookie_abs {f:ℝ→ℝ}(h:Cookie G L f):Cookie G L (fun x=> |f x|):= by obtain ⟨a,b,h,h'⟩:=h.invoice; refine ⟨a,b,h,?_⟩; simpa only [abs_abs] using h'
lemma steam {t : ℝ} (f:ℝ→ℝ)(ht:t< -(1/8:ℝ))(hf:Rate G L t f) : ∀ᶠ x in atTop, ∀ (B:BudgetPoint)(sf y β γ D : ℝ)(R:ℕ) (X:∀ i:Stars, Position (G:=G) B x y β γ D (Trio.fence p (radiusB x) i) L (Meadow.studio p (radiusB x)) R), sf ≤ f x → (∀ i,(X i).e'≤ f x) → B.supportExponent=N.supportExponent →
      incomeK B x L y β γ (2*Trio.base p (radiusB x)) D X (coverTicket p) sf ≤ (betaF G x L)^(-(1/8:ℝ)):= by
   let r:= r₀; let z:= z₀; let k:=k₀
   let f' x:= (ballCost (r₀ x):ℝ)*f x
   let I x:= Rack.beans (c:=Y x) (r x) (f x) (fun _=>f' x)
   have hp: Rate G L t f':= ((balls G L (Trio.rows G L p).1).mul hf).weaken (by simp)
   have hI : Rate G L t I:= Rate.add (hp.add hp) (sparks G L fun i=> ((Trio.feeStars G L p i).mul (hp.add hp)|>.mul_left |ray i|).weaken (by simp))
   have he: Rate G L t (fun x=> ((ballCost (k x):ℝ)* I x)*Real.exp ((N.supportExponent+1+1)*Q)):= ((balls G L ((Trio.rows G L p).2.2.2)).mul hI|>.mul_right _).weaken (by simp)
   filter_upwards [he _ ht] with t hh B sf y β γ D R X hV hs hB
   apply le_trans _ ((le_abs_self _).trans hh); unfold incomeK Marlin.tithe; rw [hB]
   apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
   let z' := (r₀ t); have hU (q:ℝ)(hy:q≤ f t): (ballCost z':ℝ)*q≤ f' t:= mul_le_mul_of_nonneg_left hy (Nat.cast_nonneg _)
   apply add_le_add (add_le_add (hU _ hV) (hU _ hV))
   apply sum_le_sum; intro i hi; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
   exact mul_le_mul_of_nonneg_left (add_le_add (hU _ (hs i)) (hU _ (hs i))) (Nat.cast_nonneg _)

def muralBill (G:Gauge) (L:Side) (p R:ℕ)(N:RG.Stage) (V σ h m y:ℝ→ℝ) (x:ℝ) := let f i:= goalK R p |V x| |σ x| |h x| |m x| |y x| (Fintype.card (Site (Trio.fence p (radiusB x) i)))
    sharesR N (Trio.base p (radiusB x)) f (coverTicket p) + (0:ℝ)*(0*betaF G x L)

variable {x:ℝ}{V σ h m y:ℝ→ℝ}
lemma stake_estate (hv:Cookie G L V)(h':Cookie G L σ)(hr:Cookie G L h)(hm:Cookie G L m)(hy:Cookie G L y):Cookie G L (muralBill G L p R N V σ h m y):= by
   unfold muralBill; simp only [zero_mul,add_zero]; exact stake_cost N (fun i=> lasts (fun x=>|V x|) _ _ _ _ _ (cookie_abs hv) (cookie_abs hr) (cookie_abs hm) (cookie_abs h') (cookie_abs hy) (census_cost ..) R p) _ (Cookie.bolt (Trio.rows G L p|>.2.2.1)) _ -- V.abs

lemma dues (B:BudgetPoint)(s y' β γ D : ℝ) (X:∀ i:Stars, Position (G:=G) B x y' β γ D (Trio.fence p (radiusB x) i) L (Meadow.studio p (radiusB x)) R)
     (hr : 0<β) (he:B.order=N.order)(hP:B.power=N.power)(hB:B.supportExponent=N.supportExponent)(hs:0 ≤ s)(hm:s ≤ m x) (hv:∀ i,(X i).y'≤ V x) (hq:∀ i,(X i).V ≤ σ x)
      (hx:∀ i,(X i).q' ≤ (gStep β)^R*y x)(hζ:∀ i,(X i).μ ≤ (gStep β)^(R+2)*h x) :
      funds B x L y' β γ (Trio.base p (radiusB x)) D X (coverTicket p) s ≤ (gStep β)^R * muralBill G L p R N V σ h m y x:= by
   have ht:0<gStep β:=(Fare.gS β hr).1
   rw [muralBill,zero_mul,add_zero]; unfold funds; apply tilt_collected _ N R _ _ _ _ _ he hP hB
   intro i; have hV:0≤ (X i).q':=by obtain ⟨F,h',H⟩:= (X i).above; exact Cost.nonneg (h' 0)
   exact prize_caught R p hr hs ((hv i).trans (le_abs_self _)) ((hq i).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _) hV (abs_nonneg _) (Nat.cast_nonneg _) ((hζ i).trans (mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg ht.le _))) (hm.trans (le_abs_self _)) le_rfl ((hx i).trans (mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg ht.le _)))
end YM.RG01Estimate.Award
