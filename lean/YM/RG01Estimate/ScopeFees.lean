import YM.RG01Estimate.HomeAwards
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Ninety
/-!
 # When the bets buy quality. At any stage t. BEFORE moving P.
 Includes spare powers for Π curvature equality on auxiliary. Retains p+'. Order
 dictated by R for ordinary stage. All sums budgeted before curvature reset.
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
variable {G:Gauge}{L:Side}
section bills
-- R is desired positive budget power (typically r+1) not Micro Taylor order. `d≤ κ_poly`.
-- chosen orientation templates transcript.
def goalK (R b:ℕ)(f d h z y K:ℝ) := (2:ℝ)*((f+d)+ ((R+2:ℕ):ℝ)*h)*z+ 2*(K*y)+(0:ℝ)*b
def stakesR (N:RG.Stage)(b:ℕ)(f: Stars→ℝ):= ∑ i:Stars,|ray i| * ((2:ℝ)^N.order*((1+(b:ℝ))^(N.power*N.order))*f i)
def sharesR (N:RG.Stage)(b:ℕ)(f:Stars→ℝ) (Q:ℝ) := stakesR N b f*Real.exp ((N.supportExponent+3)*Q)
lemma lasts (f h g d y K: ℝ→ℝ)(hv:Cookie G L f)(hh:Cookie G L h)(hg:Cookie G L g)(hd:Cookie G L d)(hy:Cookie G L y)(hk:Cookie G L K)(R b:ℕ) : Cookie G L fun x=> goalK R b (f x) (d x) (h x) (g x) (y x) (K x):= by
   let Q:= ((Cookie.const (2:ℝ)).pays (hv.joins hd|>.joins ((Cookie.const (↑(R+2):ℝ)).pays hh))).pays hg
   exact Q.joins ((Cookie.const (2:ℝ)).pays (hk.pays hy)) |>.joins (Cookie.const _)
-- finite stars sums
lemma stake_cost {p:Stars→ℝ→ℝ} (N:RG.Stage)(hv:∀ i,Cookie G L (p i)) (b:ℝ→ℕ)(hp:Cookie G L (fun x=>(b x:ℝ)))(Q:ℝ) : Cookie G L fun x=> sharesR N (b x) (fun i=>p i x) Q:= by
   apply Cookie.pays _ (Cookie.const _)
   let V (x:ℝ) := fun i: Stars=> (|ray i| * ((2:ℝ)^N.order*((1+(b x:ℝ))^(N.power*N.order))*p i x))
   have he (i:Stars) : Cookie G L (fun x=> V x i):= (Cookie.const _).pays (((Cookie.const _).pays (((Cookie.const 1).joins hp).pow _)).pays (hv _))
   change Cookie G L fun x=> (∑ i:Stars, V x i)
   have ht (s:Finset Stars) : Cookie G L fun x=>∑ i∈s,V x i:= by
      induction s using Finset.induction_on with
      | empty => simp only [sum_empty]; exact Cookie.const _
      | @insert x s hs ih=> simp only [sum_insert hs]; exact (he _).joins ih
   exact ht Finset.univ
lemma tilt_collected (B:BudgetPoint)(N:RG.Stage)(R:ℕ)(g:Stars→ℝ)(z:ℕ) (β K:ℝ) (p:Stars→ℝ)(h: B.order=N.order)(hx:B.power=N.power)(he:B.supportExponent=N.supportExponent)(hp: ∀ i,p i≤ (gStep β)^R*g i):
    Trio.oroW B z p *Real.exp (preExponent B*K) ≤ (gStep β)^R * sharesR N z g K := by
   unfold Trio.oroW Trio.tilt; rw [h,hx,show preExponent B=N.supportExponent+3 from congr_arg₂ (·+·) he rfl]
   unfold sharesR; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; unfold stakesR; rw [Finset.mul_sum]; refine sum_le_sum fun i hi=>?_ ; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hp i) (by positivity)) (abs_nonneg _)); ring_nf; simp
lemma prize_caught (R b:ℕ){β V σ v' δ θ y m q h z K n:ℝ} (he:0<β)(hm:0 ≤ m)
    (hv: V ≤  v')(hh:σ  ≤  θ)(hX:0  ≤  v')(hT:0 ≤  θ)(hp:0 ≤  q)(hr:0 ≤  h)(hC:0 ≤ n)(hδ: δ ≤  (gStep β)^(R+2)*h)
    (hM:m ≤  z)(hk:n ≤  K)(hq:q  ≤  (gStep β)^R*y):
     prize R β V σ δ m q n ≤  (gStep β)^R*goalK R b v' θ h z y K := by
   unfold prize goalK; rw [zero_mul,add_zero,mul_add (gStep β^R)]
   have hb:= (Fare.gS β he); have hZ :=hm.trans hM; apply add_le_add
   · let b:=gStep β; have hz:0<b:=hb.1; let s:= β*((↑(R+2):ℝ)*δ)
     have hs:s ≤  b^R*((↑(R+2):ℝ)*h):= by
       unfold s; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ (by positivity : 0  ≤  (↑(R+2):ℝ))) he.le).trans_eq
       rw [pow_add]; unfold b; linear_combination ((gStep β)^R *((↑(R+2):ℝ)*h))*hb.2
     apply le_trans (mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hv (pow_pos hb.1 R).le) (mul_le_mul_of_nonneg_left hh (pow_pos hb.1 R).le)) hs) (by positivity : (0:ℝ) ≤ 2)) hM hm (by unfold b ; positivity)) (le_of_eq ?_)
     unfold b; ring
   apply (mul_le_mul_of_nonneg_left (mul_le_mul hk hq hp (hC.trans hk)) (by positivity : (0:ℝ) ≤ 2)).trans_eq; ring
-- cost sculpt keeping v≥ 0 & expos
lemma census_cost {p:ℕ} (i:Stars) : Cookie G L (fun x=> (Fintype.card (Site (Trio.fence p (radiusB x) i)):ℝ)):= by
  have he:= (Trio.rows G L p).2.1
  let f x := (tent p (radiusB x):ℝ)
  let g x:=2*(f x+i.val); have hg:Bolt G L g:= (Bolt.still 2).times (he.joins (Bolt.still _))
  refine Cookie.copy (Cookie.bolt (hg.nod 4)) ?_; filter_upwards with x; rw [site_card]; symm; change (g x)^4= ((↑((2*(tent p (radiusB x)+i.val))^4:ℕ)):ℝ); unfold g f; norm_cast
end bills
end YM.RG01Estimate.Award
