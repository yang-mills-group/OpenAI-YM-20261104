import YM.RG01Estimate.Repark
import YM.RG01Estimate.CrestForecast
import YM.RG01Estimate.TrunkWeight
/-! # Stage bills required for acceleration. No loans from Period census. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Precise
open PhysicalNext.Repeat
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior Gauge Set
open Matrix Finset Push AbsoluteSums Gas Extra.Iteration Extra.Iteration.Calibration Bid Bloch Laurent UVNext UVNext.PricedKernels
open Pressure AnalyticBridge VerifiedReset Collection Quotes PriceCompiler Uniform RG.Shoot
open ConnectedActivityE6 Testing SectorMeasure Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural Macrame
open Sienna Token Lantern Lapis Shellac Fare Planned.JetPort Pane
open Laplace Courtyard Receipt ConnectedActivityE6.Coat Roost Boulevard Award
open Evoc Deck AbsoluteSums.Animals Board Promise Slide Trio
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}
   {N m d n i j r ℓ:ℕ}
lemma passport_hub (m n t:ℕ) : ∃ p≥t, ∀ B:ℕ,1 ≤ B→ house t B (m*B) (Fate.steps n)+optic t B (m*B)+5 ≤ Meadow.studio p B ∧ Meadow.studio t B≤ Meadow.studio p B := by
   let q:=house t 1 m (Fate.steps n)+optic t 1 m+5
   have he (B:ℕ)(hB:1≤B): optic t B (m*B) ≤ optic t 1 m * B := by unfold optic Mint.width; nlinarith
   refine ⟨q+t,Nat.le_add_left ..,fun B hB=> ?_⟩
   have hf := he B hB
   have h':house t B (m*B) (Fate.steps n) ≤ house t 1 m (Fate.steps n)*B:= by
       unfold house; apply (Nat.add_le_add (Nat.mul_le_mul_left _ hf) (Nat.mul_le_mul_left _ (show 4*optic t B (m*B)+2≤(4*optic t 1 m+2)*B from by nlinarith))).trans_eq
       ring
   constructor
   · have hV : house t B (m*B) (Fate.steps n)+optic t B (m*B) +5 ≤ q*B:= by unfold q; rw [Nat.add_mul,Nat.add_mul]; nlinarith only [hB,hf,h']
     apply hV.trans; unfold Meadow.studio Meadow.roomSize Mint.width; nlinarith
   unfold Meadow.studio Meadow.roomSize Mint.width
   nlinarith

variable (G:Gauge)(L:Side)
local notation "z" => fun t=>Trio.base ℓ (radiusB t)
local notation "Z" => fun t=>Trio.fence ℓ (radiusB t)

def crow (ℓ:ℕ)(Y:ℝ)(t:ℝ):= ∀ B:BudgetPoint,B.threshold=Pressure.temp t → B.threshold ≤2*Pressure.fiery G t L →
     ∀ β:ℝ,betaF G t L / 2 ≤ β→ β≤2*betaF G t L → ∀ c:Side, 2*Trio.base ℓ (radiusB t)<c.val → ∀ (x:Site c)(V:Config G c), Healthy B.threshold (neighbors (Trio.base ℓ (radiusB t)) x) V → ∀ i:Stars,
       ∃ (u:Site (Trio.fence ℓ (radiusB t) i)→G.El) (p:Positions (Uniform.Primary (Trio.fence ℓ (radiusB t) i) G)), actual (gStep β • p)= gauge u (Slide.shape (Trio.pad (Y:=Trio.fence ℓ (radiusB t)) (w:=Trio.tent ℓ (radiusB t)) (fun _ => rfl) i) x V)∧ ‖p‖+1<Y

lemma opens : ∃ Y:ℝ→ℝ,Cookie G L Y∧(∀ t,1<Y t)∧∀ᶠ t in atTop,crow G L ℓ (Y t) t := by
   obtain ⟨f,hf,hQ⟩:= Receipt.openings G L z (Cookie.bolt ((Trio.rows G L ℓ).2.2.1))
   refine ⟨fun t=>|f t|+2,(Award.cookie_abs hf).joins (Cookie.const _),fun t=>?_,?_⟩; · linarith only [abs_nonneg (f t)]
   filter_upwards [hQ] with t ht B hp hB β hx h C e x V hω i
   have he: (Trio.tent ℓ (radiusB t)+i.val)+1 ≤ z t:= by dsimp only [Trio.base]; have hh:=i.isLt; omega
   obtain ⟨u,p,H,H'⟩:= ht _ hB C ((Z) t i) x _ le_rfl e he _ hx h V hω
   exact ⟨u,p,H,H'.trans (by linarith only [le_abs_self (f t)])⟩

section cost
-- polynomial wagers & conversion. authorization Register.All
-- on Auxiliary caps even. `next_bound` includes 2^r margin.
lemma spill_rate : ∀ᶠ t in atTop, ∀ β:ℝ,betaF G t L/2 ≤ β→β≤2*betaF G t L → betaF G t L ^ (-Fate.aim r- (1/64:ℝ)) ≤ gStep β^(r+1) := by
   have he:= (Rate.power (G:=G) (L:=L) (a:=-(1/64))|>.mul_right ((2:ℝ)^(r+1))).below (by norm_num) 1 zero_lt_one
   filter_upwards [he, Delay.shift_pos G L] with t ht hZ β hf hβ
   have hp : 0<β:= (half_pos hZ).trans_le hf; have hb:= (reverse_g t β hZ hp hβ)
   let s:= betaF G t L; let p:= (Real.sqrt s)⁻¹; have hg:(s)^(-Fate.aim r)=p^(r+1):= by unfold p Fate.aim; rw [Real.sqrt_eq_rpow, ←Real.rpow_neg (x:=s) hZ.le, ← Real.rpow_mul_natCast hZ.le]; ring_nf; rfl
   change s^_≤_; rw [sub_eq_add_neg,Real.rpow_add (x:=s) hZ,hg,mul_comm]
   apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0 ≤ p from inv_nonneg.mpr (Real.sqrt_nonneg _)) hb (r+1)) (Real.rpow_nonneg hZ.le _))
   rw [mul_pow,← mul_assoc]; exact mul_le_of_le_one_left (pow_nonneg ((gS β hp).1.le) _) ((le_abs_self _).trans ht)
lemma affix_cost (d:ℕ) : ∀ᶠ t:ℝ in atTop,Real.exp ((Trio.paySide G L d t:ℝ)* incomingE G L t) ≤ Real.exp 1 := by
   have hh: Rate G L (-(11/10)) (fun t=> incomingE G L t) := by apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with t ht; unfold incomingE; rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le, ← Real.rpow_mul ht.le]; norm_num
   filter_upwards [((Trio.circles G L d).uses.mul hh).below (by norm_num) 1 zero_lt_one] with t ht; exact Real.exp_le_exp.mpr ((le_abs_self _).trans ht)
lemma lofts (Y:ℝ→ℝ)(h:Cookie G L Y)(j:ℕ) : ∃ p:ℝ→ℝ,(Cookie G L p ∧ (∀ t,0 ≤ p t) ∧ ∀ᶠ t in atTop,∀ P:BudgetPoint,P.order=j→Loft t (Y t) P L G (p t)):= by
   obtain ⟨W,hW,H⟩:=talk j Y h; refine ⟨fun t=> |W t|, cookie_abs hW, fun t=> abs_nonneg _,?_⟩; filter_upwards [H] with t ht P h; have h:= ht P h
   refine ⟨?_,h.extend⟩; intro c x β v E _ _ _ F b hp hb he hX hY hF hΦ l hl h
   exact ((ht P ‹P.order=j›).pay c x β v E F hp hb he hX hY hF hΦ l hl h).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hΦ.nonneg)
end cost
end YM.RG01Estimate.Precise
