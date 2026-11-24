import YM.Juniper.Voucher.Seat
import YM.Juniper.Gauze.Revenue
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Voucher
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {i j :ℕ}
open UVExtension Oriel Charted Clock Instrument Bright LocalAtlas Gauze
variable {K:Targets X.p X.K}{D:Rolls X.p} (j i : ℕ)
-- ask genuine internal precision step `x^-r` relative to pre-E credit *rim`, conclude chip receipts. Coupling ≤ (sqrt x)^-1. Handles unrelated representatives! address exponent premium already paid before requesting.
def powerUp (r:ℕ) := 4*r+9
local notation "P"=> X.p.profile i
local notation "L"=> D.L j
local notation "J"=> trek (K j i).halo (mast j)

def PricedForce (x:ℝ) (D:Rolls X.p) (K:Targets X.p X.K) (j i:ℕ):Prop:= let p:= X.p.profile i; let B:= Height.away p; let l:= D.L j; let T:= trek (K j i|>.halo) (mast j)
   gold G l x+B*(planks G l T p x*Real.exp (stout p*coverTicket T)) ≤ rim*(Time.credit G p*δE x) ∧ ∀ r:ℕ, powerUp r ≤ j →
      (betaK G l (powerUp r) j x ≤ rim*(x^r)⁻¹*(Time.credit G p*δE x))∧(4*x^j)⁻¹ ≤ rim*(x^r)⁻¹

lemma salary {r:ℕ} (h:powerUp r≤j): ∀ᶠ x in atTop, (betaK G L (powerUp r) j x ≤ rim*(x^r)⁻¹*(Time.credit G P*δE x))∧(4*x^j)⁻¹ ≤ rim*(x^r:ℝ)⁻¹:=by
   have hf: climbed j (powerUp r) < -((11/10:ℝ)+r):= by
      unfold climbed rampK LocalAtlas.leaf leew vow powerUp; push_cast; have ht: (j+1:ℝ)⁻¹≤1:=inv_le_one_of_one_le₀ (by simp); linarith only [ht,Nat.cast_nonneg (α:=ℝ) r] -- 4*... yes -4.375+2 = -2
   have he: Rate G L (climbed j (powerUp r)) (betaK G L (powerUp r) j):= Rate.power
   have hp:=Time.credit_pos G (P); have hP:0<rim:=by norm_num [rim]
   filter_upwards [Sienna.contraction G L (a:=1) (b:=rim*Time.credit G (P)) (by positivity) he hf,Delay.shift_pos G L,eventually_gt_atTop (1:ℝ),eventually_ge_atTop (1/rim:ℝ)] with x hx hk hu hr
   have h₀:0<x:=zero_lt_one.trans hu; let v:=betaF G x L; have hV:x ≤ v:= le_add_of_nonneg_right (Work.E04.shift_nonneg G L)
   constructor; swap
   · rw [← div_eq_mul_inv]; apply (le_div_iff₀ (by positivity)).mpr; rw [mul_comm, ← div_eq_mul_inv]; refine (div_le_iff₀ (by positivity)).mpr ?_; have hR: r+1 ≤ j:= by unfold powerUp at h; omega
     have hm := pow_le_pow_right₀ hu.le hR; rw [pow_succ] at hm; have hv:1≤x*rim:= (div_le_iff₀ hP).mp hr; nlinarith only [mul_le_mul_of_nonneg_left hv (show 0≤x^r by positivity), mul_le_mul_of_nonneg_left hm hP.le,show 0<rim*x^j by positivity]
   rw [one_mul] at hx; have ht:0< (11/10:ℝ)+r:= by positivity
   refine hx.le.trans ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos h₀ hV (by linarith)) (mul_nonneg hP.le hp.le)).trans_eq ?_)
   have hh: δE x=x ^(-(11/10:ℝ)) := by unfold δE Clock.gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg h₀.le,← Real.rpow_mul h₀.le]; norm_num
   rw [hh,neg_add,Real.rpow_add h₀, Real.rpow_neg h₀.le,Real.rpow_neg h₀.le,Real.rpow_natCast]; ring
lemma sullied : ∀ᶠ x in atTop, PricedForce x D K j i:= by
   have hp : ∀ᶠ x in atTop,∀ r∈ Finset.range (j+1),powerUp r ≤ j →(betaK G L (powerUp r) j x ≤ rim*(x^r)⁻¹*(Time.credit G P*δE x))∧(4*x^j)⁻¹ ≤ rim*(x^r)⁻¹:= (eventually_all_finset _).2 fun i' _=> (eventually_imp_distrib_left.mpr (fun h=> salary j i h)) -- lemma syntax check
   filter_upwards [hp,trophy (C:=K) (j:=j) (i:=i) D (show 0 < rim by norm_num [rim])] with x hp h; exact ⟨h,fun i hi=> hp i (mem_range.mpr (by unfold powerUp at hi; omega)) hi⟩
variable {F:Protection D}
structure Extol (D:Rolls X.p)(K:Targets X.p X.K){F:Protection D}(W:Delays F): Prop where
   paid : ∀ i j, StepStages i j → ∀ x,W.betaEntry i≤x → PricedForce x D K i j
lemma receipt (W:Delays F) : ∃ U:Delays F, DelayLe W U∧ Extol D K U:= by
    obtain ⟨g,-,hh,hg⟩:= collect_upper W.betaEntry _ fun i=> eventually_transitions i _ _ (fun j (_:StepStages i j)=> sullied (K:=K) (D:=D) i j); exact ⟨{W with betaEntry:=g},⟨hh,le_rfl,le_rfl,le_rfl⟩,⟨fun i j hi x hx=> hg i x hx j hi⟩⟩
variable {E:Expenses K}{p : Return.Wages}{v:ℕ→ℝ}
abbrev uplift (_:PhysicalNext.Repeat.Register D E p v)(W:Delays F) := Extol D K W
def snowy (G:Gauge): Legato.Booster G where
   asks S _ _ W:= uplift S W
   mono hp hv:= ⟨fun i j hij x hx=> hp.paid i j hij x ((hv.beta _).trans hx)⟩
   buy _ _ _ W:= receipt W
end YM.Juniper.Voucher
