import YM.Juniper.Orrery.Distant
/-!
 # Buy exponential TILES allowance (actual family, after-L)
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Orrery
open UVExtension
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Tabernacle
open Whirl PhysicalNext.Repeat.Graces
open Oriel Charted Dales Tour Bright Voucher Flare
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A:Alloy X D}
section boost
variable (S:Sheet G) (d:Rolls S)(k j:ℕ)
local notation "H"=> S.profile k
local notation "σ"=> ((H).width)
local notation "L"=> d.L j
local notation "E"=> (fun x:ℝ=> Real.exp (-σ /4*(radiusB x)))
local notation "Β"=> (fun x:ℝ => x ^ j)
abbrev Sleeve (x:ℝ) := (E x ≤ (Β x)⁻¹/2)∧ radiusB (Pressure.betaF G x L) ≤ 2*radiusB x
lemma purchaseBase : ∀ᶠ x in atTop,Sleeve S d k j x:= by
   have hσ :0<σ:= (S.profile k).width_pos
   let P (x:ℝ) := Real.exp (-(σ/4)* Pressure.Stores.till x); have hP : Rate G L (-((j:ℝ)+1)) P:= Rate.cutoff (a:= -((j:ℝ)+1)) (show 0<σ/4 by positivity)
   have hR:= hP.mul_left 2; filter_upwards [hR (-(j:ℝ)) (by linarith), Push.AbsoluteSums.Fees.horizons G L 125 (ε:=1) zero_lt_one (le_refl (0:ℝ)) (show 2*1 < (3:ℝ) by norm_num), eventually_gt_atTop (0:ℝ)] with x hx hp hx₁
   refine ⟨(le_trans (b:=P x) ?_ ?_),hp.2.1⟩
   · suffices σ/4*↑(Pressure.Stores.till x) ≤ σ/4*↑(radiusB x) by apply Real.exp_le_exp.mpr; linarith only [this]
     gcongr; exact Nat.div_le_self ..
   rw [abs_of_pos (mul_pos (by norm_num) (show 0<P x from Real.exp_pos _))] at hx; refine le_div_iff₀ (by norm_num : (0:ℝ)<2) |>.mpr ((mul_comm _ _).trans_le (hx.trans ?_)); let u:= betaF G x L; have hh :x≤u:= le_add_of_nonneg_right (Work.E04.shift_nonneg G L); change _ ≤ (x^j)⁻¹; rw [← Real.rpow_natCast x, ← Real.rpow_neg hx₁.le]; exact Real.rpow_le_rpow_of_nonpos hx₁ hh (by simp)
structure Tailcoat {H':Protection d}(U: Delays H'): Prop where
   arm (k j:ℕ) : StepStages j k → ∀ x,U.betaEntry j ≤ x → Sleeve S d k j x
variable {H':Protection d}
lemma reserved (U:Delays H') : ∃ W:Delays H', DelayLe U W∧ Tailcoat S d W:=by obtain ⟨g,-,hg,h⟩:=collect_upper U.betaEntry _ fun j=>eventually_transitions j _ _ (fun k (_ : StepStages j k)=> purchaseBase S d k j); exact ⟨{U with betaEntry:=g},⟨hg,le_rfl,le_rfl,le_rfl⟩,⟨fun k j hk x hx=> h j x hx k hk⟩⟩
variable {Y: Targets X.p X.K}{V: Expenses Y}{p: Return.Wages}{v:ℕ→ℝ}
abbrev dressing (_ : PhysicalNext.Repeat.Register D V p v) {P:Protection D}(d:Delays P) := Tailcoat X.p D d
def tune (G:Gauge): Legato.Booster G where
   asks S _ _ W:= dressing S W
   buy _ _ _ _:= reserved ..
   mono h hv:=⟨fun k j hk x hx=> h.arm k j hk x ((hv.beta j).trans hx)⟩
end boost
section adjust
variable {hG:G.Simple}
noncomputable def agenda (P:Gauze.Snip G)(V:Extras G): Extras G := { Flare.agenda P V with booster:= (Flare.agenda P V|>.booster).and (tune G) }
lemma attaches {P:Gauze.Snip G}{V:Extras G}{W:Nursery G hG}(h:Stock (Orrery.agenda P V) W) : Stock (Flare.agenda P V) W∧ Tailcoat W.M.p W.P W.A.delay := by obtain ⟨hx,h'⟩:=h.boosted; exact ⟨{ h with boosted:=hx},h'⟩
end adjust
section forecast
variable (R:Factor A) {N m n k r:ℕ}(hm:m<N) {s:ℝ}
local notation "B"=> (A.B.a.budget m)
local notation "B₀"=> (A.B.a.budget (m+1))
local notation "J"=> A.B.a.clock.J (m+1)
local notation "B*"=> A.B.a.clock.hatBeta m
local notation "L!"=> A.B.a.clock
local notation "σ"=> (Time.forecastE A.B.a m)
local notation "S₀"=> A.B.a.params m
local notation "Φ"=> A.B.kin.path N m
local notation "Δ"=> (S₀).clip
local notation "α"=> A.B.kin.alpha N m
open Dales Oriel Averaging
variable (H: Tour R N m n s) (h:Paperwork R.shape s Camp.soft A.delay)
local notation "T"=> ((2*rim)*σ)
local notation "v"=> (L!).allowance m
local notation "u"=> ((B*)^r)⁻¹
local notation "K"=> regularNeed G (B) Δ (S₀).width (S₀).paths α T
include H h
lemma viewH : K ≤ (rim/4)*v:= by
   let Q:=rim*1*σ; exact (Voucher.tighten R H h le_rfl le_rfl (b:=1) (by simp) (Q:=Q) le_rfl (z':=Q) le_rfl).1
omit H h
variable (hT:Tailcoat X.p D A.delay)
include hT
local notation "W"=> Real.exp (- (S₀).width/4*↑((B).B))
lemma coversR : (B₀).B ≤ 2*(B).B:= by
   have he:= hT.arm _ _ (step_paid _ m) _ (A.B.valid.pays m)|>.2; rw [← PriceCompiler.beta_eq A.B.valid] at he; exact he
lemma exponential (hk:r ≤ J) : W ≤ u/2:= by
   have he:= hT.arm _ _ (step_paid _ m) _ (A.B.valid.pays m)|>.1; have hξ:= (B|>.threshold_pos)
   have hr : (B*)^r≤(B*)^J:= pow_le_pow_right₀ (A.B.a.fits.delayed _).le hk
   have hh:0<B*:= zero_lt_one.trans (A.B.a.fits.delayed _); rw [PriceCompiler.params_eq A.B.valid]; exact he.trans (div_le_div_of_nonneg_right (inv_anti₀ (by positivity) hr) (by positivity))
include H h hT
open Ovens Ovens.Pipes
variable {c:Side}(T':Curtain G c)(he:Curtain.TidyC T' (A.B.a.budget m) (A.B.a.budget m).B ((2*rim)*Time.forecastE A.B.a m))
local notation "Δ₁"=> delta (T'.book.read T'.stamp)
local notation "W!"=> (Collection.fill T'.book Φ Δ (B) T'.stamp α Δ₁)
local notation "z"=> Collection.shelves T'.book Φ (B)
include H hT he
lemma sold (hk:powerUp r≤J)(hG:G.Simple) : Orrery.Payment (B) ((z).reg) ((W!).regular-pris (B).B (z).reg ((W!).regular)) ((rim/8)*u * v):= by
   let d:= (B); have hh:= hT.arm _ _ (step_paid _ m) _ (A.B.valid.pays m); have hy:=A.B.a.clock.hatBeta (m+1); let β:=A.B.a.clock.hatBeta (m+1); have hβ: β∈ Rain.lands A m:= by have h:1<β:= A.B.a.fits.delayed _; change β/2≤β ∧ β≤2*β; constructor <;> linarith
   have hv:= Bright.here R H.hm hβ 0; obtain ⟨p,hQ,hδ⟩:=he.income
   have hx : (B).threshold^2*|Δ₁| ≤ T:= delta_bound hG ⟨fun i=> (hδ i).1,p,fun i=> (hδ i).2,Quotes.segment _ (fun i=>(hδ i|>.2).1) hQ⟩
   have ζ : W ≤ u/2 := exponential hT (r:=r) (m:=m) (by unfold powerUp at hk; omega)
   obtain ⟨f,hf,hF⟩:= sticker (B) Φ (A.B.support.cap N m H.hm.le) hv.width T' he hx hv.decent hG
   refine ⟨f,hf, fun i=> budget_loosen (hF i) ?_⟩
   have hσ:0≤ v:= (fundedP m A.B.a).1.le
   refine ((mul_le_mul_of_nonneg_left (viewH R H h) (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_right ζ ?_)).trans_eq (by ring)
   exact mul_nonneg (by norm_num [rim]) hσ
end forecast
end YM.Juniper.Orrery
