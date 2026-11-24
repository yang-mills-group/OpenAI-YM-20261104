import YM.Juniper.Voucher.Bounty
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
open UVExtension Oriel Charted Clock Instrument
variable {κ d D:ℝ}{G:Gauge}{X: Metals G}
-- after-origin K has exponential slack *in exponent* once in `QuoteHard` (hence with B.post via Time.now, invoke that). need shrinking normalization margin. Buy κ/8.
local notation "P"=> Instrument.plain
def swim (d c x:ℝ): Prop := let A:=x+c
    Real.exp (-d* (P).P A^(2:ℕ))≤ (rim/4)*(P).w x
lemma shore (h:0<d)(c:ℝ) : ∀ᶠ x in atTop, swim d c x :=by
   have hr:= Clock.growing (lt_trans zero_lt_one plain.above); have hx: Tendsto (fun x:ℝ=> x+c) atTop atTop:= tendsto_atTop_add_const_right atTop _ tendsto_id
   have he: Tendsto (fun x:ℝ=>Real.exp (- (d/2)*(P).P (x+c)^ (2:ℕ))) atTop (𝓝 0):= Real.tendsto_exp_atBot.comp  ((tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr (half_pos h))).mpr ((tendsto_pow_atTop (n:=2) (by norm_num)).comp (hr.comp hx)))
   filter_upwards [he.eventually (ge_mem_nhds (show 0 < rim/4 by norm_num [rim])), hx.eventually (Postage.saved plain (d/2) (half_pos h)), just_near c,plain.support 2 one_lt_two] with x he hh hp hq
   let u:= Real.exp (-(d/2)*(P).P (x+c)^ (2:ℕ)); have hv:u≤ (P).w x:= hh x (hq x _ (Clock.same x) hp); change Real.exp _≤ _; apply le_trans ?_ (mul_le_mul he hv (Real.exp_nonneg _) (by norm_num [rim]:0≤rim/4)); rw [← Real.exp_add]; apply Real.exp_monotone; apply le_of_eq; ring
variable {i j:ℕ}{s: Sheet G}{T:Rolls X.p}(Q:PostCost T){F:Protection T}
-- Witness pay numerical BEFORE. choose after Qin provided. compiler assures postCast.
def Savings (W: Delays F) := ∀ j (x:ℝ), W.betaEntry j≤x→ swim (Q.g j) (G.slopeConstant*Real.log (T.L j).val) x
lemma token (W:Delays F): ∃ V:Delays F, DelayLe W V ∧ Savings Q V:=by
    obtain ⟨g,-,hh,hg⟩:= collect_upper W.betaEntry _ fun i=>Voucher.shore (Q.posG i) (G.slopeConstant*Real.log (T.L i).val); exact ⟨{W with betaEntry:=g},⟨hh,le_rfl,le_rfl,le_rfl⟩,hg⟩
def seating (G:Gauge) : Legato.Booster G where
   asks _ S _ W:= Savings S W
   mono h hv:= fun i x hh=> h i x ((hv.beta _).trans hh)
   buy _ S _ V:= token S V
section case
variable {A:Alloy X T} (H:Savings A.post A.delay) (m:ℕ)
local notation "U"=> A.B.a
local notation "J"=> A.B.a.clock
include H
lemma chair : Return.forcing A.B m ≤ (rim/4)*(J).forcedAllowance m:= by
   have hp:=H _ _ (A.B.valid.pays m)
   have h(c):= Deployment.clock_eqns (J) c
   change Real.exp (- _ * _^ (2:ℕ))≤ _; rw [(h (m+1)).2.1, (h m).2.2.2.2.1,PriceCompiler.beta_eq A.B.valid]; exact hp
end case
end YM.Juniper.Voucher
