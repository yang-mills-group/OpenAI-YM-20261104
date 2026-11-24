import YM.LocalLTE.Moor.Book
import YM.LocalLTE.Cycles.Prodigal
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Rain.Glazing
/-! Clock precision and re-expression room. Tallies physical costs AFTER support and tilt, at a fixed horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.ClockB
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Height Roof Trio YM.LocalLTE.Inset
variable {G : Gauge} {c f : Side} {j k i n m a : ℕ}
/- 'side' quorum. budget u now denotes TYL remainder, e raw E. Gold
 retention for Local at preprojection. -/
section rates
variable (G) (L:Side) (W: RG.Stage) (b:ℕ) (l e : ℝ) (x:ℝ)
local notation "ζ" => betaF G x L
local notation "d" => base b (Pressure.radiusB x)
local notation "q" => fence b (Pressure.radiusB x)
local notation "J" => W.order
def lanternPay:= turnCost_dummy where turnCost_dummy:= Height.away W*((ζ)^e+(ζ)^e)+(ζ)^e -- Ash cost

def ease (i:Stars):ℝ := Boulevard.ticket (J) ((J).factorial*(ζ)^l+(J).factorial*(ζ)^l)+2*((Fintype.card (Site (fence b (Pressure.radiusB x) i)):ℝ)*lanternPay G L W e x)

def gust (x:ℝ) :ℝ:= ∑ i:Stars, |Slide.ray i| * ((2:ℝ)^W.order*((1+(base b (radiusB x):ℝ))^(W.power*W.order)) * ease G L W b l e x i)

def tomorrow := lanternPay G L W e x + Height.away W * (gust G L W b l e x * Real.exp (Trio.stout W * Trio.coverTicket b))

lemma glow : Rate G L e (lanternPay G L W e):= ((Rate.power.add Rate.power).mul_left _).add Rate.power
lemma winds (i:Stars) (h:e≤l): Rate G L l (fun x=> ease G L W b l e x i):= by
  refine Rate.add (((Rate.add (Rate.power.mul_left _) (Rate.power.mul_left _)).mul_left _).mul_right _) ((Rate.mul_left ((Trio.feeStars G L b i).mul (glow G L W e)) _).weaken ?_); linarith
lemma gusts (h:e≤l) : Rate G L l (gust G L W b l e):= by
  have hb := (rows G L b).2.2.1; unfold gust; apply sparks G L (f:=fun i x=>|Slide.ray i| * (_)); intro i
  apply Rate.weaken (Rate.mul_left ((Bolt.uses (Bolt.times (Bolt.still ((2:ℝ)^W.order)) (((Bolt.still 1).joins hb).nod (W.power*W.order)))).mul (winds G L W b l e i h)) _); linarith
lemma income (h:e≤l) : Rate G L l (tomorrow G L W b l e):= (Rate.add ((glow G L W e).weaken h) (((gusts G L W b l e h).mul_right _).mul_left _))

-- full inventive E actual Kinematics Gold re-expression set
abbrev gapB (x:ℝ) := (1/2:ℝ) * (Time.credit G W * δE x)
-- extra condition e<-23/20
lemma spritely (he:e < -(23/20:ℝ)) (h : e ≤ l) {v:ℝ} (hl:l<v) : ∀ᶠ t in atTop,
    let y:= betaF G t L; let s:= lanternPay G L W e t
    1≤ y ∧ s≤gold G L t ∧ s+Height.away W * (planks G L b W t * Real.exp (stout W * coverTicket b)) ≤ gapB G W t ∧ tomorrow G L W b l e t ≤ y^v:= by
  filter_upwards [Sienna.contraction G L (a:=1) zero_lt_one (glow G L W e) he, (income G L W b l e h) v hl,Roof.compar G L b W,eventually_ge_atTop (1:ℝ)] with t ht hv hh hz y s
  have hS:1≤ y:=hz.trans (le_add_of_nonneg_right (Work.E04.shift_nonneg ..))
  have he:s≤ gold G L t:=le_of_lt (by rw [one_mul,one_mul] at ht; exact ht)
  refine ⟨hS,he,le_trans ?_ hh,(le_abs_self _).trans hv⟩; apply add_le_add_left; apply he.trans; apply le_add_of_nonneg_left; unfold gold Height.away Push.Local.turnCost; exact mul_nonneg (by positivity) (Real.rpow_nonneg (show 0≤y from zero_le_one.trans hS) _)
end rates
-- Aero pre-L condition (monotone threshold receipts purchased)
variable {X:Metals G} (D:Rolls X.p) {C:Targets X.p X.K} {Z: Expenses C} {p:Return.Wages} {v:ℕ→ℝ}
variable {F:ℕ→ℕ→Postage} {S:Time.Scouts (F:=F)} {P:Protection D} (W:Delays P) {r α w l e π d κ q : ℝ} {ℓ p':ℕ} (R:Register D Z p v)
-- Aero uses b> etc.
variable {s:Sheet G} {K:MapPrices} (Q:Targets s K)
def capline (j i:ℕ):ℕ:= (Height.aerodynamic (Q j i)).choose
-- With Offset `fromMax` use
lemma medium (p₀:ℝ) (h:(Height.aerodynamic (C j i)).choose ≤ (D.L j).val) (ht:3≤ℓ) (he:-(3/8:ℝ)*(ℓ-3:ℕ)<e) (hj:StepStages j i):
    ∀ᶠ x in atTop, Height.Aerobics (Z j i) (D.L j) (p j i) (R.μ j i) (R.c j i) (R.o j i) x e (heap G (X.p.profile i) p₀) ℓ (X.p.profile i).order (X.p.profile i).power Chi.canonical:=
  (Height.aerodynamic (C j i)).choose_spec _ h _ _ _ _ _ (R.consumes _ _ hj).1 (R.consumes _ _ hj).2.1 _ (heap G (X.p.profile i) p₀) _ _ _ _ ht he
lemma frameBook (hv:w<α) (hy:α<0) (h:Reliable G κ q) (j i ℓ:ℕ) : ∀ᶠ x in atTop, let L:= D.L j; let b:=Trio.resize ℓ (C j i|>.halo); let k:= (X.p.profile i).order
    ∀ i:Stars,YM.LocalLTE.Frame.Lease G k κ (Trio.fence b (radiusB x) i) (cone α (betaF G x L)) (cone w (betaF G x L)) Chi.canonical:= by
  apply eventually_all.mpr; intro r'
  let f x:=Trio.fence (Trio.resize ℓ (C j i|>.halo)) (radiusB x) r'; let y x:ℝ:= (f x).val
  have he : Rate G (D.L j) 0 y:= by
    have hx:= Trio.feeStars G (D.L j) (resize ℓ (C j i|>.halo)) r'; apply Rate.compare hx; filter_upwards with x; unfold y; rw [site_card]; push_cast; change |((f x).val:ℝ)| ≤ |(((f x).val:ℝ))^4|; rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]; apply le_self_pow₀
    · exact_mod_cast (show 1 ≤ _ from (f x).pos)
    decide
  filter_upwards [YM.LocalLTE.Frame.leased G (X.p.profile i).order h α w hv hy he (χ:=Chi.canonical)] with x hz; exact hz (f x) le_rfl

-- supplementary cutoff at exponent e
local notation "t'" => (X.p.profile i)
include R
lemma flight (e:ℝ) (hp: (Z j i).wanting ≤ -(7/16:ℝ)) (h:StepStages j i) : ∀ᶠ x in atTop,∀ p:BudgetPoint,p.threshold ≤ 2*Pressure.fiery G x (D.L j)→p.power=(t').power→p.order=(t').order→p.supportExponent=(t').supportExponent→p.B= radiusB x→∀ β a Λ:ℝ,|β| ≤2*betaF G x (D.L j)→|a|≤cloak D j→0 ≤Λ→Λ≤ ConnectedActivityE6.loopBill G (D.L j) x →
    Real.exp (-((t').width/4)*p.B) *Song.octaveNeed G p (t').clip (t').width (t').paths Λ β a ≤betaF G x (D.L j) ^ e:= by
  let u:= X.p.profile i; let L:=D.L j
  have he : Rate G L e (fun x=> Real.exp (-(u.width/4)*radiusB x)) := by
    refine (Rate.cutoff (G:=G) (L:=L) (a:=e) (show 0<u.width/4 from div_pos u.width_pos (by norm_num))).compare (Eventually.of_forall fun x=>?_)
    rw [abs_of_nonneg (Real.exp_nonneg _),abs_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_le_exp.mpr; exact mul_le_mul_of_nonpos_left (show (Pressure.Stores.till x:ℝ)≤radiusB x by exact_mod_cast Nat.div_le_self ..) (by have he:=u.width_pos; linarith)
  filter_upwards [Boulevard.deposits D R h hp,(he.mul (Rate.power (G:=G) (L:=L) (a:=-(7/16)))) _ (by linarith : e + -(7/16) < e)] with x hh hK p hΛ hv hy hx hB β a Λ hk hω ha hz
  have ht:=hh.2.1 p hΛ hv hy hx hB _ _ _ hk hω ha hz|>.1
  rw [hB]; exact (mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)).trans ((le_abs_self _).trans hK)
end YM.PhysicalNext.Repeat.ClockB
