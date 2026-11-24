import YM.RGComparison01.Sensor.Draft
/-!
# Finance Mark rank probes after the rest of the budget.
 Pre-audited dimension bound from D Aux. No dependence on real volume S;
 costs after-call. qMark.Support charges only in physical kernels. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Sensor
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat Deck
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Gauge
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Push.Uniform Fare Sienna Lapis Lotus Pledge Baked Merge Palette Team Pulse
open AuxFabric AuxPackage AuxConstant Metric Next.Fluctuations Bid
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

variable {G : Gauge} {L: Side}{R D X d f:ℝ→ℝ} {β u a p:ℝ}
section
lemma surveys (V: ChartPrices)(A:ℝ)(k:ℕ)(h:Geo G L X)(hp:Geo G L D): Geo G L (fun t=> tally V (X t) (D t) A k G):= by
   let W (t:ℝ) := X t
   have ht : Geo G L (fun t=> Lapis.lensT k V (W t)):= (Geo.fixed _).joins ((Geo.power h _).times (Geo.fixed _))
   have he: Geo G L (fun t=> |glare V (X t) k (D t)|):= Geo.mean ((((h.times ht).joins hp)).joins (Geo.fixed 1))
   exact (Geo.fixed _).times (((Geo.fixed 1).joins (((Geo.fixed 1).joins he).times (Geo.fixed 1))).power k)
-- radius condition only.Stage bool; do not demand R positive here.Certs deliver.can use even before sensors. η for debt.
variable (V:ChartPrices)(k :ℕ)
abbrev umbra (G : Gauge)(L:Side)(x:ℝ):= (2*Delay.fineMonitor G L x)^ (2:ℕ)
lemma weight_cap (G:Gauge)(L:Side)(h:0<β)(e:ℝ)(hv:0 < Pressure.betaF G e L)(he:β ≤ 2*Pressure.betaF G e L): lensWeight (gStep β) (Pressure.fiery G e L) ≤ umbra G L e:= by
    let r:=Delay.fineMonitor G L e; let γ:=gStep (Pressure.betaF G e L); let a:= gStep β; have hQ:0 ≤ r:= Delay.monitor_pos ..|>.le
    have hT:0 < a:= Fare.gS _ h|>.1
    have hP: 0 ≤ γ:= Fare.gS _ hv|>.1.le
    change (γ*r)^ (2:ℕ) * a⁻¹^ (2:ℕ) ≤ (2*r)^2; rw [←mul_pow]; refine pow_le_pow_left₀ (by positivity) ?_ _; rw [← div_eq_mul_inv]; apply (div_le_iff₀ hT).2; exact (mul_le_mul_of_nonneg_right (Geo.strip hv h he) hQ).trans_eq (by ring)

-- root price at planned counts.Plate factors sanitized. *1/unspent units payable g^-δ*
variable (G)(L:Side)
set_option quotPrecheck false
local notation "U"=> V.horizon
local notation "Y₀"=> Before.Service.trailCost V (k+3)
-- single chip. include lowering cost for both Full K invoice folding and rooted threshold after-call. u = full envelope with λ_norm=q/u and γ user reserve; positivity.Prop.
abbrev coinW (x:ℝ) (r:ℕ) :ℝ:= Real.exp (x* ((r+r+1)^ (4:ℕ):ℕ))
abbrev uplink (μ X D Z y :ℝ)(r Q:ℕ)(x:ℝ):= umbra G L x * coinW y r + (|μ| * umbra G L x + |μ| * tally V X D Z k G * Sensor.wage k Q +1)
lemma earns_coin (q r:ℕ)(μ a D y:ℝ)(he: μ≥0)(x:ℝ)(z:ℝ) : let g:= tally V a D z k G; let u:= uplink G V k L μ a D z y r q x
     0<u ∧ umbra G L x * coinW y r ≤ u ∧ ‖μ/u‖ * umbra G L x ≤ 1 ∧ ‖μ/u‖* g ≤ (Sensor.wage k q)⁻¹ := by
    intro g u; let β':=umbra G L x; let f:= Sensor.wage k q; have hu:0≤ β':=sq_nonneg _; have hv: 0 ≤ g:= Sensor.fare_nn ..; have hx : 0 ≤ coinW y r:= Real.exp_nonneg _; have hz:0<f:=by unfold f Sensor.wage Sensor.chip; positivity
    have ht:u= β'*coinW y r+(μ*β'+ μ*g*f+1):= by unfold u uplink; rw [abs_of_nonneg he]
    have hb:0 < u:= by rw [ht]; positivity
    have hf:= div_nonneg he hb.le
    simp only [Real.norm_of_nonneg hf]
    refine ⟨hb,by rw [ht]; exact le_add_of_nonneg_right (by positivity),?_,?_⟩
    · change μ/u*β' ≤ 1; rw [div_mul_eq_mul_div,div_le_one hb]; rw [ht]; linarith only [mul_nonneg hu hx,mul_nonneg (mul_nonneg he hv) hz.le]
    change μ/u*g ≤ f⁻¹; rw [div_mul_eq_mul_div,← one_div f,div_le_div_iff₀ hb hz,one_mul,ht]; linarith only [mul_nonneg hu hx,mul_nonneg he hu]
variable {μ v:ℝ→ℝ}
structure Hands (r Q : ℕ)(X D μ R:ℝ→ℝ)(Z y η x:ℝ) :Prop where
    high (β:ℝ)(hb:0<β)(ht:betaF G x L/2 ≤ β) : let S:=R x*gStep β
                                          (0 < V.horizon→ S ≤ V.horizon) ∧ Before.Service.trailCost V (k+3)*S +S*(D x)≤1
    stock (β:ℝ)(hb:0<β)(ht:betaF G x L/2 ≤ β) : uplink G V k L (μ x) (X x) (D x) Z y r Q x≤ gStep β^(-η)
lemma handy (r Q :ℕ)(Z y η:ℝ)(hR:Geo G L R)(hx:Geo G L X)(hd:Geo G L D)(hp:Geo G L μ)(he:0<η):∀ᶠ x in atTop, Hands G V k L r Q X D μ R Z y η x:=by
    let f t:= tally V (X t) (D t) Z k G; have hF:Geo G L f:= surveys V Z k hx hd
    let p:=Sensor.wage k Q; have hq: Geo G L (umbra G L):= Geo.power ((Geo.fixed 2).times Geo.by_delay) _
    have hW:Geo G L (fun t=>uplink G V k L (μ t) (X t) (D t) Z y r Q t):= (hq.times (Geo.fixed _)).joins (((hp.mean.times hq).joins ((hp.mean.times hF).times (Geo.fixed p))).joins (Geo.fixed 1))
    have hV : ∀ᶠ x in atTop, ∀ β,0<β→betaF G x L/2 ≤ β→0 < V.horizon→R x*gStep β ≤ V.horizon:= by
        by_cases ht : 0<U; swap; · simp [ht]
        filter_upwards [hR.uniform ht] with x hx β hb h hQ; exact (mul_le_mul_of_nonneg_right (le_abs_self _) (Fare.gS β hb|>.1.le)).trans (hx β h).le
    have hd':Geo G L (fun t=>Y₀*R t+R t * D t):=((Geo.fixed _).times hR).joins (hR.times hd)
    filter_upwards [hV,hW.loss he 0,hd'.uniform zero_lt_one] with x hx hH hd; refine ⟨fun β hb ht=>⟨hx β hb ht,?_⟩,fun β hb ht=>?_⟩
    · apply le_trans _ (((mul_le_mul_of_nonneg_right (le_abs_self (_+_)) (Fare.gS _ hb|>.1.le)).trans ((hd β ht).le))); apply le_of_eq; ring
    exact (le_abs_self _).trans (by simpa only [pow_zero,mul_one,Nat.cast_zero,zero_sub] using hH β hb ht)
end
end YM.RGComparison01.Sensor
