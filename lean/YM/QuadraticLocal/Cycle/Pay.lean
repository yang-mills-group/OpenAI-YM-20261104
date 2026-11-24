import YM.QuadraticLocal.Cycle.Pools
/-! # Numeric payer center on each stage. Local statements and gates. Use before real Shape clock -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.MintClock
open Function Filter Finset Lattice RG Pressure Ac Marker Next.Scheduling
open Wilson RG.Supply PhysicalNext Repeat
open ConnectedActivityE6 Push Push.AbsoluteSums Coat RemainderComparison
open AnalyticBridge VerifiedReset QuadraticLocal.Earn QuadraticLocal.Mentor Animals
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
namespace Page
variable (G:Gauge)(D:Side)(P:Page)(U V:Stage)
variable (hP:Eligible G D P) (x:ℝ)
local notation "K"=> (fun x=> Pressure.betaF G x D)
local notation "Q"=> Delay.fineMonitor G D
local notation "D'"=> D.val
local notation "Bf" => Pressure.radiusB ∘ ( K )
local notation "W"=> temperature G D
local notation "Φ"=> P.order+P.rank+1
noncomputable def tariff (a c:ℝ)(B:ℕ) := Footprint.payment 1 (B+2) (U.power*U.order+Wages.grade (P.order+P.rank+1) U.power U.order) c (Invoice.liberty G (U.power*U.order) Φ U.power U.order B (temperature G D x)) 1 a (Invoice.tax (P.order+P.rank+1) P.cap)
lemma front_quote {p:BudgetPoint}(h:Time.Same U p) (B:ℕ)(hb:p.B=B)(a c:ℝ): Invoice.price p (W x) (P.order+P.rank+1) P.cap a c G = Page.tariff G D P U x a c B:= by
 unfold Invoice.price Page.tariff Invoice.memories; rw [h.1,h.2.1,hb]
lemma income {M:ℝ→ℕ}(h:Reserve G D (fun x=>(M x:ℝ)))(a c:ℝ):Reserve G D (fun x=> Page.tariff G D P U x a c (M x)) :=by
 let f(x:ℝ):= Invoice.liberty G (U.power*U.order) Φ U.power U.order (M x) (temperature G D x)
 have hW:Reserve G D f:= ((((Reserve.const _).mul (((Reserve.const _).mul Reserve.monitoring|>.pow _)))).mul ((h.add (Reserve.const _)|>.pow _))) -- defeq annotation? fix
 let g x:=(Footprint.spread 1 (M x+2):ℝ); have hg:Reserve G D g:= by simp_rw [g, Footprint.spread,one_mul]; apply Reserve.ball; simpa using! h.add (Reserve.const 2)
 exact ((((Reserve.mul (Reserve.const _) hW).mul hg).mul (Reserve.const _)).mul (Reserve.const _)) -- hW exponent c*..., check ordering.
-- compare through # CoverBrush.Link.Visibility separately including old e.
noncomputable def raising (P:Page) (L:Side) (x:ℝ):= Scene.productivity L P.c P.b (P.height x) P.cap P.order
local notation "Γ"=> U.supportExponent
noncomputable def life := Tint.Campus.Hearth.Week.maxFee D P.cap (P.span (radiusB x)) (P.helm (radiusB x)) (U.supportExponent+1+1) P.cover
noncomputable def flow := Shelter.Deck.crewCost (P.helm (radiusB x)) (U.supportExponent+1) P.cover
local notation "A"=> (P.computes G D x)
local notation "s"=> P.helm (radiusB x)
-- factor after synthesis. Pure-Reconstruction clocks minimal
lemma template {p:BudgetPoint}(h:Time.Same U p): (A).school D p = P.life D U x ∧ (A).flow p=P.flow U x ∧ Earnings.past D p=Spire.fees D (U.supportExponent+1+1):=by -- nutrition: notation A dot no
 rw [Earnings.school, Earnings.past,Earnings.flow,h.2.2]; exact ⟨rfl,rfl,rfl⟩
include hP
lemma proceeds : Reserve G D (fun x=>Page.raising P D x):= (Reserve.const _).add ((Reserve.const _).mul hP.paid)
omit hP
local notation "s₁" x:max=> P.span (radiusB x)
lemma tons : Reserve G D fun x=> Page.life D P U x:=by
 let a x:= Breeze.areaBudget (P.span (radiusB x)) P.cap (D.val^4:ℝ)
 have ha:Reserve G D a:=(((((Reserve.ball _ (topReserve («P»:=P))).mul (Reserve.const _)).add (Reserve.const 1)).pow _).mul (Reserve.const _))
 exact (((((Reserve.const _).mul (Reserve.ball _ (hcap («P»:=P)))).mul (Reserve.const _)).mul ha).mul (Reserve.const _))
lemma movement:Reserve G D (Page.flow P U):= (Reserve.const _).mul (Reserve.ball _ (hcap («P»:=P)))
lemma season : Reserve G D (fun x=> (Willow.haloSlack (radiusB x))⁻¹):=by
 unfold Willow.haloSlack Willow.area; simp_rw [one_div,inv_inv]; push_cast; exact (Reserve.const _).mul (((Reserve.field.add Reserve.field).add (Reserve.const _)).pow 4)
-- allocation ≥ requested shapes / Year.Const.Ko_Meta.Month.P.Birth
abbrev reward (t ε:ℝ):= min (Beaming.spray t) (t^ε)
variable {ε:ℝ}(hε:0<ε)
local notation "Sp" u:max=> (Page.reward ( K u ) ε)
include hε
lemma tender (f:ℝ→ℝ)(h:Reserve G D f): ∀ᶠ x in atTop,f x ≤ Sp x:=by obtain hp:= h.rate ε hε; obtain ⟨k,hk⟩:= h; filter_upwards [hp,hk,Beaming.spray_late (G:=G) D k] with x hf ht hz using le_min ((le_abs_self _).trans (ht.trans hz)) ((le_abs_self _).trans hf)
end Page
end YM.QuadraticLocal.MintClock
