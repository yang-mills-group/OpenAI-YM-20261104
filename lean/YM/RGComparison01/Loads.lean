import YM.RGComparison01.Vision
/-!
# Explicit output local fees

 After post-L choices, as usual. Use before Hessian. Guard all repainted
 reach + Orbit prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage AuxBeam AuxSpell AuxJets AuxStage
open Push.AbsoluteSums.Animals Slide Tensor WilsonStartup Bouquet Push.PriceCompiler
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves
open RG.Supply Shoot Input Org Ovens Progress.DirectedRecipe Next.Scheduling Further.PhysicalPeriodLimitF933
open Vision
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} {P : Teller G} {K : KernelChoices} {C Z W' μ σ Λ σ' C' : ℝ} {j q n k b w: ℕ} {v d W u : ℝ→ℝ}
namespace Loads
variable (b k w q : ℕ) (L: Side)
variable (S : RG.Stage) (X : Kraal.Floor G L) (E : BareRates.pre G S.width S.paths j) (d u:ℝ→ℝ)
variable (v : ℝ) -- abs(alpha)≤...
local notation "Y" => (fun x:ℝ=> (Trio.paySide G L b x:ℝ))
local notation "D" => (fun t=> Trio.base b (radiusB t))
-- output through order k, Aux widths d, Pencils coefficient order q. explicit multiplied g channel everywhere
abbrev quota (k b w:ℕ) : ℝ:= (k+1:ℕ)*(Pencils.bounder k b+k+w+1:ℕ)
abbrev rateP (t:ℝ) := |2*u t+ Bonus.baseFee E S.clip (Y t) (ConnectedActivityE6.loopBill G L t) v (d t) k + ritual_fee w k (X.s t) 0 (d t) + quota k q w* X.u t|
abbrev coin (k:ℕ) : ℝ:= 2*2^(k+1) + 1
abbrev tune (t:ℝ) (i: Slide.Stars) := Boulevard.ticket S.order (rateP b k w q L S X E d u v t) + 2*((Fintype.card (Site (Trio.fence b (radiusB t) i)):ℝ)*coin k)
abbrev size (P : RG.Stage) (x:ℕ) : BudgetPoint := ⟨P.power,P.order,P.supportExponent,x+1,1,P.power_ge,P.order_ge,P.price_pos, Nat.zero_lt_succ _,zero_lt_one,le_rfl⟩
abbrev annual (t:ℝ) := Trio.oroW (size S (D t)) (D t) (tune b k w q L S X E d u v t)
abbrev salary (t:ℝ) := let s:= annual b k w q L S X E d u v t; coin k + Height.away S * (s*Real.exp ((S.supportExponent+3) *Trio.coverTicket b))
lemma voting (G : Gauge) (i:Slide.Stars) : Geo G L (fun x=> (Fintype.card (Site (Trio.fence b (radiusB x) i)):ℝ)):= by
  have he:= (Trio.rows G L b).2.1
  let F x := (Trio.tent b (radiusB x):ℝ)
  let g x:=2*(F x+i.val)
  have hg:Geo G L g:= (Geo.fixed 2).times (Geo.joins (Geo.basic he) (Geo.fixed _))
  rw [show (fun x=> ((Fintype.card (Site (Trio.fence b (radiusB x) i))):ℝ)) = fun x=>g x^4 from funext fun x=>by
    rw [site_card]; change ((↑((2*(Trio.tent b (radiusB x)+i.val))^4:ℕ)):ℝ)= _; unfold g F; norm_cast]
  exact hg.power 4
lemma tiltage (G : Gauge) : Geo G L (fun x=> Trio.tilt (size S (D x)) (D x)):=
    (Geo.fixed ((2:ℝ)^S.order)).times (((Geo.fixed 1).joins (Geo.basic (Trio.rows G L b|>.2.2.1))).power (S.power*S.order))
lemma shape (hd:Geo G L d) (hu : Geo G L u): Geo G L (rateP b k w q L S X E d u v) :=
    (((Geo.joins ((Geo.fixed _).times hu) (Kraal.dangerous E _ k _ (Trio.circles ..) hd)).joins (Kraal.for_ritual w k hd X.wings)).joins ((Geo.fixed _).times X.spans)).mean
lemma wages (hd:Geo G L d) (hu : Geo G L u): Geo G L (Loads.salary b k w q L S X E d u v):= by
  have ht:= ((shape b k w q L S X E d u v hd hu).rate)
  have hv i:Geo G L (fun t=> Loads.tune b k w q L S X E d u v t i):= (((Geo.fixed _).times (shape b k w q L S X E d u v hd hu)).times (Geo.fixed _)).joins ((Geo.fixed _).times ((voting b L G i).times (Geo.fixed _)))
  have hh: Geo G L (Loads.annual b k w q L S X E d u v):= Geo.expel Finset.univ (fun i t=> |Slide.ray i| * (Trio.tilt (size S (D t)) (D t)*tune b k w q L S X E d u v t i)) (fun i _=> (Geo.fixed _).times ((tiltage b L S G).times (hv i)))
  exact (Geo.fixed _).joins ((Geo.fixed _).times (hh.times (Geo.fixed _)))
lemma pondering (t:ℝ) (i: Stars): 0≤ tune b k w q L S X E d u v t i:= by
  apply add_nonneg; unfold Boulevard.ticket rateP; positivity
  unfold coin; positivity
end Loads
end YM.RGComparison01
