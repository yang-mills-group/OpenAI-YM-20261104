import YM.RGComparison01.Sluice
/-!
# Recover quote from comparison on small auxiliary spouse

 Keep exact true unmarked scalar shift there. Patch price only uses
 Sun boundary derivatives; all logarithms on actual branches with gap.
 -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera
open RG.Supply RG.Shoot Push.Uniform Sienna Fare Lapis Metric Further.LogJets Blaze.Frond
open Pencils
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
namespace Bouquet
variable {G : Gauge} {K : Teller G} {S: ConnectedActivityE6.Target G K} {Y v u p a g c' m H' E s' : ℝ} {J:Target.Order G Y} {k i b m':ℕ}
    {ι:Type} {κ:Chi} {c f L : Side} {S':StepData c f}
    (T:Tube G S') {R:RG.Rep G f} (H:Cash Y u a L S J p T R) (W : Cabinet ι H b)
    (P:BudgetPoint)
local notation "O" => selfA H
local notation "Y'" => Beam.marquee H P
local notation "Z" => Song.plusone H (selfA H) κ g

variable (he: Collection.Local (Beam.marquee H P) P (Song.plusone H (selfA H) κ g) m c')
include he
lemma flatten (k i : ℕ) {σ C Λ : ℝ} (ht:T.down.Bounds T.low σ C Λ) (hz:P.B=radiusB u)
    (hw:S'.push R.beta R.eval = Collection.earlyValue (Y') T.down T.low P Z R.beta H' g)
    (M : Trio.Offer G c) : ∀ V∈Boulevard.sunny P,(metricA T g R+Trio.froth M) V=H' * Fintype.card (Site c)-Trio.froth (W.tot κ k i g - M) V - Boulevard.throng (W.leftward κ g k i).logRead V := by
  intro V hv
  have ha:= smoky hv
  let x:= H'; let S:= (Y').read Z
  have hE:= (Pane.crystalline T.down T.low P R.beta V ha)
  have hmu (i:Support c): Healthy P.threshold i V:= by unfold Healthy; rw [ha]; simp
  have hM:= W.unearned P he k i V; simp_rw [W.total P k i V _ hz (hmu _)] at hM
  have hg:= (Activities.gas_one ((Y').read Z) P ha)
  have hh: ((Y').read (W.leftward κ g k i)).additive P V= Boulevard.throng (W.leftward κ g k i).logRead V:= tsum_congr fun i=> masked_eq _ _ _ _ (hmu _)
  change Real.log _+Bonus.ember T g R.beta V+_= _
  rw [hw]; unfold earlyValue Rep.eval Rep.exponent Collection.frozen; dsimp only; rw [hg,mul_one,← Real.exp_add, Real.log_exp, hE, hM,hh, show receipt T.down T.low P V= secondTerm T.low T.down V from allGoodPrice ht V ha]
  unfold Bonus.ember Trio.froth; simp_rw [Pi.sub_apply,Finset.sum_sub_distrib]; ring

variable (hp : Sluice.Shore G L m' u v) (ht : P.order=m') (hP:P.threshold=Pressure.temp u) (hB:P.B=radiusB u)
include hp ht hP hB
lemma rental {σ C Λ : ℝ} (k i:ℕ) (hW:T.down.Bounds T.low σ C Λ) (hw:S'.push R.beta R.eval = earlyValue (Y') T.down T.low P Z R.beta H' g)
    (M:Trio.Offer G c) (hM:∀ i,P.Regular univ (M i))
    (hΛ:Meadow.Budget P (Y').reg (W.leftward κ g k i).logRead E)
    (x : Positions (Uniform.Primary c G)) (hx:‖x‖ + 2*furl G L u < v) (ha:flags P.threshold (actual x)=∅)
    (hΩ : ∀ W': Positions (Uniform.Primary c G),‖W'‖+2*furl G L u < v → actual W'∈ sunny P→ Brush m' s' v⁻¹ ((Boulevard.stillA (metricA T g R+Trio.froth M))∘actual) W') :
    ∀ l:List (Directions G c), l.length ≤ P.order → (∀ i∈l,‖i‖≤P.threshold) → ‖leftDerivs (Boulevard.stillA (Trio.froth (W.tot κ k i g-M))) l (actual x)‖ ≤ Boulevard.ticket m' s' + 2*((Fintype.card (Site c):ℝ)*E):= by
  have hh: P.threshold ≤ 2*Pressure.fiery G u L:= by rw [← H.laws.data.funds.length_eq,hP]; exact H.laws.data.room.temperatures
  let F:= W.tot κ k i g; let Q (x):=Trio.froth (F-M) x
  have hQ: P.Regular univ Q := by
    rw [show Q=∑ j:Site c,(F j-M j) from funext fun x=> (Finset.sum_apply x Finset.univ (fun i=>F i-M i)).symm]; exact Meadow.regularA _ (fun j _=> CouplingShape.reg_sub (CouplingShape.reg_extend (W.fire P he k i j hB) (subset_univ _)) (hM j))
  exact hp P ht hP hh x hx ha _ _ _ _ _ _ _ hΛ hQ (flatten T H W P he k i hW hB hw M) hΩ
end Bouquet
end YM.RGComparison01
