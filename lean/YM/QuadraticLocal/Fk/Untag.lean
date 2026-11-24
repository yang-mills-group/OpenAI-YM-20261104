import YM.QuadraticLocal.Fk.Window
import YM.QuadraticLocal.Fk.Offer
/-!
# All the interactions, and pricing the pose discrepancies

Where used on `Budget.whole`: uses true unit cost of all terms, not volume-free bound inferred
 from convergence or stationarity elsewhere. We'll use exponential winding rate so even the
 polynomial multiplicity in this estimate is good. The analytic license for each cluster
 book doesn't alone pay for actual Step.Support readout.V_View outcome.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V:Type}{G:Gauge} {n c:Side} {k j e d r o:ℕ} {a b σ r' :ℝ}
open Aperture Poetry Echo Work.G05 Toggle Aux Aux.Name Marker Multi
open QuadraticLocal.Sunrise
variable {ι α : Type} [DecidableEq V] {P:Passport n V} {R:Census V}
variable (M:ι→ Row P R G α)
namespace Alliance
variable (q:ι→ℂ)(w:V→ℕ)(w':V→ℝ)
set_option quotPrecheck false
variable (H: Scene.Armada M w' w a b j k d)(he:0<a) (Q:Ratio c n)
local notation "F" p:max=> Accumulate.rootPrice M w' a p
local notation "I"=> Club M
local notation "Ψ"=> Q.parent
local notation "Lx"=> ((Q.count.val:ℝ)^4)
local notation "υ"=> univ
variable (hb:b≤1)
open RemainderComparison
local notation "T"=> Breeze.areaBudget c.val k Lx
local notation "x"=> (0:Site n)
private lemma scope (i:Site c): pdist i ≤ c.val:= Finset.sup_le (fun j _=> (ZMod.natAbs_valMinAbs_le (i j)).trans (by omega))
local notation "Z" p:max=> ( fun i:Club M=> if Accumulate.closer M Q i p c.val then Accumulate.rootPrice M w' a i else 0)
abbrev landing (b:ℝ):= Air.united c ( b*Breeze.areaBudget c.val k ((Q.count.val:ℝ)^4) )
local notation "Δ"=> ( Air.united c ( b*Breeze.areaBudget c.val k ((Q.count.val:ℝ)^4) ))
variable (hp:0≤ r')
include hb H
lemma airport : SumBudget (Accumulate.rootPrice M w' a) ( Air.united c ( b*Breeze.areaBudget c.val k ((Q.count.val:ℝ)^4) )):= by
 let f(i:Site c):=(Z i); have hu :∀ i:Site c,SumBudget (f i) (b*T):= Accumulate.inside k M Q w' H.positive H.suggests hb (fun z=> ( Club.cardLe M z).trans (H.quota _)) c.val
 have hx : (fun a'=>∑ i: Site c,f i a')= Accumulate.rootPrice M w' a:=by funext i; let y:= Club.reach M i Q; have hy : y≤c.val:= Club.extent_le M i Q fun j _=> scope _; unfold f Accumulate.closer; simp_rw [ ( show Club.reach M i Q ≤ c.val from hy ), true_and]; simp
 rw [← hx]; refine budget_loosen (budget_over (Finset.univ:Finset (Site c)) f _ (fun i _=> hu i)) (le_of_eq (by unfold Air.united; simp))
local notation "Px"=> Stationary.arm
open Comparison.RG02 Order
variable {S:StepData c n} {B₀:Clip} {D':PathData G}{O:ChartRatio G}
variable (K:Comparison.RG02.Bulk.Kernel S B₀ D' O)(X:Forest S.ratio)(t:S.Choices) (y:Stationary.Link G c)
variable (L:Layout G)(T':Finset Age)
local notation "x₀"=> (Stationary.arm G c 1 y)
local notation "Yp" p:max=> ScatterR.history M L T' K X t x₀ p r j
variable (p: Press M j) (u: Club M)
local notation "A" v:max=> Press.Newspapers M v p y r (Bunch.mapC (Club.site M v Q))
variable {hw:ℝ}
def seen (d:ℕ)(u:Club M):ℂ:= Complex.ofReal ( Press.Newspapers M u p y d ( Bunch.mapC ( Club.site M u Q)))
local notation "D" v:max=> seen M Q y p r v
def miss (d:ℕ)(u:Club M) : Poly R:= Poly.send (Club.alliance M u) ( (ScatterR.history M L T' K X t x₀ u d j - seen M Q y p d u)*(∏ i∈u.val,q i)) -- Lift alias recom
local notation "ν"=> Alliance.miss M q Q K X t y L T' p r
-- economics
variable (hq:∀ i, ‖q i‖ ≤ (M i).salary)
variable (δ:∀u, ‖ScatterR.history M L T' K X t (Stationary.arm G c 1 y) u r j - seen M Q y p r u‖ ≤ r')
include he hb hq hp δ
omit δ hb in
lemma vault (D':ℂ)(hc:‖D'‖≤r'): Poly.price w' (Poly.send (Club.alliance M u) (D'*(∏ i∈u.val,q i))) ≤ r'* Accumulate.rootPrice M w' a u:= by
 rw [Poly.solo,norm_mul,norm_prod,mul_left_comm,Accumulate.rootPrice, Finset.prod_mul_distrib, Club.union_price]; let f:= ∏ i∈u.val, Poly.toll w' (M i).mode; have hP:0 ≤ f:= Finset.prod_nonneg fun i _=> (Poly.worth H.positive _).le; refine mul_le_mul hc ?_ (mul_nonneg hP ( Finset.prod_nonneg (f:= fun i=> ‖q i‖) (fun i _=> norm_nonneg _))) hp; exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _=> norm_nonneg (q i)) (fun i _=> (hq i).trans (Air.heel M w w' H he i))) hP
lemma receipt : SumBudget (fun u: Club M=> Poly.price w' ( Alliance.miss M q Q K X t y L T' p r u)) ( r'*Air.united c ( b*Breeze.areaBudget c.val k ((Q.count.val:ℝ)^4) )):= by
 let f (i:Club M):= ScatterR.history M L T' K X t x₀ i r j - seen M Q y p r i
 have hτ(i:Club M): Poly.price w' ( Poly.send (Club.alliance M i) (f i * (∏ j∈i.val,q j))) ≤ (r'*Accumulate.rootPrice M w' a i) := by
    have hx: ‖f i‖ ≤ r':= δ i
    exact Alliance.vault M q w w' H he hp i hq (f i) hx
 exact budget_mono (budget_scale hp (Alliance.airport M w w' H Q hb)) (fun i=>Poly.nonnegative H.positive _) (fun i=> hτ i)


lemma identification : Summable ( Alliance.miss M q Q K X t y L T' p r) ∧ Poly.price w' ( ∑' u:Club M, Alliance.miss M q Q K X t y L T' p r u ) ≤ ( r'*Air.united c ( b*Breeze.areaBudget c.val k ((Q.count.val:ℝ)^4) )):= by
 let f:= Alliance.miss M q Q K X t y L T' p r; let B:= Δ; have ht:= Alliance.receipt M q w w' H he Q hb hp K X t y L T' p hq δ -- signature
 obtain ⟨l,hl,h⟩:= Poly.equivalent_norm (R:=R) H.positive; have he: Summable f:= Summable.of_norm_bounded (ht.2.1.mul_right l) fun i=> h _
 exact ⟨he, le_of_tendsto' ((Poly.price_cont w').tendsto _|>.comp he.hasSum) (fun i=> ( Poly.batch H.positive i f).trans ( budget_sum ht i ))⟩ -- elaborates `HasSum`
end Alliance
end YM.QuadraticLocal.Earn
