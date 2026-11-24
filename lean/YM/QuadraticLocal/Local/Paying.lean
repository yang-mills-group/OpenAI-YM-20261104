import YM.QuadraticLocal.Local.Waffle
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Venue
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open RemainderComparison RemainderComparison.Portal RemainderComparison.WickReps RemainderComparison.Aria.Pose
open AllOrder AllOrder.Catch AllOrder.Catch.Clock AllOrder.Wheel AllOrder.Wheel.Ride Further.LogJets AllOrder.Burn
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable (G:Gauge) (L:Side){η θ:ℝ}{Pᵥ:BudgetPoint}{α:Type*} {V:Type}[Fintype V]{k:ℕ}
open QuadraticLocal.Sunrise QuadraticLocal.Poetry
variable (P:RG.Stage)(J: V→Loan)
variable (a:ℝ) (h:0< a) (hv:0<θ)
namespace Crew
set_option quotPrecheck false
local notation "b₀" t:max=> bulk G L t
local notation "Λ"=> Base G L P
local notation "τ"=> Aux.fare G L
local notation "T₀"=> Sigma Λ
open Next.Rank.Glyph
variable {f n:Side}{K:BudgetPoint}{G L} (T:StepData n f)(R R':RG.Rep G f)(x:V→Site f)(Q:∀ i:V,Atom G (J i).r)
variable (Y:Config G n)
open QuadraticLocal.Echo
local notation "Z"=> Focus.census V
local notation "S*"=> (Set.univ: Set V)
lemma honor (hv:R'.eval=R.eval)(hβ:R'.beta=R.beta) (U:(Z).Mode) : Wry.theatre T R' J Q x U = Wry.theatre T R J Q x U:= by
 ext1 y; unfold Wry.theatre Wry.vote Wry.holding Wry.sector Wry.timeF; rw [hβ,hv]
-- Aura normalization ⊥ Vp; preserve tight β power for every wallet movement.Froots.Geometry costs. Θ.Sensor.URI.Rank
local notation "b" f:max=> Crew.earn (betaF G f L) a
abbrev adm (u:ℝ)(η :ℝ)(t:V→ℝ):V→ℝ:=fun i=> Crew.earn u η / t i
variable {P J} (U:ℝ) (N:ℕ)(hT:Viable (θ:=θ) G L P J a N U)
variable (t:V→ℝ)(hS:∀ i,0<t i)
set_option quotPrecheck false
local notation "AL"=> adm (betaF G U L) a t
include hT hS
lemma supported : ∀ i,0 < (AL) i:= fun i=> div_pos hT.small.1 (hS i)
lemma theory_mass (v:V→α→ℝ)(x:α)(h:∀ i,‖v i x‖≤1) (p:modes V):|Votes.picking (AL) t x v p|≤1:= by
 unfold Votes.picking; rw [Finset.abs_prod]; refine le_trans («b»:=∏ i∈p.val,(1:ℝ)) (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=>?_)) (by simp)
 rw [show t i * _ * _ = v i x * Crew.earn (betaF G U L) a from (by change t i * v i x*(b U/t i)=_; field_simp [(hS i).ne']), abs_mul]; -- hS function explicit
 rw [abs_of_pos hT.small.1]; exact (mul_le_mul (h i) hT.small.2 hT.small.1.le zero_le_one).trans_eq (one_mul _)
lemma freight (p:Finset V)(hp:0<betaF G U L): (1/∏ i∈p,(adm (betaF G U L) a t i))=(betaF G U L)^(a*p.card)*∏ i∈p,t i := by
 have hp' :∀ i, 0<t i:= hS
 unfold adm earn; rw [Real.rpow_neg hp.le a, Finset.prod_div_distrib,Finset.prod_const,Real.rpow_mul_natCast hp.le, inv_pow, one_div,inv_div]; field_simp -- lemma name verify
end Crew
end YM.QuadraticLocal.Venue
