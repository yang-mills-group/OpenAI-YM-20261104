import YM.AllOrder.Floe.Acre
import YM.AllOrder.Floe.Topo
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Harmonic
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Atlas
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω:ℝ}{k r m n N l:ℕ}{j:Side}
open Rent PriceCompiler
namespace PlanV
variable (g:G.Simple) (A:ℕ→Stage)(d f:ℕ→ℝ)(U:MapPrices)
/-! Preparatory price real cutoff at grade cap k+2≤J. choose before L. Record stable witness. No paying post-L operator constants for carry. -/
open Iron
variable (K:KernelChoices)
def baseS (x:ℕ): Sky K G x (U.α x) (|U.Ω x|) (U.η x):= Classical.choice (outlook _ _ _ _ _ _ (U.alpha_pos x) (abs_nonneg _) (U.eta_pos x))
-- Sky threshold, invoice pre widths shrink. Align real Stage.
local notation "m₀"=> baseS (G:=G) U K
abbrev arms (G:Gauge)(k x:ℕ): ℝ:= min (leaseF (A x).width (k+2)) ((baseS (G:=G) U K x).width)
lemma arms_p(G:Gauge)(k x:ℕ):0<arms A U K G k x:= lt_min (lease_pos (A x).width_pos _) ((baseS U K x).pos)
structure Roots where
   pre : ℕ → ℕ → Fees
   shape k: Concession A U (arms A U K G k) G (k+2) (fun _ _=>1) (pre k)
-- Post Career comparisons independent Φ Monitor scale. uniform cost folded. Could take rate (`≤1/8`). Lifts & clocks through allocations. preserve via Raise.
include g
lemma acquire : Nonempty (Roots (G:=G) A U K):= by choose s hs using fun n => lease g A U (fun _ _=>1) (arms A U K G n) (n+2) (fun _ _=>by norm_num) (fun i=>arms_p ..); exact ⟨s,hs⟩ -- arg order
omit g
variable {A U K}
namespace Roots
variable (R:Roots (G:=G) A U K) (x y k:ℕ)
abbrev rake (x:ℕ)(a:Age):=R.pre k x a
-- avoids Floor lifts by metric α price thus career with abs always. record
local notation "Ω₀"=> fun (x:ℕ)=> |U.Ω x|
abbrev wage (L:ℝ)(i:Age):= StateE.career i.r L (R.pre k x i) (R.pre k y i) (|U.Ω x|) (|U.Ω y|)
structure Tall (L:ℝ)(i:Age):Prop where
 rent : wage R x y k L i ≤ 1/4
 door : R.pre k y i ≤ R.pre k x i /2 * L

def Rise (x:ℕ)(L:ℝ):=∀ y (h:StepStages x y), ∀ k,k+2≤y→ ∀ i∈Age.scope (k+2),Tall R x y k L i
lemma tall_late(i:Age):∀ᶠ L:ℝ in atTop,Tall R x y k L i:= by
 have hv (b:ℝ) (k:ℕ) (h:0<k) : Tendsto (fun L:ℝ=> b/L^k) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega));
 have he:Tendsto (fun L:ℝ=> wage R x y k L i) atTop (𝓝 0):= by unfold wage career; split; exact hv _ _ (by norm_num); rename_i h; exact hv _ _ (by unfold Age.r at *; omega)
 filter_upwards [(he.eventually (ge_mem_nhds (show 0<(1/4:ℝ) by norm_num))), (tendsto_id.const_mul_atTop (half_pos (R.shape k|>.pos x i))).eventually_ge_atTop (R.pre k y i)] with i hi hl; exact ⟨hi,hl⟩
lemma rise_late :∀ᶠ L:ℝ in atTop,R.Rise x L:= eventually_transitions _ _ _ fun y h=> by
 let T L k:= k+2 ≤ y → ∀ i∈Age.scope (k+2), Tall R x y k L i
 have hx k :∀ᶠ L:ℝ in atTop, T L k := by filter_upwards [(Filter.eventually_all_finset (I:=Age.scope (k+2)) (p:=fun i L=>Tall R x y k L i)).mpr (fun i _=> R.tall_late x y k i)] with L h; exact fun _=>h
 filter_upwards [(Filter.eventually_all_finset (I:=range (y+1)) (p:=swap T)).mpr (fun k _=> hx k)] with L h; exact fun k hk=> h k (Finset.mem_range.mpr (by omega)) hk
-- consumer actual transfer uniform & Formal nontrivial
lemma prize :∃ ν:ℕ→ℕ, ∀ x (L:Side),ν x ≤ L.val→R.Rise x L.val:= by
 choose u hu using fun x => Filter.eventually_atTop.mp (R.rise_late x); choose f hf using fun x => exists_nat_gt (u x); exact ⟨f,fun x L h=>hu x _ ((hf x).le.trans (Nat.cast_le.mpr h))⟩
end Roots
end PlanV
end YM.AllOrder.Floe.Step
