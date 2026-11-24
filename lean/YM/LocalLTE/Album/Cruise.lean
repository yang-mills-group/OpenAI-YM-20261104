import YM.LocalLTE.Slide.Carving
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Brisk
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.PhysicalNext.Repeat.Scarf
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain Trio Marlin Push.BetaTransport Shingle
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L:Side} {X : Listing G c} {m r j k p:ℕ} {e d a Z K q b v Y : ℝ} {x:ℝ} {S:Set ℝ} {ι:Type}
-- primary ornament site widened, still full K mass allocation ONLY eligibility. Frame output may use m beyond (2*z) with flag tests.F.work
variable (B:BudgetPoint)(X : Listing G c) (s : Finset ℕ) (m : ℕ)

local notation "Y"=> diamond X s m

variable (z w:ℕ){f T:Collection.Source G c}(g t: Trio.Offer G c)
variable (hA: ∀ i:(Site c), Trio.Tidy B (neighbors w i) (t i)∧ (∀ V,t i V ≠0→¬ Healthy B.threshold (neighbors w i) V)∧ ∀ V, ‖t i V‖ ≤ e) (hk: Meadow.Budget B X.reg T.logRead a) (he: Meadow.Budget B (Marlin.leap z) g b) (hR: Rooms X.reg s m B p) (hh:z≤ m)(hx:m≤w)
local notation "U"=> hesitates B X s m z T t g
variable {L: Listing G c}{c₁ a' :ℝ}
    (hn:∀ i,L.hard i=X.hard i ∧ f.hardRead i=T.hardRead i)
    (ht: ∀ s b, Nonempty ((L.read f).Moves s b))
    (hv: ∀ s' b,Nonempty (((diamond X s m).read T).Moves s' b))
    (h:∀ V:Config G c,(L.read f).additive B V= (X.read T).additive B V+Fintype.card (Site c)*d+(∑ i, masked B.threshold (neighbors z i) (g i) V)+ ∑ i,t i V)
local notation "j₀"=> Marlin.lodge (diamond X s m) m w
local notation "t₀"=> Marlin.bison T g U
include ht h hv hk w hR
lemma carve_add (R:PathData G)(c':Clip)(β x :ℝ) (V:Config G c) :
    (Collection.frozen L R c' B f β x).exponent V= (Collection.frozen (Marlin.pluck B (j₀)) R c' B (Marlin.poursP B (j₀) (t₀)) β (x-d)).exponent V+(∑' i,(t₀).logarithm i V):=by
    refine Marlin.cruiseV B (diamond X s m) m w T g U V (R:=L) f R c' _ _ _ (Scarf.acreage X.reg s m B hR _ hk) ?_ ht hv
    intro W; rw [h W, Scarf.stratus B X s m hk hR W]; unfold hesitates; rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,Finset.sum_add_distrib]; abel
end YM.PhysicalNext.Repeat.Scarf
