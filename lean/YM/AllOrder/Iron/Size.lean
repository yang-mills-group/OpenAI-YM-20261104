import YM.AllOrder.Ker.Matrix
import YM.Push.STATIONARY_UNIFORM.Cost
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Iron
open Lattice Laurent Bloch Matrix Complex RG Push.Uniform Precision Push
open Progress.ClassicalKin Progress.ClassicalKin.Tent Function Wilson
open Primitives.TwoWave Primitives.TwoWave.RealSlice Further.PhysicalPeriodLimitF933 Shingle Macrame
open Gauge Tree Pressure Jacobi Finset Bid Exterior Filter Metric
open Ker.Start Ker
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge} {n:Side}
-- Genuine pre-L relation. Constants charged at post-L are independent of period.
lemma line_length (hn: 3≤n.val) (x y:Leaf n (Lobby P K G)):
    let B:= mapper P K G hn
    P.L.val*separation x.1 y.1 ≤ separation (address _ _ (B x)) (address _ _ (B y))+P.L.val:= by
    intro B; rw [← live P K hn x,← live P K hn y]; exact Corona.foreshorten (shores P n) _ _

variable {X: Side→Prop} {f : (n:Side)→ Positions (Joint (trees P K n) G)→ℝ}
variable {N k d:ℕ} {p:Clip}{R:PathData G}{O:ChartRatio G}
lemma sightline {a h c:ℝ}(ha:0 ≤ a) (ht:h ≤ P.L.val*a) (hf: ContDiffAt ℝ ω (f n) 0)
   (sc: Scatter (address (trees P K n) G) a N (f n) 0 c) (hn:3 ≤ n.val)(hk:k+1 ≤ N)(hc:0≤c) : Room (billed P K f k n) h (c*Real.exp (P.L.val*a*k)) := by
    intro i w; let L:= P.L.val; let t : Fin (k+1) → Leaf n (Lobby P K G) := Fin.cons i w
    let b:= mapper P K G hn; let B:= redesk b
    have he:= sc (k+1) hk (b ∘ t) 0; let x:=fun j=> address (trees P K n) G (b (t j)); let S:ℕ:=spanSites (address (trees P K n) G) (x 0) (b ∘ t)
    have hT: billed P K f k n i w = entry (f n) 0 (b ∘ t) := by
     unfold billed extractF tax; rw [dif_pos hn]; change iteratedFDeriv ℝ (k+1) (f n ∘ B.toContinuousLinearMap) _ _ = _; rw [Next.Foundations.jets_linear _ (hf.of_le le_top),ContinuousMultilinearMap.compContinuousLinearMap_apply]; exact congr_arg (⇑(iteratedFDeriv ℝ (k+1) (f n) 0)) (funext fun j=>desk_spot ..)
    rw [hT, ← Real.norm_eq_abs, mul_assoc,← Real.exp_add]; refine he.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) hc)
    let d:=∑ j:Fin k,separation i.1 (w j).1; change -a*(S:ℝ) ≤ L*a*(k:ℝ)+-h*d; have hh: L*d ≤ S+k*L := by calc
     L*d = ∑ j:Fin k,L*separation i.1 (w j).1:= by unfold d; rw [mul_sum]
     _ ≤ ∑ j:Fin k,(separation (x 0) (x j.succ)+L):= sum_le_sum fun j _=> (show L*separation (t 0).1 (t j.succ).1≤_ from line_length P K hn _ _)
     _ = _:= by unfold S spanSites; rw [Fin.sum_univ_succ, sum_add_distrib]; simp [x,b] -- edit
    have hu : (L:ℝ)*d≤S+k*L:=by exact_mod_cast hh
    have ht : h≤L*a:=ht; nlinarith only [mul_le_mul_of_nonneg_left hu ha,mul_le_mul_of_nonneg_right ht (by positivity : 0≤(d:ℝ))] -- edit type

def breath (a:ℝ)(N:ℕ):= weaker N (a/(8*((N:ℝ)+1)))
lemma breath_pos {a:ℝ}(ha:0<a) (N:ℕ):0<breath a N:= by unfold breath weaker; positivity
lemma promised {a:ℝ}(ha:0≤a): breath a N ≤ (P.L.val:ℝ)*weaker N (entryWidth N P.L a):= by
    let x:ℝ:= N+1
    let v:ℝ:=P.L.val
    have hx:0<x:=by unfold x; positivity
    have hv:1≤v:=by unfold v; exact_mod_cast (show 1 ≤ P.L.val from P.L.pos)
    unfold breath weaker; rw [← mul_div_assoc,entryWidth]; apply div_le_div_of_nonneg_right _ (by positivity)
    change a/(8*x) ≤ v * (a / (4*x*(1+v))); rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity : 0<8*x) (show 0 < 4*x*(1+v) by positivity)).2; nlinarith only [mul_le_mul_of_nonneg_left hv (mul_nonneg ha hx.le)]

end YM.AllOrder.Iron
