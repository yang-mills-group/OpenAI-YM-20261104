import YM.Next.STATIONARY.Joint.OnShell
import YM.AllOrder.Haiku.Deduce
import YM.AllOrder.Local.Taylor
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Haiku
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Response Ink Ink.Method Ink.Money
open Tree Wilson Exterior Precision Push Pressure Next.Fluctuations MeasureTheory
open Stationary
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n m c:Side}{a C D:ℝ}{k N:ℕ} {ι:Type}
local notation "L"=> Coarse G
-- defeq Ward.Link footing
local notation "F[" n "]"=> Stationary.Link G n

namespace Project
open PertExtension.Series Radial
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
section simp
variable (f:X→ℝ)
lemma maturity (k:ℕ): Rank X k (jet f k):=(Rank.hom (ContinuousLinearMap.id ℝ X) (iteratedFDeriv ℝ k f 0)).scal _
lemma stroll (k:ℕ) : jet f k=Tensor.diagonal (Tensor.coeff f k 0):= rfl
lemma self (hf:ContDiffAt ℝ ω f 0)(k:ℕ): iteratedFDeriv ℝ k (jet f k) 0=iteratedFDeriv ℝ k f 0 := by
 rcases k with _|k; · ext1 i; simp
 rw [stroll,show Tensor.diagonal (Tensor.coeff f (k+1) 0) = Work.G05.blockTaylor (k+1) f- Work.G05.blockTaylor k f from ?_]; swap; · unfold Work.G05.blockTaylor; rw [Finset.sum_range_succ]; abel
 rw [iteratedFDeriv_sub_apply (Work.G05.blockTaylor_contDiff ..|>.contDiffAt) (Work.G05.blockTaylor_contDiff ..|>.contDiffAt), Work.G05.blockTaylor_jets (d:=k+1) (hf.of_le le_top) (k+1) le_rfl, AllOrder.Local.Taylor.t_above f (Nat.lt_succ_self _), Pi.zero_apply, sub_zero]
lemma other (hk:k≠N) : iteratedFDeriv ℝ N (jet f k) 0=0:= by
 rw [stroll]; rcases lt_or_gt_of_ne hk with hk|hk; exact congr_fun (AllOrder.Local.Taylor.diag_above _ hk) 0; exact AllOrder.Local.Taylor.diag_flat _ N hk
end simp
lemma still_one (hG:G.Simple) {F:Stationary.Link G n →ℝ}(h:Stained G F)(he:AnalyticAt ℝ F 0): iteratedFDeriv ℝ 1 F 0=0:= by
   have hh : fderiv ℝ F 0=0 := by
     apply ContinuousLinearMap.ext; intro i; exact oneFlag hG (fderiv ℝ F 0) (fun u v=>by rw [← tincture u]; exact chain_fixed _ (h u) he.differentiableAt v) i
   ext1 i; simp [hh]
end Project
end YM.AllOrder.Haiku
