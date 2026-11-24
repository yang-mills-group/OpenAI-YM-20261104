import YM.LocalLTE.Dilation.Offset
import YM.LocalLTE.Slide.Ice
/-! Policy: expand base support only on nonwinding.Leg. Makes chart requests; population of large-spatial candidates uniform (on stated shells). -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Dilation
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Next.Foundations
open Planned.GuardedAtom Guard Push Local YM.MergeProof
open Pressure Tree Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{o:Site n}{P:BudgetPoint}
variable (o:Site n)(p:BudgetPoint)(l:ℕ)
local notation "Z"=> neighbors (l*p.B) o
noncomputable def sill (s:ℝ) (l:ℕ):= Real.exp ((s+2)*ballCost l)
noncomputable def silhouette (X:ℕ → Support n)(i:ℕ) : Support n:= if X i ⊆neighbors (l*p.B) o ∧ Nonwrapping (neighbors (l*p.B) o) o then neighbors (l*p.B) o else X i
local notation "r"=> sill p.supportExponent l
lemma roomy (X:ℕ→Support n) : Fills o X (silhouette o p l X) p (sill p.supportExponent l):=by
   let q:= p.supportExponent+2; have hc:0 ≤ q:= add_nonneg p.exponent_pos.le zero_le_two; have hV:1≤ r:=Real.one_le_exp (mul_nonneg hc (by positivity))
   refine ⟨hV,fun i=>?_,fun i _ =>?_,fun i t ht=>?_⟩
   · unfold silhouette; split; next h=>exact h.1
     rfl
   · unfold silhouette; split; next h=>exact h.2
     assumption
   unfold silhouette; split
   · change Real.exp (q*coverNumber p.B (Z: Support n))*t ≤ _; refine le_trans (mul_le_mul_of_nonneg_right (show Real.exp (q*coverNumber p.B (Z: Support n)) ≤ r from ?_) ht) (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
     · exact Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (PhysicalNext.Repeat.Scarf.standing _ _ l o le_rfl)) hc)
     exact le_mul_of_one_le_left ht (Real.one_le_exp (mul_nonneg hc (by positivity)))
   exact le_mul_of_one_le_left (mul_nonneg (Real.exp_pos _).le ht) hV
lemma allShoulders (X:ℕ→Support n)(i:ℕ)(hx:X i⊆ neighbors (l*p.B) o)(hp:10*(l*p.B)< n.val): silhouette o p l X i= neighbors (l*p.B) o := if_pos ⟨hx,fun j hj=>Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (by rw [separation_comm]; exact (neighbors_mem ..).1 hj)) hp⟩
end YM.LocalLTE.Dilation
