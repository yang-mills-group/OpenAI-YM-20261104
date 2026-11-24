import YM.Integration.WilsonConditionalTaylorThermalHaarOdd
import YM.Integration.WilsonConditionalTaylorThermalFourthLinked

/-! The remaining Haar insertion is one fixed color-space quadratic
form at every occupied bond. Its norm precedes the whole finite descent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalOnsite
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial
open WilsonConditionalTaylorThermalLogHaar WilsonConditionalTaylorThermalFourthLinked
open scoped Classical BigOperators ContDiff
variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "E" => Coordinates G d

def quadratic (P : ChartRatio G) (z : G.Color) := jet (Chart.fee P) 2 z/P.scale
def price (P : ChartRatio G) := (2:ℝ)⁻¹ * ‖iteratedFDeriv ℝ 2 (Chart.fee P) 0‖/P.scale

theorem component (P : ChartRatio G) (R : LocalRatio P) (i : d.Links) (k : ℕ) (x : E) :
    jet (leaf P i) k x=jet (Chart.fee P) k (x i) := by
  have s : ContDiffAt ℝ ∞ (Chart.fee P) ((0:E) i) := (Chart.Ratio.fee_smooth R).of_le (by simp)
  have left := directions (s.comp (f:=fun y:E=>y i) 0 (contDiffAt_apply ℝ G.Color _ _)) x
  have right := directions (f:=Chart.fee P) s (x i)
  exact congrFun (left.unique right) k

theorem original (P : ChartRatio G) (R : LocalRatio P) (t : d.Tags) (x : E) :
    localTerm P t x=(∑i:d.Links,quadratic P (x i))-jet (d.phase G t) 4 x := by
  have unit (i:d.Links) : leaf P i (0:E)=P.scale := by
    change max (P.scale*P.J 0) 0=P.scale
    rw [R.anchored,mul_one,max_eq_left R.scale.le]
  simp only [localTerm,WilsonConditionalTaylorThermalHaarOdd.onsite P R x,component P R,unit,quadratic]

theorem bound (P : ChartRatio G) (R : LocalRatio P) (z : G.Color) :
    |quadratic P z| ≤ price P*‖z‖^2 := by
  let A := iteratedFDeriv ℝ 2 (Chart.fee P) 0
  have linear := A.le_opNorm (fun _:Fin 2=>z)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Real.norm_eq_abs] at linear
  change |((Nat.factorial 2:ℝ)⁻¹*A (fun _=>z))/P.scale|≤((2:ℝ)⁻¹*‖A‖/P.scale)*‖z‖^2
  rw [abs_div,abs_of_pos R.scale,abs_mul,abs_of_pos (by positivity:0<((Nat.factorial 2:ℝ))⁻¹)]
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat]
  calc
    _ ≤ (2:ℝ)⁻¹*(‖A‖*‖z‖^2)/P.scale := by gcongr <;> first | exact R.scale.le | norm_num
    _ = _ := by ring

end YM.Integration.WilsonConditionalTaylorThermalOnsite
