import YM.Integration.WilsonPositionProgramInvertedStencil

/-! The one original normalized tree changes the coordinates of every
full series and preserves its scalar and coupling variable. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramInversionAlgebra
open WilsonCoeffUV WilsonCoeffUV.Blue XSpace PowerSeries MvPolynomial
open WilsonPositionProgramInvertedStencil WilsonPositionProgramRayChart
open scoped Classical BigOperators
variable {G : Gauge} {p : Period} (T : p.Tree)
local notation "U" => Woods G p.side

def income : PowerSeries ℂ →+* Bare.Series T G := PowerSeries.map (algebraMap ℂ (Bare.Vertices T G))

theorem scalar (s : PowerSeries ℝ) :
    packet (G:=G) T (soil s) = income T (PowerSeries.map (algebraMap ℝ ℂ) s) := by
  apply PowerSeries.ext
  intro n
  simp only [packet,WilsonPositionProgramRayChart.pull,loom,soil, income,
    RingHom.comp_apply,PowerSeries.coeff_map]
  simp [cord,MvPolynomial.algebraMap_eq]

theorem unturned (K : Matrix U U ℝ) (s : PowerSeries ℝ) : loom K (soil s)=soil s := by
  apply PowerSeries.ext
  intro n
  simp only [loom,soil,PowerSeries.coeff_map]
  simp [cord,MvPolynomial.algebraMap_eq]

theorem smul (c : ℝ) (f : Ink U) : c • f=soil (PowerSeries.C c)*f := by
  rw [Algebra.smul_def,soil,PowerSeries.map_C]
  rw [PowerSeries.algebraMap_apply,MvPolynomial.algebraMap_eq]

theorem term (K : Matrix U U ℝ) (s : PowerSeries ℝ) (c : ℝ) (f : Ink U) (n : ℕ) :
    packet T (loom K ((PowerSeries.X : Ink U)^n * soil s * (c • f))) =
      income T (PowerSeries.X^n * (PowerSeries.map (algebraMap ℝ ℂ) s * PowerSeries.C (c:ℂ))) *
        packet T (loom K f) := by
  have keep : packet T (loom K PowerSeries.X) = income T PowerSeries.X := by
    simp [packet,WilsonPositionProgramRayChart.pull,loom,income]
  simp only [smul c f,map_mul,map_pow,unturned,scalar T,PowerSeries.map_C,keep]
  rw [show (algebraMap ℝ ℂ) c=(c:ℂ) from rfl]
  ring

end YM.Integration.WilsonPositionProgramInversionAlgebra
end
