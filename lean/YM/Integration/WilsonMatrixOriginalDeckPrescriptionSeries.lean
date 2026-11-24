import YM.Integration.WilsonMatrixOriginalDeckPrescription

/-! Coefficients of the original full-height transfer between two logarithmic clocks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPrescriptionSeries
open MS MS.Menus MS.Local.Physical WilsonMatrixOriginalDeckPrescription
open scoped Classical BigOperators Matrix
variable {G:Gauge}{B:Deck G} (Q:MS.Land.Prescription B) (h:ℕ)
local notation "I"=>Glyph B h

def trial (μ ν:ℝ)(n:ℕ):Matrix I I ℂ:=
  (fees Q h μ 0)⁻¹ * (fees Q h ν n - ∑ j:Fin n, fees Q h μ (n-j.val) * trial μ ν j.val)
termination_by n
decreasing_by exact j.isLt

/-- The original zeroth invertible fee resolves the full truncated coefficient. -/
theorem measured (μ ν:ℝ)(n:ℕ):
    (∑j:Fin (n+1),fees Q h μ (n-j.val)*trial Q h μ ν j.val)=fees Q h ν n:=by
  have last:fees Q h μ 0*trial Q h μ ν n=
      fees Q h ν n-∑j:Fin n,fees Q h μ (n-j.val)*trial Q h μ ν j.val:=by
    rw [trial,←mul_assoc,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (original Q h μ)),one_mul]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,Nat.sub_self,last]
  abel

theorem born (μ ν:ℝ):fees Q h μ 0*trial Q h μ ν 0=fees Q h ν 0:=by simpa using measured Q h μ ν 0

end YM.Integration.WilsonMatrixOriginalDeckPrescriptionSeries
