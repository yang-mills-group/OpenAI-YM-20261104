import YM.Integration.WilsonConditionalTaylorThermalBook
import YM.Integration.WilsonConditionalTaylorThermalDivision
import YangMills.WilsonProof.NativeSupport.ConnectedWick

/-! The first temperature-dependent coefficient of the original Core16
normalized history is a negative connected insertion. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonConditionalTaylorThermalQuotient
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open PertExtension PertExtension.Series Tested Radial GaussianScore RGComparison.Core16.Descent
open RGComparison.Core16 WilsonConditionalTaylorThermalLaplace WilsonConditionalTaylorThermalBook
open PowerSeries
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge} {n c : Side} {d : Descent n c} (P : ChartRatio G) (R : LocalRatio P)
    (room : d.Room G)
local notation "E" => Coordinates G d
local notation "μ" => Chart.tangent G d.Links

include R in
theorem original (t : d.Tags) (u v : ℕ → ℝ) {f : Config G n → ℝ}
    (test : d.Testable f) {w : ℕ} (grade : d.grade f w) :
    ranking P d u f (w+2) - ranking P d v f (w+2) =
      -ThermalShortcuts.ConnectedWick.connected (ambient t room) μ
        (ThermalShortcuts.ThermalJets.signedForm G d t (u-v)) (field (d:=d) f w) := by
  let A (z : ℕ → ℝ) (h : Config G n → ℝ) := PowerSeries.mk (bareRank P d z h)
  have pivot' (z : ℕ → ℝ) : coeff 0 (A z 1) ≠ 0 := by simpa [A] using (pivot P R z room).ne'
  have old : WilsonConditionalTaylorThermalDivision.zeroBefore (A v f) w := by
    intro i hi
    simpa [A] using field_rank_zero P R room v test grade i hi
  have changes {h : Config G n → ℝ} (ok : d.Testable h) {k : ℕ} (hp : d.grade h k) :
      WilsonConditionalTaylorThermalDivision.zeroBefore (A u h-A v h) (k+2) := by
    intro i hi
    simp only [A,map_sub,coeff_mk,sub_eq_zero]
    exact WilsonConditionalTaylorThermalBook.lower P R room u v ok hp i hi
  have vacuumChange' := changes (unit_test d) (unitGrade (G:=G) (d:=d))
  have q := WilsonConditionalTaylorThermalDivision.changed (pivot' u) (pivot' v) old
    (changes test grade) (by simpa only [Nat.zero_add] using vacuumChange')
  have cost : scale P t ≠ 0 := by rw [←vacuum P R room t u]; exact (pivot P R u room).ne'
  change coeff (w+2) (A u f*(A u 1)⁻¹) - coeff (w+2) (A v f*(A v 1)⁻¹) = _
  rw [← map_sub,q]
  simp only [A,map_sub,coeff_mk,sourceChange P R room t u v test grade,
    vacuumChange P R room t u v,source P R room t v test grade,vacuum P R room t v,
    vacuum P R room t u]
  have z : vertex (G:=G) t (u-v) =
      ThermalShortcuts.ConnectedWick.quadratic (ThermalShortcuts.ThermalJets.signedForm G d t (u-v)) :=
    funext (ThermalShortcuts.ThermalJets.signed_half t (u-v))
  unfold ThermalShortcuts.ConnectedWick.connected
  rw [←z]
  field_simp
  ring

end YM.Integration.WilsonConditionalTaylorThermalQuotient
