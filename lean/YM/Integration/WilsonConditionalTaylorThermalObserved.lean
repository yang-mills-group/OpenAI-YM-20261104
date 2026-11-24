import YM.Integration.WilsonConditionalTaylorThermalQuotient

/-! Common lower coefficients and the Poincaré expansion of the signed
difference of the original two conditioned Wilson observables. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalObserved
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open PertExtension PertExtension.Series Tested Radial GaussianScore RGComparison.Core16.Descent
open RGComparison.Core16 WilsonConditionalTaylorThermalLaplace WilsonConditionalTaylorThermalBook
open WilsonConditionalTaylorThermalDivision PowerSeries
open scoped Topology ContDiff Classical BigOperators

private theorem divided {N U V D : PowerSeries ℝ} {w : ℕ}
    (d0 : coeff 0 D ≠ 0) (v0 : coeff 0 V ≠ 0) (old : zeroBefore N w)
    (inputs : zeroBefore (U-N) (w+2)) (vacua : zeroBefore (D-V) 2) :
    zeroBefore (U*D⁻¹-N*V⁻¹) (w+2) := by
  have free (X : PowerSeries ℝ) : zeroBefore X 0 := by intro k hk; omega
  have d := PowerSeries.mul_inv_cancel D (by simpa only [← coeff_zero_eq_constantCoeff_apply] using d0)
  have v := PowerSeries.mul_inv_cancel V (by simpa only [← coeff_zero_eq_constantCoeff_apply] using v0)
  let O := N*V⁻¹
  have hO : zeroBefore O w := by simpa only [Nat.add_zero] using productLower old (free V⁻¹)
  let A := (U-N)-O*(D-V)
  have hA : zeroBefore A (w+2) := by
    intro i hi
    rw [show coeff i A = _ - _ from map_sub ..,inputs i hi,productLower hO vacua i hi,sub_zero]
  have identity : U*D⁻¹-N*V⁻¹ = A*D⁻¹ := by
    have Oeq : O*V=N := by dsimp [O]; rw [mul_assoc,mul_comm V⁻¹ V,v,mul_one]
    have aeq : A = U-O*D := by dsimp only [A]; rw [mul_sub,Oeq]; ring
    rw [aeq,sub_mul,mul_assoc,d,mul_one]
  rw [identity]
  simpa only [Nat.add_zero] using productLower hA (free D⁻¹)

private theorem difference {f h : ℝ → ℝ} {a b : ℕ → ℝ}
    (left : Aspiration f a) (right : Aspiration h b) : Aspiration (f-h) (a-b) := by
  intro n
  obtain ⟨A,hA,ha⟩ := left n
  obtain ⟨B,hB,hb⟩ := right n
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  filter_upwards [ha,hb] with g ga gb
  have poly : peval (a-b) n g = peval a n g-peval b n g := by
    simp [peval,Zone.eval,mul_sub,Finset.sum_sub_distrib]
  change ‖(f g-h g)-peval (a-b) n g‖ ≤ _
  rw [poly,show (f g-h g)-(peval a n g-peval b n g)=(f g-peval a n g)-(h g-peval b n g) by ring]
  exact (norm_sub_le ..).trans ((add_le_add ga gb).trans_eq (add_mul ..).symm)

variable {G : Gauge} {n c : Side} {d : Descent n c} (P : ChartRatio G) (R : LocalRatio P)
    (room : d.Room G) (tag : d.Tags) (u v : ℕ → ℝ) {f : Config G n → ℝ}
    (test : d.Testable f) {w : ℕ} (grade : d.grade f w)
include R room test grade in
theorem before (e : ℕ) (early : e < w+2) :
    ranking P d u f e = ranking P d v f e := by
  let A (z : ℕ → ℝ) (h : Config G n → ℝ) := PowerSeries.mk (bareRank P d z h)
  have piv (z : ℕ → ℝ) : coeff 0 (A z 1) ≠ 0 := by simpa [A] using (pivot P R z room).ne'
  have old : zeroBefore (A v f) w := by
    intro i hi
    simpa [A] using field_rank_zero P R room v test grade i hi
  have changes {h : Config G n → ℝ} {k : ℕ} (ok : d.Testable h) (g : d.grade h k) :
      zeroBefore (A u h-A v h) (k+2) := by
    intro i hi
    simp only [A,map_sub,coeff_mk,sub_eq_zero]
    exact WilsonConditionalTaylorThermalBook.lower P R room u v ok g i hi
  have vacuumChange := changes (unit_test d) (unitGrade (G:=G) (d:=d))
  have hz := divided (piv u) (piv v) old (changes test grade)
    (by simpa only [Nat.zero_add] using vacuumChange) e early
  change coeff e (A u f*(A u 1)⁻¹) = coeff e (A v f*(A v 1)⁻¹)
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

include R test grade in
theorem original :
    Aspiration ((fun g => d.conditioned (offset u g) f 1)-(fun g => d.conditioned (offset v g) f 1))
      (ranking P d u f - ranking P d v f) ∧
    (∀e < w+2, ranking P d u f e = ranking P d v f e) ∧
    ranking P d u f (w+2)-ranking P d v f (w+2) =
      -ThermalShortcuts.ConnectedWick.connected (ambient tag room) (Chart.tangent G d.Links)
        (ThermalShortcuts.ThermalJets.signedForm G d tag (u-v)) (field (d:=d) f w) := by
  exact ⟨difference (coefficient_formula P R u room test) (coefficient_formula P R v room test),
    before P R room u v test grade,WilsonConditionalTaylorThermalQuotient.original P R room tag u v test grade⟩

end YM.Integration.WilsonConditionalTaylorThermalObserved
