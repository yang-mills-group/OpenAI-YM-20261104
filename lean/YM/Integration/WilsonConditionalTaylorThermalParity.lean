import YM.PertExtension.OrbParity
import YM.Integration.WilsonConditionalTaylorThermalInteractionDivision
import YM.Integration.WilsonConditionalTaylorThermalMixedQuotient

/-! At the flat held field the entire original tagged descent has even
coupling parity, including its finite-temperature vacuum denominator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalParity
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalLaplace PowerSeries
open scoped Classical BigOperators ContDiff Topology
variable {G : Gauge} {n c : Side} {d : Descent n c}

theorem unnormalized (P : ChartRatio G) (z : ℕ→ℝ) (f : Config G n→ℝ) {k : ℕ} (odd : Odd k) :
    bareRank P d z f k=0 := by
  let μ := Chart.tangent G d.Links
  letI : μ.IsNegInvariant :=
    ⟨(measurePreserving_pi _ _ (fun (_ : d.Links)=>Measure.measurePreserving_neg (volume : Measure G.Color))).map_eq⟩
  unfold bareRank
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero;intro t _
  let K := nearFee P t (d.resetTerms z f t)
  let S := d.phase G t
  change (∫u, normTerm K S k u ∂μ)=0
  have e (u) : normTerm K S k (-u) = -normTerm K S k u := by
    rw [PertExtension.Orb.kerTerms_neg,odd.neg_one_pow,neg_one_mul]
  have shift := integral_neg_eq_self (normTerm K S k) μ
  simp_rw [e] at shift
  rw [integral_neg] at shift
  linarith

theorem full (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (z : ℕ→ℝ) (f : Config G n→ℝ)
    {k : ℕ} (odd : Odd k) : ranking P d z f k=0 := by
  let N := PowerSeries.mk (bareRank P d z f)
  let V := PowerSeries.mk (bareRank P d z (1 : Config G n→ℝ))
  have pos : coeff 0 V≠0 := by simpa only [V,coeff_mk] using (pivot P R z room).ne'
  have unit := WilsonConditionalTaylorThermalInteractionDivision.normalized (N:=N) pos
  have read (i : ℕ) : coeff i (N*V⁻¹)=ranking P d z f i := rfl
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have H := congrArg (coeff k (R:=ℝ)) unit
    rw [coeff_mul] at H
    simp only [read,V,N,coeff_mk,unnormalized P z f odd] at H
    rw [Finset.sum_eq_single_of_mem (k,0) (Finset.mem_antidiagonal.mpr (add_zero k))] at H
    · exact (eq_zero_or_eq_zero_of_mul_eq_zero H).resolve_right (pivot P R z room).ne'
    intro ⟨a,b⟩ hab ne
    have add : a+b=k := Finset.mem_antidiagonal.mp hab
    rcases Nat.even_or_odd b with even|bo
    · have smaller : a<k := by
        by_contra! w
        apply ne
        ext1 <;> simp [show a=k by omega,show b=0 by omega]
      have ao : Odd a := by obtain ⟨j,e⟩:=even;obtain ⟨r,h⟩:=odd;exact ⟨r-j,by omega⟩
      rw [ih a smaller ao,zero_mul]
    · rw [unnormalized P z 1 bo,mul_zero]

theorem directions (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (z a b : ℕ→ℝ)
    (f : Config G n→ℝ) {k : ℕ} (odd : Odd k) :
    WilsonConditionalTaylorThermalMixedQuotient.difference P d z a b f k=0 := by
  simp only [WilsonConditionalTaylorThermalMixedQuotient.difference,WilsonConditionalTaylorThermalMixedDivision.square,
    full P R room _ f odd,sub_zero]

end YM.Integration.WilsonConditionalTaylorThermalParity
