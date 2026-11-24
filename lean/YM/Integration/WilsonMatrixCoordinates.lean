import YM.Integration.WilsonLinkAmplitudeExpansion

/-! A finite real coordinate representation of every right-translated linear Wilson matrix probe. -/
noncomputable section
namespace YM.Integration.WilsonMatrixCoordinates
open YM Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators Classical
variable (G : Gauge)

abbrev Index := Fin (Module.finrank ℝ G.Mat)

def basis := Module.finBasis ℝ G.Mat

def coordinate (i : Index G) : G.Mat →L[ℝ] ℝ :=
  { (basis G).coord i with cont := ((basis G).coord i).continuous_of_finiteDimensional }

def weight (B : G.Mat →L[ℝ] ℝ) (i : Index G) (q : G.El) : ℝ :=
  B (basis G i * G.mat q)

theorem decompose (B : G.Mat →L[ℝ] ℝ) (q g : G.El) :
    B (G.mat (g*q)) = ∑ i, weight G B i q * coordinate G i (G.mat g) := by
  have h : (∑ i, coordinate G i (G.mat g) • basis G i) = G.mat g :=
    (basis G).sum_repr (G.mat g)
  calc _ = B ((∑ i, coordinate G i (G.mat g) • basis G i) * G.mat q) := by rw [h,G.mat_mul]
       _ = ∑ i, coordinate G i (G.mat g) * weight G B i q := by
            simp only [Finset.sum_mul,smul_mul_assoc,map_sum,map_smul,smul_eq_mul,weight]
       _ = _ := by
            apply Finset.sum_congr rfl
            intro i _
            exact mul_comm _ _

theorem budget (B : G.Mat →L[ℝ] ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q : G.El, (∑ i, |weight G B i q|) ≤ M := by
  have he i : Continuous (weight G B i) :=
    B.continuous.comp (continuous_const.mul G.continuous_mat)
  have hc : Continuous (fun q : G.El => ∑ i, |weight G B i q|) := by
    apply continuous_finsetSum
    intro i _
    exact (he i).abs
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hh (q : G.El) : (∑ i, |weight G B i q|) ≤ M := by
    have hn : 0 ≤ ∑ i, |weight G B i q| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using hM q (Set.mem_univ _)
  exact ⟨M,(Finset.sum_nonneg fun _ _ => abs_nonneg _).trans (hh 1),hh⟩

end YM.Integration.WilsonMatrixCoordinates
