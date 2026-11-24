import YM.Next.MAXWELL.Algebra
import YM.Next.MAXWELL.House

set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open WaveOn Wick
open scoped ContDiff Topology BigOperators InnerProductSpace
variable {G: Gauge} {l: ℕ}
def phi (a b i l : Axis) : WickPol G := ∑ c : G.ColorIndex,
  symbol 0 (omegaLeg c a i)*symbol 0 (omegaLeg c b l)
def sheetEnergy (a b : Axis) : WickPol G := ∑ i : Axis, phi a b i i
def polStress (G : Gauge) (a b : Axis) : WickPol G := sheetEnergy a b -
  (((kr a b * (1/4):ℝ):ℂ)) • ∑ i : Axis, sheetEnergy i i
lemma measure_phi (a b i l : Axis) (A : TaylorTower G) :
    probe A (phi a b i l) = (⟪asWave (A 0) a i 0, asWave (A 0) b l 0⟫_ℝ : ℂ) := by
  have he (c : G.ColorIndex) (a b) : omegaLeg c a b (A 0) = asWave (A 0) a b 0 c := rfl
  unfold phi; simp_rw [map_sum,map_mul,symbol_test,he, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1; rw [real_inner_comm, EuclideanSpace.inner_eq_star_dotProduct]; rfl
lemma shade_phi (a b i l : Axis) (u : G.El) : pigment u (phi a b i l)=phi a b i l := by
  apply equalPol; intro A; rw [pigment_action, measure_phi, measure_phi]
  let L : G.Color →ₗᵢ[ℝ] G.Color := ⟨G.adjoint u,G.norm_adjoint u⟩
  exact congr_arg (fun t : ℝ => (t:ℂ)) (L.inner_map_map (asWave (A 0) a i 0) (asWave (A 0) b l 0))
theorem stress_label (G : Gauge) (a b : Axis) : polStress G a b ∈ shellSector G 4 := by
  have he (a b i l) : MvPolynomial.IsWeightedHomogeneous scaleW (phi (G:=G) a b i l) 4 := by
    unfold phi; apply MvPolynomial.IsWeightedHomogeneous.sum
    intro c _; exact (symbol_hom (omegaLeg (G:=G) c a i) (fun i => i+2)).mul
      (symbol_hom (omegaLeg (G:=G) c b l) (fun i => i+2))
  have ht (a b : Axis) : sheetEnergy (G:=G) a b∈ lowerCap G 4 := by
    apply Submodule.sum_mem
    intro i _; rw [lowerCap,MvPolynomial.mem_restrictSupport_iff]
    intro p hp; change degree p ≤ 4
    exact (he a b i i (MvPolynomial.mem_support_iff.mp hp)).le
  apply sector.mpr
  refine ⟨Submodule.sub_mem _ (ht a b) (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ht i i)),?_⟩
  intro u; simp only [polStress,sheetEnergy,map_smul,map_sum,map_sub,shade_phi]
end YM.Maxwell.Free
