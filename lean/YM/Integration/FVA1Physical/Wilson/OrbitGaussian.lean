import YM.Integration.FVA1Physical.Wilson.OrbitKernel
import YM.MSbar.Folia.Life

/-! Write the independent conditional orbit law as a Gaussian integral, retaining
the full exponential-coordinate Haar Jacobian and the same cut in both integrals. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Lattice RG YM.Wilson Tree Precision Matrix
open Further.GaussianScalar MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Bakery MSbar.Bakery.Film
open Next.SectorChange MSbar.Whisk MSbar.Cacao
open scoped Classical Topology
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (F : Forest S.ratio) (X Y : Support f) (A : Set (Config G f))
variable (γ : ChartRatio G) (m : SpaceP F X G)
variable (C : Matrix (↥(board F X) × G.ColorIndex) (↥(board F X) × G.ColorIndex) ℝ) (τ : ℝ)
variable (P φ : Config G f → ℝ) (U : Config G f)

def gaussianMass : ℝ :=
  ∫ v : SpaceP F X G, Portal.purse (clipM F X Y A γ τ m U)
      (fun z=>fLog F X γ τ z m U P C) v * φ (draw F X U m τ v) ∂fieldLaw C

def gaussianOrbit : ℝ :=
  if gaussianMass F X Y A γ m C τ P 1 U=0 then φ 1
  else gaussianMass F X Y A γ m C τ P φ U / gaussianMass F X Y A γ m C τ P 1 U

variable (hγ : LocalRatio γ) (hc : C.PosDef) (ht : 0 < τ)
variable (ha : MeasurableSet A) (hP : Envelope P) (hφ : Envelope φ)
variable (cover : (fun t:IV F (board F X) G=>twirl F (board F X) t U) ⁻¹' A ⊆ covered γ (orbitJ F X U))
include hγ hc ht ha hP hφ cover

theorem orbit_gaussian_mass :
    angleMass F (board F X) (fun V=>ink A P V * φ V) U =
    τ^Fintype.card (↥(board F X) × G.ColorIndex) * modeCost C * gaussianMass F X Y A γ m C τ P φ U := by
  let v := fun t:IV F (board F X) G=>twirl F (board F X) t U
  obtain ⟨_,h⟩ := exposed v (orbitJ F X U) γ hγ m C A φ P hc ha (mspec F X U) hP hφ cover ht
  have eq (j : IV F (board F X) G) : palette A v P φ j=ink A P (v j)*φ (v j) := by
    by_cases e:v j∈A <;> simp [palette,ink,spec,e]
  simp_rw [eq] at h
  exact h

/-- The identical Jacobian and Gaussian normalization occur downstairs even if
the cut has zero measure. -/
theorem orbit_gaussian_kernel :
    orbitKernel F (board F X) A P φ U=gaussianOrbit F X Y A γ m C τ P φ U := by
  let a := τ^Fintype.card (↥(board F X) × G.ColorIndex) * modeCost C
  have nz : a≠0 := (mul_pos (pow_pos ht _) (modeCost_pos hc)).ne'
  have num := orbit_gaussian_mass F X Y A γ m C τ P φ U hγ hc ht ha hP hφ cover
  have den := orbit_gaussian_mass F X Y A γ m C τ P 1 U hγ hc ht ha hP (Envelope.const 1) cover
  simp only [Pi.one_apply,mul_one] at den
  unfold orbitKernel orbitQuotient gaussianOrbit
  rw [den,num]
  by_cases hz: gaussianMass F X Y A γ m C τ P 1 U=0
  · simp [hz]
  rw [if_neg (mul_ne_zero nz hz),if_neg hz,mul_div_mul_left _ _ nz]
end YM.Integration.FVA1Physical.Wilson
