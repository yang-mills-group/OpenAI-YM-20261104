import YM.Integration.WilsonCoherentReportingFrame
import YM.Integration.WilsonCoherentPivotStencil

/-! The retained chart polynomial of the complete physically registered
product, with its actual threshold coefficients and common compact pivots. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentReportingPivot
open Function Lattice Wilson RG Source Finset
open PhysicalNext.Repeat.Legato RGComparison.Core16 RGComparison.Core16.Spool
open WilsonCoherentReportingFrame
open scoped Classical Matrix.Norms.Frobenius NNReal

variable {G : Gauge} (R : Run G) {I : Type} [Fintype I] (d : I → ℕ) {n : Side}

def mass (θ : ℝ) (y : ∀ i,R.family.label (d i)) : ℝ :=
  ∑ a,‖charge R d θ y a‖

theorem counted (θ : ℝ) (y : ∀ i,R.family.label (d i)) :
    mass R d θ y = ∏ i,∑ j, ‖(R.family.labels.level (d i)).scaled θ⁻¹ (y i) j‖ := by
  classical
  rw [Fintype.prod_sum]
  simp only [mass,charge,norm_prod]

def row (θ : ℝ) (y : ∀ i,R.family.label (d i)) (o : I → Site n)
    (b : Edge (Site n) → G.El) (z : Edge (Site n) → G.Color) (p : ℕ) (t : ℝ) : ℂ :=
  ∑ a, charge R d θ y a * WilsonCoherentPivotStencil.row (roster R d a)
    (b ∘ legs (roster R d a) o) (z ∘ legs (roster R d a) o) p t

theorem purchased (p : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ (n : Side) (θ : ℝ)
    (y : ∀ i,R.family.label (d i)) (o : I → Site n) (U : Config G n)
    (b : Edge (Site n) → G.El) (z : Edge (Site n) → G.Color)
    (t D : ℝ), 0<t → 0≤D → t*D<1 →
    (∀a : WilsonCoherentReportingFrame.Axis R d, ‖z ∘ legs (roster R d a) o‖≤D) →
    (∀ (a : WilsonCoherentReportingFrame.Axis R d) (j : Slice (roster R d a)),
      U (legs _ o j)=G.lieExp (t • z (legs _ o j))*b (legs _ o j)) →
    (∀i,Healthy θ ((R.family.localSection (d i)).footprint (o i)) U) →
    ‖(∏ i,Push.Local.primary (R.family.localSection (d i)) (o i) θ (y i) U) -
      row R d θ y o b z p t‖ ≤ mass R d θ y * (C*(t*D)^(p+1)) := by
  classical
  choose fee pos paid using fun a : WilsonCoherentReportingFrame.Axis R d => WilsonCoherentPivotStencil.purchased (roster R d a) p
  let costs : WilsonCoherentReportingFrame.Axis R d → ℝ≥0 := fun a => ⟨fee a,pos a⟩
  let C : ℝ := (univ.sup costs : ℝ≥0)
  refine ⟨C,(univ.sup costs).property,?_⟩
  intro n θ y o U b z t D ht hD hr size hit healthy
  let J := roster R d
  have each (a : WilsonCoherentReportingFrame.Axis R d) :
      ‖tally (J a) o U - WilsonCoherentPivotStencil.row (J a) (b∘legs (J a) o) (z∘legs (J a) o) p t‖
        ≤ C*(t*D)^(p+1) := by
    have cap : fee a≤C := le_sup (f:=costs) (mem_univ a)
    have q := mul_le_mul_of_nonneg_left (size a) ht.le
    exact (paid a n o U _ _ t ht (q.trans_lt hr) (hit a)).trans
      (mul_le_mul cap (pow_le_pow_left₀ (by positivity) q _) (by positivity) (univ.sup costs).property)
  rw [WilsonCoherentReportingFrame.physical R d θ y o U healthy,row,←sum_sub_distrib,mass,sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro a _
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (each a) (norm_nonneg _)

end YM.Integration.WilsonCoherentReportingPivot
