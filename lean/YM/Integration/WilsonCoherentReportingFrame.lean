import YM.Integration.WilsonCoherentTerminalFrame
import YM.Push.LOCAL_SPLITTING.Atoms

/-! The full registered source at a reporting date, including the unit
coordinate and every independently chosen engineering grade. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentReportingFrame
open Lattice Wilson RG Source Finset
open PhysicalNext.Repeat.Legato RGComparison.Core16 RGComparison.Core16.Spool
open WilsonCoherentTerminalFrame
open scoped Classical

variable {G : Gauge} (R : Run G) {n : Side}

theorem arm {d : ℕ} (θ : ℝ) (y : R.family.label d) (o : Site n) (U : Config G n) :
    Push.Local.presented (R.family.localSection d) o θ y U =
      ∑ a,(R.family.labels.level d).scaled θ⁻¹ y a * Light (lamp R d a) n o U := by
  classical
  let V := (R.family.labels.level d).scaled θ⁻¹ y
  let E : R.family.label d →ₗ[ℂ] ℂ :=
    (MvPolynomial.aeval (entry (expandAt o U))).toLinearMap.comp (R.family.localSection d).evalC
  have total : V = ∑ a,V a • Pi.single a (1:ℂ) := by
    ext i
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  change E V = ∑ a, V a * E (Pi.single a 1)
  conv_lhs => rw [total,map_sum]
  simp only [map_smul,smul_eq_mul]

variable {I : Type} [Fintype I] (d : I → ℕ)
abbrev Axis := (i : I) → (R.family.labels.level (d i)).Index
def charge (θ : ℝ) (y : ∀ i,R.family.label (d i)) (a : Axis R d) : ℂ :=
  ∏ i,(R.family.labels.level (d i)).scaled θ⁻¹ (y i) (a i)
def roster (a : Axis R d) (i : I) := lamp R (d i) (a i)

theorem original (θ : ℝ) (y : ∀ i,R.family.label (d i)) (o : I → Site n) (U : Config G n) :
    ∏ i,Push.Local.presented (R.family.localSection (d i)) (o i) θ (y i) U =
      ∑ a,charge R d θ y a * tally (roster R d a) o U := by
  simp_rw [arm R θ]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro a _
  rw [Finset.prod_mul_distrib]
  rfl

theorem physical (θ : ℝ) (y : ∀ i,R.family.label (d i)) (o : I → Site n) (U : Config G n)
    (healthy : ∀i,Healthy θ ((R.family.localSection (d i)).footprint (o i)) U) :
    ∏ i,Push.Local.primary (R.family.localSection (d i)) (o i) θ (y i) U =
      ∑ a,charge R d θ y a * tally (roster R d a) o U := by
  convert original R d θ y o U using 1
  exact prod_congr rfl fun i _ => Push.Local.presented_primary _ (Next.Foundations.sound G (d i)) _ _ (healthy i)

end YM.Integration.WilsonCoherentReportingFrame
