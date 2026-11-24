import YM.Integration.WilsonCoherentInheritedReturn
import YM.Next.FOUNDATIONS.Primary

/-! Exact enrollment of arbitrary, independently chosen terminal Wilson
coefficients on one finite regulator. Both physical scale factors are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentTerminalFrame
open Function Lattice Wilson RG Tree Precision Source
open PhysicalNext.Repeat.Legato RGComparison.Core16 RGComparison.Core16.Spool
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (N per : ℕ)

def coordinates {d : ℕ} (v : R.family.label d) : R.family.label d :=
  (R.family.labels.level d).scaled (R.family.path.levels.clock.threshold N)⁻¹
    ((((R.family.S.a N : ℂ)^d)⁻¹) • (R.family.factory d N per).terminal.symm v)

theorem named {d : ℕ} (v : R.family.label d) :
    Descent.fieldLabel R.family N per (coordinates R N per v)=v := by
  have pos : 0 < R.family.path.levels.clock.threshold N := (R.family.path.levels.budget N).threshold_pos
  unfold Descent.fieldLabel coordinates
  rw [(R.family.labels.level d).scaled_inv pos.ne',
    smul_smul, mul_inv_cancel₀,one_smul,LinearEquiv.apply_symm_apply]
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos _).ne')

def lamp (d : ℕ) (a : (R.family.labels.level d).Index) : Lamp G :=
  investment (Next.Foundations.sound G d) (Next.Foundations.valuation G d) a

theorem basis (d : ℕ) (a : (R.family.labels.level d).Index) (o : Site (R.family.side N per)) :
    R.family.O N per (Descent.fieldLabel R.family N per (Pi.single a 1)) o =
      Light (lamp R d a) (R.family.side N per) o := by
  rw [Descent.field_label_correct]
  rfl

theorem row {d : ℕ} (v : R.family.label d) (o : Site (R.family.side N per)) (U : Config G (R.family.side N per)) :
    R.family.O N per v o U =
      ∑ a,coordinates R N per v a * Light (lamp R d a) (R.family.side N per) o U := by
  classical
  let V := coordinates R N per v
  let E : R.family.label d →ₗ[ℂ] ℂ :=
    (MvPolynomial.aeval (entry (expandAt o U))).toLinearMap.comp (R.family.localSection d).evalC
  have total : V = ∑ a,V a • Pi.single a (1:ℂ) := by
    ext i
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  have phys : R.family.O N per v o U=E V := by
    calc
      _ = R.family.O N per (Descent.fieldLabel R.family N per V) o U := by rw [named]
      _ = E V := by rw [Descent.field_label_correct]; rfl
  rw [phys,total,map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul]
  rfl

variable {I : Type} [Fintype I] (d : I → ℕ)
def weight (v : ∀ i,R.family.label (d i)) (a : ∀ i,(R.family.labels.level (d i)).Index) : ℂ :=
  ∏ i,coordinates R N per (v i) (a i)

theorem joint (v : ∀ i,R.family.label (d i)) (o : I → Site (R.family.side N per)) (U : Config G (R.family.side N per)) :
    ∏ i,R.family.O N per (v i) (o i) U =
      ∑ a,weight R N per d v a * tally (fun i=>lamp R (d i) (a i)) o U := by
  classical
  simp_rw [row R N per]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.prod_mul_distrib

end YM.Integration.WilsonCoherentTerminalFrame
end
