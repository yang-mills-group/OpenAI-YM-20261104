import YM.Integration.WilsonPositionProgramTrialPublicJointPivotRose
import YM.Integration.WilsonPhysicalNormalizedWholeTable

/-! Both signed arrays are tested on the same inherited column at each slot of the finite position stock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotWeights
open Filter Function Finset Set MeasureTheory Lattice RG PhysicalNext.Repeat.Legato
open RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress FVA2 FVA2.Register Trace.Target
open Spec Table Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize PhysMS
open WilsonPhysicalNormalizedSignedMenu (Row)
open WilsonPhysicalPositionTargetRows (rows)
open WilsonPhysicalNormalizedWholeTable (cost)
open scoped Classical Topology BigOperators
variable {G : Gauge} {d n : ℕ}

def salary (v : Sec G d) : ℝ := ∑ j : Pin G d, ‖tableD G d v j‖

theorem receipt (v : Fin n → Sec G d) : cost v = ∏ i, salary (v i) := by
  unfold cost salary
  rw [Fintype.prod_sum]
  simp only [norm_prod]

theorem paid (M W : Row G d n) (v : Fin n → Sec G d) {e : ℝ} (ep : 0 ≤ e)
    (registered : ∀ b, ‖rows M b - rows W b‖ ≤ e) :
    ‖M v - W v‖ ≤ (∏ i, salary (v i)) * e := by
  have restored := WilsonPhysicalNormalizedWholeTable.tested M W v
  rw [receipt] at restored
  apply restored.trans
  apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _)
  exact (pi_norm_le_iff_of_nonneg ep).mpr registered

theorem determining {A : Screen G d} (D : Fray A) (T : Change G d) (P Q : Prediction G d)
    {e : ℝ} (ep : 0 ≤ e)
    (registered : ∀ i b, ‖D.purse P i b - D.purse Q i b‖ ≤ e) (i) (b) :
    ‖D.purse (recruit (stand T) P) i b - D.purse (recruit (stand T) Q) i b‖ ≤
      (∏ j, salary (stand T (Module.finBasis ℝ (Sec G d) (b j)))) * e :=
  paid (P (D.scope i).n (D.scope i).t) (Q (D.scope i).n (D.scope i).t)
    (fun j => stand T (Module.finBasis ℝ (Sec G d) (b j))) ep (registered i)

theorem diagnostic (φ : Test 3) (M W : Points 3 → Row G d 3)
    (hm : WilsonPositionProgramTrialPublicJointPivotRose.Live φ M)
    (hw : WilsonPositionProgramTrialPublicJointPivotRose.Live φ W)
    (v : Fin 3 → Sec G d) {e : ℝ} (ep : 0 ≤ e)
    (registered : ∀ b : Fin 3 → Pin G d,
      ‖(φ.applyTo fun x => WilsonPositionThermometerConnected.value (fun s => M x
        (Rose.missing (fun j => Module.finBasis ℝ (Sec G d) (b j)) s))) -
       (φ.applyTo fun x => WilsonPositionThermometerConnected.value (fun s => W x
        (Rose.missing (fun j => Module.finBasis ℝ (Sec G d) (b j)) s)))‖ ≤ e) :
    ‖(φ.applyTo fun x => WilsonPositionThermometerConnected.value (fun s => M x (Rose.missing v s))) -
      (φ.applyTo fun x => WilsonPositionThermometerConnected.value (fun s => W x (Rose.missing v s)))‖ ≤
      (∏ j, salary (v j)) * e :=
  paid (WilsonPositionProgramTrialPublicJointPivotRose.tested φ M hm)
    (WilsonPositionProgramTrialPublicJointPivotRose.tested φ W hw) v ep registered

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotWeights
