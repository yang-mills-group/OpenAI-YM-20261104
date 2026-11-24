import YM.Integration.WilsonPositionProgramTrialPublicJointPivotFitted

/-! Uniform bounds for each finite response on the two actual position sections. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotNorm
open Filter Function Finset Set MeasureTheory Lattice RG PhysicalNext.Repeat.Legato
open RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress FVA2 FVA2.Register Trace.Target
open Spec Table Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize PhysMS
open WilsonPhysicalNormalizedSignedMenu (Row offered docket retag)
open WilsonPhysicalPositionTargetRows (rows)
open WilsonPositionPrescribedScreen (hierarchy)
open WilsonPhysicalRosePositionFace (located predicted)
open WilsonPositionProgramTrialPublicJointPivotRose (Live tested)
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
open WilsonPhysicalPositionTargetRows (meter counted zero smooth)
open WilsonPositionProgramTrialPublicJointPivotFitted (undress named)
variable {d n : ℕ}
abbrev moved (T : Change G d) (W : Row G d n) : Row G d n :=
  offered (fun _: Fin n => ()) (fun _: Unit => T) W

theorem drift {ι : Type*} (l : Filter ι) (T : ι → Change G d)
    (near : Tendsto (fun i => guide G d (T i)) l (𝓝 0)) :
    ∀ᶠ i in l, ∀ W : Row G d n, ‖rows (moved (T i) W) - rows W‖ ≤ (1/2:ℝ)*‖rows W‖ := by
  let field (r : Fin n → Pin G d) (j : Fin n) := Module.finBasis ℝ (Sec G d) (r j)
  let home : Fin n → Unit := fun _ => ()
  let atDate (i : ι) : Unit → MoveSpace G d := fun _ => guide G d (T i)
  have here : Tendsto atDate l (𝓝 0) := tendsto_pi_nhds.mpr fun _ => near
  have cap (r : Fin n → Pin G d) : ∀ᶠ i in l,
      ‖meter home (field r) (atDate i) - meter home (field r) 0‖ ≤ (1/2:ℝ) := by
    have p := ((smooth home (field r)).continuous.tendsto 0).comp here
    have s : Tendsto (fun i => ‖meter home (field r) (atDate i) - meter home (field r) 0‖) l (𝓝 0) := by
      simpa only [Function.comp_apply,sub_self,norm_zero] using (p.sub_const (meter home (field r) 0)).norm
    exact ((tendsto_order.mp s).2 _ (by norm_num : (0:ℝ)<1/2)).mono fun _ h => h.le
  filter_upwards [Filter.eventually_all.mpr cap] with i close W
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro r
  calc
    ‖(rows (moved (T i) W) - rows W) r‖ =
        ‖(meter home (field r) (atDate i) - meter home (field r) 0) (rows W)‖ := by
      rw [_root_.sub_apply,zero]
      change ‖(moved (T i) W) (field r) - W (field r)‖ = _
      rw [show atDate i = (fun h : Unit => guide G d ((fun _ : Unit => T i) h)) from rfl,counted]
      rfl
    _ ≤ ‖meter home (field r) (atDate i) - meter home (field r) 0‖ * ‖rows W‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (close r) (norm_nonneg _)

theorem original {ι : Type*} (l : Filter ι) (V : Store G) (Q : ι → Prediction G d)
    (T : ι → Change G d) (ready : (V.survey d).Via Q (u:=l))
    (near : Tendsto (fun i => guide G d (T i)) l (𝓝 0)) :
    ∀ᶠ i in l, ∀ (A : Row G d n) (hq : Bijective (stand ((V.survey d).firstPass (V.prepared d) (Q i)))),
      ‖rows (moved (T i) (undress ((V.survey d).firstPass (V.prepared d) (Q i)) hq A))‖ ≤ 3 * ‖rows A‖ := by
  let pass (i : ι) := (V.survey d).firstPass (V.prepared d) (Q i)
  have prep := drift (n:=n) l pass ((V.survey d).turns_approach (V.prepared d) ready)
  filter_upwards [prep,drift (n:=n) l T near] with i fitted put A hq
  let W := undress (pass i) hq A
  have equal : moved (pass i) W = A := by
    ext p
    exact named (pass i) hq A p
  have one := fitted W
  rw [equal,norm_sub_rev] at one
  have two := put W
  have left := norm_le_norm_sub_add (rows W) (rows A)
  have right := norm_le_norm_sub_add (rows (moved (T i) W)) (rows W)
  change ‖rows (moved (T i) W)‖ ≤ _
  linarith
end YM.Integration.WilsonPositionProgramTrialPublicJointPivotNorm
