import YM.Integration.WilsonPhysicalRosePositionFace

/-! The connected three-field assay as one multilinear tested row on the original position stock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotRose
open Filter Function Finset Set MeasureTheory Lattice RG PhysicalNext.Repeat.Legato
open RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress FVA2 FVA2.Register Trace.Target
open Spec Table Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize PhysMS
open WilsonPhysicalNormalizedSignedMenu (Row offered)
open WilsonPositionThermometerConnected (value)
open scoped Classical Topology BigOperators
variable {G : Gauge} {d : ℕ}
abbrev Fields (G : Gauge) (d : ℕ) := Fin 3 → Sec G d
abbrev Face := Finset (Fin 3)

def faces (M : Row G d 3) (p : Fields G d) (s : Face) : ℂ := M (Rose.missing p s)

private theorem placed (p : Fields G d) (i : Fin 3) (v : Sec G d) (s : Face) :
    Rose.missing (update p i v) s =
      if i ∈ s then update (Rose.missing p s) i v else Rose.missing p s := by
  funext j
  by_cases e : j = i
  · subst j
    by_cases mem : i ∈ s <;> simp [Rose.missing,mem]
  · by_cases mem : i ∈ s <;> simp [Rose.missing,mem,update_of_ne e]

private theorem add (M : Row G d 3) (p : Fields G d) (i : Fin 3) (a b : Sec G d) :
    value (faces M (update p i (a+b))) =
      value (faces M (update p i a)) + value (faces M (update p i b)) := by
  fin_cases i <;> simp [WilsonPositionThermometerConnected.value,faces,placed,MultilinearMap.map_update_add] <;> ring

private theorem smul (M : Row G d 3) (p : Fields G d) (i : Fin 3) (z : ℂ) (a : Sec G d) :
    value (faces M (update p i (z • a))) = z • value (faces M (update p i a)) := by
  fin_cases i <;> simp [WilsonPositionThermometerConnected.value,faces,placed,MultilinearMap.map_update_smul] <;> ring

def connected (M : Row G d 3) : Row G d 3 :=
  MultilinearMap.mk' (fun p => value (faces M p)) (add M) (smul M)

def Live (φ : Test 3) (M : Points 3 → Row G d 3) : Prop :=
  ∀ p : Fields G d, Integrable (fun x => φ x * connected (M x) p)

def tested (φ : Test 3) (M : Points 3 → Row G d 3) (h : Live φ M) : Row G d 3 :=
  MultilinearMap.mk' (fun p => φ.applyTo fun x => connected (M x) p)
    (fun p i a b => by
      simp_rw [Test.applyTo,MultilinearMap.map_update_add,mul_add]
      exact integral_add (h _) (h _))
    (fun p i z a => by
      unfold Test.applyTo
      simp_rw [MultilinearMap.map_update_smul,smul_eq_mul,mul_left_comm (φ _) z]
      exact integral_const_mul z _)

theorem original (φ : Test 3) (M : Points 3 → Row G d 3) (h : Live φ M) (p : Fields G d) :
    tested φ M h p = φ.applyTo (fun x => value (fun s => M x (Rose.missing p s))) := rfl

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotRose
