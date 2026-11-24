import YM.Integration.WilsonPositionProgramTrialPublicJointPivotRose

/-! The finite thermal polynomial of a signed three-field diagnostic, with every proper face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotSeries
open Filter Function Finset Set MeasureTheory Lattice RG PhysicalNext.Repeat.Legato
open RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress FVA2 FVA2.Register Trace.Target
open Spec Table Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize PhysMS PowerSeries
open WilsonPhysicalNormalizedSignedMenu (Row)
open WilsonPositionProgramTrialPublicJointPivotRose (Fields Face)
open private placed from YM.Integration.WilsonPositionProgramTrialPublicJointPivotRose
open scoped Classical Topology BigOperators Polynomial
variable {G : Gauge} {d : ℕ}

def whole (A : ℕ → Row G d 3) (p : Fields G d) : PowerSeries ℂ :=
  PowerSeries.mk fun k => A k p

private theorem plus (A : ℕ → Row G d 3) (p : Fields G d) (i : Fin 3) (a b : Sec G d) :
    whole A (update p i (a+b)) = whole A (update p i a) + whole A (update p i b) := by
  ext k
  simp [whole,MultilinearMap.map_update_add]

private theorem times (A : ℕ → Row G d 3) (p : Fields G d) (i : Fin 3) (z : ℂ) (a : Sec G d) :
    whole A (update p i (z • a)) = z • whole A (update p i a) := by
  ext k
  simp [whole,MultilinearMap.map_update_smul]

def signed (A : ℕ → Row G d 3) (p : Fields G d) : PowerSeries ℂ :=
  Rose.b3 (fun s => whole A (Rose.missing p s))

set_option linter.unusedSimpArgs false in
private theorem add (A : ℕ → Row G d 3) (p : Fields G d) (i : Fin 3) (a b : Sec G d) :
    signed A (update p i (a+b)) = signed A (update p i a) + signed A (update p i b) := by
  fin_cases i <;> simp [signed,Rose.b3,placed,plus,Algebra.smul_def] <;> ring

set_option linter.unusedSimpArgs false in
private theorem smul (A : ℕ → Row G d 3) (p : Fields G d) (i : Fin 3) (z : ℂ) (a : Sec G d) :
    signed A (update p i (z • a)) = z • signed A (update p i a) := by
  fin_cases i <;> simp [signed,Rose.b3,placed,times,Algebra.smul_def] <;> ring

def cash (q : ℕ) (g : ℂ) : PowerSeries ℂ →ₗ[ℂ] ℂ :=
  ∑ k ∈ range (q+1), g^k • coeff k

theorem printed (q : ℕ) (g : ℂ) (p : PowerSeries ℂ) :
    cash q g p = (trunc (q+1) p).eval g := by
  have paper : (trunc (q+1) p).eval g = ∑ k ∈ range (q+1), coeff k p * g^k :=
    eval₂_trunc_eq_sum_range g (RingHom.id ℂ) (q+1) p
  rw [paper]
  simp [cash,mul_comm]

def cooked (A : ℕ → Row G d 3) (q : ℕ) (g : ℂ) : Row G d 3 :=
  MultilinearMap.mk' (fun p => cash q g (signed A p))
    (fun p i a b => by rw [add,map_add])
    (fun p i z a => by rw [smul,map_smul])

theorem original (A : ℕ → Row G 6 3) (q : ℕ) (g : ℂ) :
    cooked A q g (Rose.tag G) = (trunc (q+1) (Rose.b3 (Rose.batchT A))).eval g :=
  printed q g (signed A (Rose.tag G))

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotSeries
