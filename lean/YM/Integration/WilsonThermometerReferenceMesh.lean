import YM.Integration.WilsonThermometerMarchReference

/-! The physical inverse-radius clock lies inside the original cutoff clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerReferenceMesh
open Function Filter Set Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize
open MergeProof.East WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionCorrectedCap
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {H : (Bel C.book).Hierarchy}

theorem scale {d : ℕ} (V : Vane C d) (checked : V.checked f H d) :
    -Real.log V.wheel.r ≤ C.S.scale V.k := by
  let A := C.path.levels
  have one : 1 ≤ Next.Rank.Station.mag A V.b V.k :=
    Real.one_le_rpow (Real.one_le_exp (sq_nonneg _)) (by linarith [checked.high.1])
  have above : C.S.a V.k ≤ V.wheel.r := by
    change C.S.a V.k ≤ C.S.a V.k * Next.Rank.Station.mag A V.b V.k
    exact le_mul_of_one_le_right (C.S.a_pos V.k).le one
  exact (neg_le_neg (Real.log_le_log (C.S.a_pos V.k) above)).trans_eq (Real.log_inv _).symm

theorem cutoff {d : ℕ} (V : Vane C d) (checked : V.checked f H d) {N : ℕ} (later : V.k ≤ N) :
    -Real.log V.wheel.r ≤ C.S.scale N := by
  have grows : Monotone C.S.scale := monotone_nat_of_le_succ fun n=>by
    rw [C.S.scale_succ]
    apply le_add_of_nonneg_right
    exact Real.log_nonneg (by exact_mod_cast (C.S.block n).property)
  exact (scale V checked).trans (grows later)

end YM.Integration.WilsonThermometerReferenceMesh
