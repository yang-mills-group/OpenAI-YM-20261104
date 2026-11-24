import YM.Integration.WilsonOriginalCoveredHearing
import YM.Integration.WilsonThermometerRegisteredCompact
import YM.Integration.WilsonJointAxialOrdinary

/-! The registered finite angular polynomial is continuous in its physical angle, after each
ordinary face has been evaluated. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredTrace
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Comparison.RG02.Cumulants Cumulants.Cloud
open Extra.Trajectories Primitives.GCC.Anchor QuadraticLocal Earn
open scoped Topology BigOperators Classical ContDiff

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V} {G : Gauge} {n : Side}

omit [Fintype V] in
theorem coefficient (M : Bulk.Colors R G n) (d : ℕ) (s : R.Mode) :
    Continuous (fun x : fieldDir G n 1 => (Air.discharge M d x).part s) := by
  by_cases hs:s=R.quiet
  · subst s
    simp only [Air.discharge, Multi.part_lit_quiet]
    exact continuous_const
  · let u:Multi.Hot R:=⟨s,Finset.nonempty_iff_ne_empty.mpr (fun eq=>hs (Subtype.ext eq))⟩
    change Continuous (fun x : fieldDir G n 1 => (Air.discharge M d x).part u.val)
    simp only [Air.discharge, Multi.part_lit, Assembly.jet]
    fun_prop

omit [Fintype V] in
theorem panel (M : Bulk.Colors R G n) (ord : ℕ) (g : ℂ) (s : R.Mode) :
    Continuous (fun x : fieldDir G n 1 =>
      (WilsonCoherentMayerWindingGrades.panel ord g (fun d=>Air.discharge M d x)).part s) := by
  simp only [WilsonCoherentMayerWindingGrades.panel,Poly.part_sum,Poly.part_smul]
  exact continuous_finsetSum _ (fun d _ => continuous_const.mul (coefficient M d s))

end YM.Integration.WilsonThermometerRegisteredTrace
