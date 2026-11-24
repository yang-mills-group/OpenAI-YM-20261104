import YM.Integration.WilsonThermometerRegisteredTrace

/-! Smoothness of each held cartesian field direction on the registered finite polynomial. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredAngularJet
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Comparison.RG02.Cumulants Cumulants.Cloud
open Extra.Trajectories Primitives.GCC.Anchor QuadraticLocal Earn
open scoped Topology BigOperators Classical ContDiff

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V} {G : Gauge} {n : Side}

omit [Fintype V] in
theorem coefficient (k:ℕ∞) (M : Bulk.Colors R G n) (d : ℕ) (s : R.Mode) :
    ContDiff ℝ k (fun x : fieldDir G n 1 => (Air.discharge M d x).part s) := by
  by_cases hs:s=R.quiet
  · subst s
    simp only [Air.discharge, Multi.part_lit_quiet]
    exact contDiff_const
  · let u:Multi.Hot R:=⟨s,Finset.nonempty_iff_ne_empty.mpr (fun eq=>hs (Subtype.ext eq))⟩
    change ContDiff ℝ k (fun x : fieldDir G n 1 => (Air.discharge M d x).part u.val)
    simp only [Air.discharge, Multi.part_lit, Assembly.jet]
    let E:=iteratedFDeriv ℝ (M.power u+d) (Bulk.projected (M.mark u)) 0
    have smooth:ContDiff ℝ k (fun x:fieldDir G n 1=>E (fun _=>(1,x))):=
      E.contDiff.comp (contDiff_pi.mpr (fun _=>contDiff_const.prodMk contDiff_id))
    exact smooth.const_smul _

omit [Fintype V] in
theorem panel (k:ℕ∞) (M : Bulk.Colors R G n) (ord : ℕ) (g : ℂ) (s : R.Mode) :
    ContDiff ℝ k (fun x : fieldDir G n 1 =>
      (WilsonCoherentMayerWindingGrades.panel ord g (fun d=>Air.discharge M d x)).part s) := by
  simp only [WilsonCoherentMayerWindingGrades.panel,Poly.part_sum,Poly.part_smul]
  exact ContDiff.sum (fun d _ => contDiff_const.mul (coefficient k M d s))

end YM.Integration.WilsonThermometerRegisteredAngularJet
