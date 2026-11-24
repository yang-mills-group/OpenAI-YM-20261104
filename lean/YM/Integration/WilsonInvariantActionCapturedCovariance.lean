import YM.Integration.WilsonInvariantActionIntegratedPair
import YM.Integration.WilsonReportMomentDifference
import YM.Comparison.RG02.Cumulants.Parents

/-! Identify the connected marked receiver with the actual measured covariance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionCapturedCovariance
open Function Finset MeasureTheory Lattice Wilson RG Source Marker Multi Primitives.GCC.Anchor
open RGComparison.Core16 FullVolume Spec PhysicalNext.Repeat.Legato Next.Rank
open Comparison.RG02.Cumulants Extra.Trajectories OPE.Therm
open WilsonReportMomentDifference WilsonInvariantActionIntegratedPair WilsonInvariantActionPairMarginals
open private tags from YM.Integration.WilsonInvariantActionIntegratedPair
open scoped BigOperators Classical

def census:Census (Fin 2):=⟨univ,mem_univ _,fun _=>mem_univ _,fun _ _ _=>mem_univ _⟩

def both:census.Mode:=⟨{0,1},mem_univ _⟩

variable {G:Gauge} (C:Family G) {N per k:ℕ}

private theorem upper (F:Fin 2 → Config G (C.side N per)→ℂ):
    (connected (microscopic census C F)).part both=
      moment (C.beta N per) (fun U=>F 0 U*F 1 U)-
        moment (C.beta N per) (F 0)*moment (C.beta N per) (F 1):=by
  let P:=microscopic census C F
  have root:P.part census.quiet=1:=by
    change moment _ (fun U=>∏j∈(∅:Finset (Fin 2)),F j U)=1
    simp [moment]
  rw [twins (0:Fin 2) (1:Fin 2) both P root (by decide) rfl]
  change moment _ (fun U=>∏j∈({0,1}:Finset (Fin 2)),F j U)-
    moment _ (fun U=>∏j∈({0}:Finset (Fin 2)),F j U)*moment _ (fun U=>∏j∈({1}:Finset (Fin 2)),F j U)=_
  simp

theorem lower (makes:C.Makes)(hk:k≤N) (F:Fin 2 → Config G (C.side k per)→ℂ):
    let μ:=scene C.path N per k
    (connected (reported census C (N:=N) F)).part both=
      (∫U,F 0 U*F 1 U ∂μ) - (∫U,F 0 U ∂μ)*(∫U,F 1 U ∂μ):=by
  let μ:=scene C.path N per k
  letI:IsProbabilityMeasure μ:=probability makes.wilson hk
  let P:=reported census C (N:=N) F
  have root:P.part census.quiet=1:=by
    change (∫U,∏j∈(∅:Finset (Fin 2)),F j U ∂μ)=1
    simp
  dsimp only
  rw [twins (0:Fin 2) (1:Fin 2) both P root (by decide) rfl]
  change (∫U,∏j∈({0,1}:Finset (Fin 2)),F j U ∂μ)-
    (∫U,∏j∈({0}:Finset (Fin 2)),F j U ∂μ)*(∫U,∏j∈({1}:Finset (Fin 2)),F j U ∂μ)=_
  simp [μ]

/-- The same original upper Wilson pair as the exact conditional-covariance
decomposition, with arbitrary actual marks, sites and retained date. -/
theorem original (R:Run G) (T:Slices R.family.path.levels per) (hk:k≤N)
    (w:Fin 2→R.family.label 4) (x:Fin 2→Site (R.family.side N per)):
    (connected (microscopic census R.family (fun j=>R.family.O N per (w j) (x j)))).part both=
      posterior R T hk (w 0) (w 1) x:=by
  rw [upper,finite]
  simp [moment,Family.num,Family.seen,tags,single,Fin.prod_univ_two]

end YM.Integration.WilsonInvariantActionCapturedCovariance
