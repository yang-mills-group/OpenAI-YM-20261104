import YM.Integration.WilsonThermometerUnitFilingCompactMaterial

/-! The genuine enrolled unnormalised pupil at its own stop has one scalar reading on the original quiet density. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFlatRead
open Finset RG Lattice Wilson Labels Source Extra.Histories Extra.Histories.Relay Extra.Trajectories Extra.Multi
open MergeProof MergeProof.Accent PhysicalNext PhysicalNext.Repeat Legato
open WilsonThermometerUnitFilingCoarse
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G)

theorem original {N per v:ℕ} (live:v≤N) (Ψ:Rep G (R.family.side v per))
    (quiet:Ψ.eval=(R.family.path.rep N per v).eval) (row:Config G (R.family.side v per)→ℂ):
    reading R (N:=N) (fun U=>(Ψ.eval U:ℂ)*row U) v le_rfl=row 1:=by
  have nz:((R.family.path.rep N per v).eval (1:Config G (R.family.side v per)):ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson live _).ne'
  unfold reading
  rw [gust_base,quiet,←mul_assoc,inv_mul_cancel₀ nz,one_mul]

theorem compact {N per v:ℕ} (live:v≤N) (Ψ:Rep G (R.family.side v per))
    (quiet:Ψ.eval=(R.family.path.rep N per v).eval) {ι:Type} [Fintype ι] (w:ι→ℂ)
    (row:ι → Config G (R.family.side v per)→ℂ):
    (∑c:ι,w c*reading R (N:=N) (fun U=>(Ψ.eval U:ℂ)*row c U) v le_rfl)=
      ∑c:ι,w c*row c 1:=by simp only [original R live Ψ quiet]

end YM.Integration.WilsonThermometerUnitFilingFlatRead
