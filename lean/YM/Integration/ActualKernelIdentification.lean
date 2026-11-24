import YM.Integration.RunRG02Along
import YM.Comparison.RG02.Bulk.Sequence
import YM.Work.F05.Graphs

/-! The arbitrary formal Chain uses the original Run's stationary germ and
inverse Hessian. No equality of Horizon witnesses or additional price premise
is required. Quantitative covariance and coefficient bounds remain separate. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualKernelIdentification
open Function Filter Lattice Wilson RG Precision Exterior Tree
open Comparison.RG02 PhysicalNext.Repeat.Legato
open scoped Topology ContDiff Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}
    {p : Clip} {P : PathData G} {O O' : ChartRatio G}

private theorem critical_unique {F : Forest S.ratio}
    {u v : fieldDir G c 1 → AxisChart G F}
    (hu : Critical F p P u) (hv : Critical F p P v)
    {eta : ℝ} (heta : 0 < eta) (hgap : PriceGap F p P eta)
    (t : S.Choices) : u =ᶠ[𝓝 0] v := by
  have hnondeg (y : AxisChart G F) :
      Work.F05.bend (tested F t p P 0) 0 y y = 0 → y = 0 := by
    intro hzero
    by_contra hne
    exact (Work.F05.tested_diag heta hgap t y hne).ne' hzero
  have htu : Tendsto u (𝓝 0) (𝓝 0) := by
    have h := hu.2.1.continuousAt.tendsto
    rwa [hu.1] at h
  have htv : Tendsto v (𝓝 0) (𝓝 0) := by
    have h := hv.2.1.continuousAt.tendsto
    rwa [hv.1] at h
  exact Work.F05.station_unique (F := tested F t p P)
    (hv.2.2 t).1 hnondeg htu htv
    ((hu.2.2 t).2.mono fun _ h => h.fderiv)
    ((hv.2.2 t).2.mono fun _ h => h.fderiv)

theorem kernel_germ (K : Bulk.Kernel S p P O) (K' : Bulk.Kernel S p P O')
    (F : Forest S.ratio) (t : S.Choices) :
    K.b F =ᶠ[𝓝 0] K'.b F := by
  obtain ⟨eta, heta, hgap⟩ := K'.gap F
  exact critical_unique (K.critical F) (K'.critical F) heta hgap t

variable (R : Run G) (Y : Bulk.Chain R.family.path)
    (N period m : ℕ) (hm : m < N)
    (F : Forest (R.family.path.levels.clock.op m period).ratio)
    (t : (R.family.path.levels.clock.op m period).Choices)

include t in
theorem stationary_germ :
    (Y.step N m period hm).b F =ᶠ[𝓝 0]
      (CommonConstruction.runAlong R).V.stationary N m period F := by
  have hcrit := (CommonConstruction.runAlong R).chooses F hm
  have hgap := (CommonConstruction.runAlong R).pricing F hm
  unfold RG02.Along.clip at hcrit hgap
  rw [← Y.clips N period (m + 1) hm] at hcrit hgap
  exact critical_unique ((Y.step N m period hm).critical F) hcrit
    ((CommonConstruction.runAlong R).toll m) hgap t

include t in
theorem stationary_fderiv :
    fderiv ℝ ((Y.step N m period hm).b F) 0 =
      fderiv ℝ ((CommonConstruction.runAlong R).V.stationary N m period F) 0 :=
  (stationary_germ R Y N period m hm F t).fderiv_eq

theorem covariance_path :
    (Y.step N m period hm).covariance F t =
      (hessian F t (R.family.path.levels.params (m + 1)).clip
        (R.alloy.B.kin.path N (m + 1)) 0 0)⁻¹ := by
  unfold Bulk.Kernel.covariance
  rw [Y.clips N period (m + 1) hm,
    CommonConstruction.runAlong_actual_path R N (m + 1) period hm]

end YM.Integration.ActualKernelIdentification
end
