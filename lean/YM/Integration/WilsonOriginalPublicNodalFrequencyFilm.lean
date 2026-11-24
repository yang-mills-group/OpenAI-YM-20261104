import YM.Integration.WilsonOriginalPublicNodalFrequencyProbe
import YM.Integration.WilsonOriginalPublicNodalBufferedCellFilm

/-! Every Fourier frequency uses the same finite set of sites for the authentic measured torus film. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalFrequencyFilm
open Function Finset PowerSeries Lattice RG Wilson Tree Source Labels XSpace XSpace.Cirrus MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open PhysicalNext.Repeat.Legato RegulatorIR.Profiles
open WilsonOriginalPublicNodalBufferedCellRow (Source Stamps Frames gain bank profile)
open WilsonOriginalPublicNodalBufferedCellFilm (Sites Disp full paper entry)
open WilsonPositionProgramTrialPublicCellHull (hull)
open WilsonPositionProgramTrialPublicJointRoom (normalized)
open WilsonIndependentPublicReportComplex (apply)
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge}{n:ℕ}(R:Run G)(W:Initialize G)(kind:Fin (n+1)→Bool)(d D:Fin (n+1)→ℕ)
  (cut:∀i,d i<D i)(Y:Sample 2)(T:(i:Fin (n+1))→Rarity (D i))(real:∀i,ContDiff ℝ ∞ (T i).ψ.val)
  (c:Fin (n+1)→Bool)(x:Fin (n+1)→ℝ)(y σ:ℝ)(sp:0<σ)(o:Fin (n+1)→ CellR)(b:Source R d)

include real in
theorem ledger (H:Sites (n:=n))(q:ℕ):
    Continuous fun w:Points (n+1) × Disp n=>coeff q
      (full R W kind d D cut Y (normalized T w.1 c) x y σ sp o H b w.2):=by
  simp only [full,map_sum]
  apply continuous_finsetSum
  intro u _
  simp only [WilsonOriginalPublicNodalBufferedCellFilm.entry,coeff_C_mul]
  have income:Continuous fun w:Points (n+1) × Disp n=>gain R d D cut (normalized T w.1 c) x y σ sp o w.2
      (fun i=>(u i).1.val) (fun i=>(u i).2):=by
    unfold gain
    apply continuous_finsetProd
    intro i _
    have arg:Continuous fun w:Points (n+1) × Disp n=>(w.1,w.2 i):=
      continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)
    have single:=WilsonOriginalPublicNodalFrequencyProbe.jewel (F:=Frames R d i) T real c i (cut i)
      (x i) y σ sp (o i) (u i).1.val (u i).2
    let source:=fun w:Points (n+1) × Point4=>jewelBloom (cut i) (u i).2
      (wheelC (x i) y (u i).1.val (WilsonPositionProgramTrialPublicCellPulse.placed
        (normalized T w.1 c i) (x i) y σ sp (o i) w.2).ψ (o i))
    have single':Continuous source:=single
    have landed:Continuous (fun w:Points (n+1) × Disp n=>source (w.1,w.2 i)):=single'.comp arg
    change Continuous (fun w:Points (n+1) × Disp n=>drumB (d i) (x i)*source (w.1,w.2 i))
    exact (show Continuous (fun _:Points (n+1) × Disp n=>drumB (d i) (x i)) from continuous_const).mul landed
  exact (Complex.continuous_ofReal.comp income).mul continuous_const

include real in
theorem measured (E:Set (Disp n))(xp:∀i,0<x i)(inside:∀ξ∈E,∀i,‖ξ i‖ ≤ 1)(clock:Feeds)(pole q:ℕ):
    ContinuousOn (fun w:Points (n+1) × Disp n=>coeff q (apply clock pole
      (paper R W kind d D cut Y (normalized T w.1 c) x y σ sp o b w.2))) (Set.univ ×ˢ E):=by
  let H:=fun i=>hull (T i) (x i) y σ (o i)
  have smooth:Continuous fun w:Points (n+1) × Disp n=>coeff q (apply clock pole
      (full R W kind d D cut Y (normalized T w.1 c) x y σ sp o H b w.2)):=by
    simp only [WilsonIndependentPublicReportComplex.coefficients]
    apply continuous_finsetSum
    intro i _
    exact (ledger R W kind d D cut Y T real c x y σ sp o b H i).mul continuous_const
  apply smooth.continuousOn.congr
  rintro ⟨ν,ξ⟩ ⟨_,fit⟩
  exact congrArg (fun f:PowerSeries ℂ=>coeff q (apply clock pole f))
    (WilsonOriginalPublicNodalBufferedCellFilm.original R W kind d D cut Y (normalized T ν c) x y σ sp o b xp ξ (inside ξ fit))

end YM.Integration.WilsonOriginalPublicNodalFrequencyFilm
end
