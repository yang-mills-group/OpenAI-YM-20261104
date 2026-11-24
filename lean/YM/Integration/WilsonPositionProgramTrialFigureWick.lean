import YM.Integration.WilsonPositionProgramTrialOrbitWick
import YM.Integration.WilsonPositionProgramCopyTop

/-! Every genuine finite planted coefficient, with its true incoming pole,
uses the same regulated Wilson/ghost Gaussian as the empty numerator. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace YM.Integration.WilsonPositionProgramTrialFigureWick
open FormalOPE.RG10 FormalOPE.RG10.BlockGauge RG Exterior Comparison.RG02
open Function MeasureTheory MeasureTheory.Measure Lattice Gauge Wilson PhysicalNext.Repeat.Legato
open PertExtension PertExtension.Series PertExtension.Orb PertExtension.Chart PertExtension.GaussianScore
open FVA2 FVA2.Trans FVA2.Wilson FVA2.Wilson.FP FVA2.GermLaplace Precision Inherit Push.Loops TreeBasis
open WilsonPositionProgramTrialOrbitAction (coordinates)
open WilsonPositionProgramTrialOrbitWick (auxiliary vacuum)
open WilsonPositionProgramCopyTop (planted normalized)
open scoped Classical BigOperators ContDiff Topology
variable {G : Gauge}

def fullDir (G : Gauge) (n : Side) : Cone G n →ₗ[ℝ] fieldDir G n 1 :=
  LinearMap.pi fun i=>(LinearMap.proj (R:=ℝ) (i.1,axisEquiv.symm i.2)).comp (coverL G n)

theorem linkField (n : Side) (A : Cone G n) :
    Precision.represent (fullDir G n A)=assemble G n A := by
  funext i
  rw [Work.F03.represent_link,assemble_exp]
  change G.lieExp (coverL G n A (i.1,axisEquiv.symm (coord i.2)))=G.lieExp (coverL G n A i)
  simp only [←coord_map,Equiv.symm_apply_apply]

theorem allowable (R : Run G) (p : XSpace.Period) {I : Type} [Fintype I] [LinearOrder I]
    (d : I→ℕ) (o : I → Cover) (b : ∀ i,(R.family.labels.level (d i)).Index) :
    Physical (planted R p d o b) ∧ Honest (planted R p d o b) := by
  let O:=planted R p d o b
  constructor
  · intro u _ v
    rw [descends]
    exact (WilsonPositionProgramCopyTop.allowed R p d o b).gauge _ (track_even u) _
  · let C:=((fullDir G p.side).comp (enter G (staple p.side))).toContinuousLinearMap
    let L := (0 : FVA2.Wilson.Field G p.side →L[ℝ] ℝ).prod C
    let word := Bulk.projected (fun (_:ℝ) U=>(O U:ℂ))
    have h : ContDiffAt ℝ ω word (L 0) := by
      rw [map_zero]
      exact ((YM.RegulatorIR.FVAAlt2.Sound.Figure.prop R (fun _:Unit=>o) d b ()).prepared p.side).smooth
    have eq : treed O=Complex.reCLM ∘ word ∘ L := by
      funext v
      change O (assemble G p.side (enter G (staple p.side) v))=(((O (Precision.represent (C v))):ℂ)).re
      rw [show Precision.represent (C v)=_ from linkField p.side (enter G (staple p.side) v)]
      rfl
    unfold Honest
    change ContDiffAt ℝ ω (treed O) 0
    rw [eq]
    exact Complex.reCLM.contDiff.contDiffAt.comp _ (h.comp 0 L.contDiff.contDiffAt)

theorem original (R : Run G) (D : ChartRatio G) (law : LocalRatio D)
    (p : XSpace.Period) (T : p.Tree) {I : Type} [Fintype I] [LinearOrder I] (d : I→ℕ)
    (o : I → Cover) (b : ∀ i,(R.family.labels.level (d i)).Index)
    (V : Measure (Cone G p.side)) [IsAddHaarMeasure V] (q : ℕ) :
    let even:=even_iff_two_dvd.mpr p.even
    let E:=WilsonPositionProgramTrialOrbitWick.gauge G p.side even
    let f:=finances E (auxiliary G p.side even)
    let W:=Invoice.power V (vacuum G p.side even) f
    let r:=q+YM.RegulatorIR.FVAAlt2.Kick.depthF Finset.univ d b
    PowerSeries.coeff r (normalized R p d o b T) =
      (PowerSeries.coeff r (W (volumeK E D (planted R p d o b)) * (W (volumeK E D 1))⁻¹) : ℝ) := by
  intro even E f W r
  rw [WilsonPositionProgramCopyTop.original R p d o b D law T q]
  have h:=allowable R p d o b
  have same:=WilsonPositionProgramTrialOrbitWick.original G p.side even D law h.1 h.2 V
  apply congrArg Complex.ofReal
  simpa only [YM.FVAAlt2.Fixed.treeMom,r,W,f,E,PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff r) same

end YM.Integration.WilsonPositionProgramTrialFigureWick
