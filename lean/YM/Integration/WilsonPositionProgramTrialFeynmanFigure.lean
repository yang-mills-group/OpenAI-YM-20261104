import YM.Integration.WilsonPositionProgramTrialWeightedWick
import YM.FVAAlt2.Fixed

/-! The same originally fitted finite Wilson source in the conventional
Feynman Gaussian. The planted cone and the independent period are unchanged. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
namespace YM.Integration.WilsonPositionProgramTrialFeynmanFigure
open FormalOPE.RG10 FormalOPE.RG10.BlockGauge RG Exterior Comparison.RG02
open Function Finset Lattice Gauge Wilson PhysicalNext.Repeat.Legato
open PertExtension PertExtension.Series PertExtension.Orb PertExtension.Chart PertExtension.GaussianScore
open FVA2 FVA2.Trans FVA2.Wilson FVA2.Wilson.FP FVA2.GermLaplace Precision Inherit Push.Loops TreeBasis
open SchemeRG11.Sway SchemeRG11.Sway.Lam Pert.Orb
open WilsonPositionProgramTrialFigureWick (fullDir linkField)
open WilsonPositionProgramTrialOrbitAction (coordinates)
open WilsonPositionProgramCopyTop (planted normalized)
open scoped Classical BigOperators ContDiff Topology
variable {G : Gauge} (R : Run G) (p : XSpace.Period)
    {I : Type} [Fintype I] [LinearOrder I] (d : I→ℕ) (o : I → Cover)
    (b : ∀i,(R.family.labels.level (d i)).Index)
local notation "O" => planted R p d o b
local notation "deg" => YM.RegulatorIR.FVAAlt2.Kick.depthF univ d b

def lift (G : Gauge) (p : XSpace.Period) : Potential G p.side →L[ℝ] fieldDir G p.side 1 :=
  (fullDir G p.side).toContinuousLinearMap.comp
    (coordinates G p.side (even_iff_two_dvd.mpr p.even)).symm.toLinearMap.toContinuousLinearMap

theorem placed (A : Potential G p.side) : Precision.represent (lift G p A)=positiveLinks A := by
  let V:=coordinates G p.side (even_iff_two_dvd.mpr p.even)
  rw [show Precision.represent (lift G p A)=assemble G p.side (V.symm A) from linkField _ _,assemble_exp]
  have eq:=congrArg Subtype.val (V.apply_symm_apply A)
  change coverL G p.side (V.symm A)=A.val at eq
  rw [eq]
  rfl

theorem prepared : Assembly.GradeAt deg (fun A : Potential G p.side => (O (positiveLinks A):ℂ)) := by
  let C:=lift G p
  let L:Potential G p.side →L[ℝ] ℝ × fieldDir G p.side 1 :=
    (0 : Potential G p.side →L[ℝ] ℝ).prod C
  let f:=Bulk.projected (fun (_:ℝ) U=>(O U:ℂ))
  have base:Assembly.GradeAt deg f:=
    (YM.RegulatorIR.FVAAlt2.Sound.Figure.prop R (fun _:Unit=>o) d b ()).prepared p.side
  have equal : (fun A : Potential G p.side => (O (positiveLinks A):ℂ))=f ∘ L := by
    funext A
    change (O (positiveLinks A):ℂ)=(O (Precision.represent (lift G p A)):ℂ)
    rw [placed]
  rw [equal]
  exact base.coarse L.contDiff.contDiffAt L.map_zero

theorem watched : Watching (O) ∧ WatchC (fun U=>(O U:ℂ)) := by
  have reg:ContDiffAt ℝ ∞ (fun A : Potential G p.side => (O (positiveLinks A):ℂ)) 0 :=
    (prepared R p d o b).smooth.of_le (by simp)
  have fixed:=WilsonPositionProgramCopyTop.allowed R p d o b
  exact ⟨⟨fixed.gauge,Complex.reCLM.contDiff.contDiffAt.comp 0 reg⟩,
    ⟨fun u hu v=>congrArg Complex.ofReal (fixed.gauge u hu v),reg⟩⟩

theorem original (D : ChartRatio G) (law : LocalRatio D) :
    Fentry (ChartC (fun A : Potential G p.side => (O (positiveLinks A):ℂ))) =
      Lam.raise (PowerSeries.mk (Orb.diagonalWith D (Orb.restrictedO (O)))) := by
  let ok:Admissible p.side:=⟨p.large,p.even⟩
  obtain ⟨phys,h⟩:=watched R p d o b
  have form:=YM.FVAAlt2.Fixed.readLand law ok (O) phys
  refine (rigidFl ok h).trans ?_
  rw [←form]
  apply congrArg Lentry
  funext A
  apply chart_line
  exact ContDiffAt.comp (f:=g0 G p.side) 0 (by rw [map_zero];exact phys.tame) (ContinuousLinearMap.contDiff (E:=Land G p.side) (F:=Potential G p.side) (𝕜:=ℝ) (g0 G p.side)).contDiffAt

end YM.Integration.WilsonPositionProgramTrialFeynmanFigure
