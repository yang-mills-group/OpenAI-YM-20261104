import YM.Integration.WilsonPositionProgramTrialOrbitAction

/-! The independently prescribed kinetic Gaussian on the actual torus is the
pullback of the reflected-link Wilson precision. Both the occupied and
unoccupied normalizers retain the same determinant and density. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialOrbitWick
open Filter Function MeasureTheory Lattice Gauge FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension PertExtension.Series PertExtension.Orb PertExtension.Chart PertExtension.GaussianScore
open FVA2 FVA2.Trans FVA2.Wilson FVA2.Wilson.FP FVA2.GermLaplace Precision Inherit Push.Loops TreeBasis
open WilsonPositionProgramTrialOrbitAction (coordinates)
open WilsonPositionProgramTrialSiteGauge (reporter)
open WilsonPositionProgramTrialGaugeAction (siteLaw)
open FormalOPE.RG10.MultiGauge PertExtension.Series.Radial MeasureTheory.Measure
open scoped Classical BigOperators Topology ContDiff
variable (G : Gauge) (n : Side) (even : Even n.val)

def vacuum : Law (Cone G n) :=
  Splice.focusWith (pd (Pert.Orb.formL G n) Pert.Orb.form_symm (fun _ h=>Pert.Orb.form_pos h))
    (coordinates G n even).toLinearMap (coordinates G n even).injective

def gauge := Repoint.issue G (staple n) (reporter G n even) (WilsonPositionProgramTrialSiteGauge.original G n even)
def auxiliary := matchW (reporter G n even) (WilsonPositionProgramTrialSiteGauge.original G n even) (siteLaw G n)

theorem quadratic (A : Cone G n) :
    (vacuum G n even).P A A/2=jet (finances (gauge G n even) (auxiliary G n even)) 2 A := by
  let E:=coordinates G n even
  let f : Cone G n→ℝ:= fun x=>Pert.Orb.action G n (E x)
  have equation : finances (gauge G n even) (auxiliary G n even)=f :=
    funext (WilsonPositionProgramTrialOrbitAction.original G n even)
  have smooth : ContDiffAt ℝ 2 f 0 := by
    exact ((show ContDiffAt ℝ ω (Pert.Orb.action G n) (E 0) by simpa using Pert.Orb.diff_action).comp 0
      E.toContinuousLinearEquiv.contDiff.contDiffAt).of_le (by exact le_top)
  have lim (x : Cone G n) : Tendsto (fun t:ℝ=>f (t • x)/t^2) (𝓝[≠] 0) (𝓝 (Pert.Orb.form (E x) (E x)/2)) :=by
    simpa only [f,map_smul] using (Pert.Orb.limit_action (E x))
  have h:=Work.F03.hessian_of_limit smooth lim
    (fun x y z=>by rw [map_add,Pert.Orb.form_add]) (fun x y=>Pert.Orb.form_symm _ _)
  rw [equation]
  change Pert.Orb.form (E A) (E A)/2 = _
  unfold jet
  rw [show (fun _:Fin 2=>A)=![A,A] from by funext i;fin_cases i <;>rfl,h.2.2]
  norm_num [Nat.factorial]
  ring

theorem original (U : ChartRatio G) (auth : LocalRatio U) {O : FVA2.Wilson.Observable G n}
    (phys : Physical O) (he : Honest O) (V : Measure (Cone G n)) [IsAddHaarMeasure V] :
    PowerSeries.mk (Orb.diagonalWith U (Orb.restrictedO O)) =
      Invoice.power V (vacuum G n even) (finances (gauge G n even) (auxiliary G n even)) (volumeK (gauge G n even) U O) *
      (Invoice.power V (vacuum G n even) (finances (gauge G n even) (auxiliary G n even)) (volumeK (gauge G n even) U 1))⁻¹ :=
  gaugeWick (gauge G n even) U auth even phys he (auxiliary G n even) V (vacuum G n even) (quadratic G n even)
end YM.Integration.WilsonPositionProgramTrialOrbitWick
