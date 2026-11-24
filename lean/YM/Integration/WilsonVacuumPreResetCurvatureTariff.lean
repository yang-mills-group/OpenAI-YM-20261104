import YM.Integration.WilsonVacuumPreResetCurvatureReserve

/-! The exact stage tariff controls the three physical curvature sources while
leaving their coefficients and threshold powers visible. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetCurvatureTariff
open RG01Estimate
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Laplace Pressure ConnectedActivityE6 Coat Evoc Push Deck
open Censor Censor.Toft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open FullVolume WilsonLimitConstruction RG01Estimate.Chart
open Comparison.Density Comparison.Density.Render
variable {G:Gauge}


open WilsonVacuumPreResetCurvatureReserve

theorem ears (T:RG.Stage)(B:BudgetPoint)(hs:B.supportExponent≤T.supportExponent+6)(k:ℕ):
    |anchoredFee (headline B) k| ≤ anchor T k:=by
  unfold anchor anchoredFee
  rw [abs_of_nonneg (by positivity)]
  gcongr
  change B.supportExponent+3≤_
  linarith

theorem priced (T D:RG.Stage)(B:BudgetPoint)(ho:B.order=T.order)(hp:B.power=T.power)
    (hs:B.supportExponent≤T.supportExponent+6)(γ β:ℝ):
    |WilsonVacuumPreResetCurvaturePrice.cost (G:=G) B D.clip D.width D.paths γ β| ≤ 
    WilsonVacuumPreResetCurvatureReserve.income G T D*(|γ| *B.threshold^2+|β| *B.threshold^3+|β| *B.threshold^4):=by
  have hlow:|factor| * turnFee B*(lowFee G B D.width*lowerSize D.clip D.paths)=head G T D:=by
    unfold head turnFee lowFee lowCost rowCost faceCost pairBill rowDegree Time.probe
    simp only [ho,hp]
  have hhi (k:ℕ):|factor| * turnFee B*(Geo.highFee G k B D.width*D.paths)=arm G T D k:=by
    unfold arm turnFee Geo.highFee Time.probe
    simp only [ho,hp]
  have low:Song.host G D.clip B D.width D.paths γ=head G T D*(|γ| *B.threshold^2):=by
    rw [←hlow];unfold Song.host;rw [abs_mul];ring
  have hi (k:ℕ):tenor G k B D.width D.paths β=arm G T D k*(|β| *B.threshold^k):=by
    rw [←hhi k];unfold tenor;rw [abs_mul];ring
  have ht:=B.threshold_pos.le
  have ha (k:ℕ):0≤anchor T k:=by unfold anchor;positivity
  have h0:=mul_nonneg (ha lowCount) (abs_nonneg (head G T D))
  have h3:=mul_nonneg (ha (octave 3)) (abs_nonneg (arm G T D 3))
  have h4:=mul_nonneg (ha (octave 4)) (abs_nonneg (arm G T D 4))
  have hq:0≤4*|T.supportExponent+9|/D.width:=by have := D.width_pos;positivity
  have ea:anchor T lowCount*|head G T D| ≤ WilsonVacuumPreResetCurvatureReserve.income G T D:=by unfold WilsonVacuumPreResetCurvatureReserve.income;linarith
  have eb:anchor T (octave 3)*|arm G T D 3| ≤ WilsonVacuumPreResetCurvatureReserve.income G T D:=by unfold WilsonVacuumPreResetCurvatureReserve.income;linarith
  have ec:anchor T (octave 4)*|arm G T D 4| ≤ WilsonVacuumPreResetCurvatureReserve.income G T D:=by unfold WilsonVacuumPreResetCurvatureReserve.income;linarith
  unfold WilsonVacuumPreResetCurvaturePrice.cost
  rw [low,hi,hi]
  calc
    _≤ |anchoredFee (headline B) lowCount*(head G T D*(|γ| *B.threshold^2))|+
      (|anchoredFee (headline B) (octave 3)*(arm G T D 3*(|β| *B.threshold^3))|+
        |anchoredFee (headline B) (octave 4)*(arm G T D 4*(|β| *B.threshold^4))|):=
      (abs_add_le ..).trans (add_le_add (le_refl _) (abs_add_le ..))
    _≤anchor T lowCount*|head G T D| *(|γ| *B.threshold^2)+
      (anchor T (octave 3)*|arm G T D 3| *(|β| *B.threshold^3)+
        anchor T (octave 4)*|arm G T D 4| *(|β| *B.threshold^4)):=by
      simp only [abs_mul,abs_abs,abs_pow,abs_of_nonneg ht]
      simp only [←mul_assoc]
      gcongr <;> exact ears T B hs _
    _≤WilsonVacuumPreResetCurvatureReserve.income G T D*(|γ| *B.threshold^2)+
      (WilsonVacuumPreResetCurvatureReserve.income G T D*(|β| *B.threshold^3)+WilsonVacuumPreResetCurvatureReserve.income G T D*(|β| *B.threshold^4)):=by gcongr
    _= _:=by ring

end YM.Integration.WilsonVacuumPreResetCurvatureTariff
