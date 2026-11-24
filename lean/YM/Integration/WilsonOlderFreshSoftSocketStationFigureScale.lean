import YM.Integration.WilsonOlderFreshSoftSocketTotal
import YM.Integration.WilsonOriginalObservedRoseFittedWeights

/-! The actual physical panel has already incorporated each inverse mesh power in its registered votes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationFigureScale
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketMeasuredCash (packet seats ticket)
open WilsonOlderFreshSoftSocketFaces (raw fill)
open WilsonOlderFreshSoftSocketRestored (degree stopped coin)
open WilsonOlderFreshSoftSocketKinetic (kinetic)
open WilsonOlderFreshHybridClock (flat)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReportingAbsoluteInletForecastBooks (value)
open WilsonOriginalStarSceneWords (pole)
open WilsonReceivedFixedDigitHistory WilsonCoeffUV.Winding ActualRunPhysicalPages Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(d:I→ℕ){D:I→ℕ}
open WilsonOriginalPublicTrialFigure (amount)
open WilsonPositionProgramReportedField (entire)
open WilsonOlderFreshSoftSocketTotal (figure)
open RG16.Literal Source Labels
omit [Fintype I] [DecidableEq I] in
theorem packet_scale (S:Finset I)(a:I→ℂ)(w:(i:I)→R.family.label (d i))(N per K:ℕ)
    (b:Columns R (fun i:S=>d i)):
    packet R d S (fun i=>a i • w i) N per K b=(∏i∈S,a i)*packet R d S w N per K b:=by
  have slot(i:S):amount R d (regulatorRun R.family N per K)
      (fun j=>entire R (d j) K (N,per) (a j • w j)) i (b i)=
      a i*amount R d (regulatorRun R.family N per K) (fun j=>entire R (d j) K (N,per) (w j)) i (b i):=by
    simp only [WilsonOriginalPublicTrialFigure.amount,WilsonPositionProgramReportedField.entire,gMap,Frame.scaled_apply,Pi.smul_apply,smul_eq_mul]
    ring
  unfold WilsonOlderFreshSoftSocketMeasuredCash.packet
  simp_rw [slot]
  rw [prod_mul_distrib,prod_coe_sort]

theorem scaled (κ:(i:I)→Knob (D i))(pt:I→Chamber)(N per K c v:ℕ)(cells:Digits R.family.path.levels I)
    (S:Finset I)(a:I→ℂ)(w:(i:I)→R.family.label (d i))(y:I → Cover)(test:Pen D S→L[ℝ]ℝ)(p:ℕ)(θ:ℝ):
    figure R d κ pt N per K c v cells S (fun i=>a i • w i) y test p θ=
      (∏i∈S,a i)*figure R d κ pt N per K c v cells S w y test p θ:=by
  unfold figure
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  rw [packet_scale]
  ring

open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonReceivedChronologicalHeldEntrance (coords)
open WilsonMeasuredPublicEntranceCellWords WilsonAddressedPhysicalCells
open WilsonReflectedPublicOrientedFaces
open WilsonMovingForkHeterogeneousCut
open PertExtension PertExtension.LatticePT
theorem on_panel (d D:Fin 3→ℕ)(κ:(i:Fin 3)→Knob (D i))(pt:Fin 3→Chamber)
    {N per f n c v req pow step:ℕ}{B:ℝ}(cut:f+n≤N)
    (P:Panel R d N per f (f+n) (Nat.le_add_right f n) cut req pow step B)
    (file:Filed R d (f+n))(station:P.slot=file.station)(axes:P.axis=file.A N per)
    (cells:Digits R.family.path.levels (Fin 3))(S:Finset (Fin 3))(y:Fin 3 → Cover)
    (test:Pen D S→L[ℝ]ℝ)(p:ℕ)(θ r:ℝ):
    (∏i∈S,(r:ℂ)^d i)*figure R d κ pt N per (f+n) c v cells S
        (votes R d (N:=N) (per:=per) file P.names P.turn) y test p θ=
      (∏i∈S,((r:ℂ)/(R.family.S.a (f+n):ℂ))^d i)*figure R d κ pt N per (f+n) c v cells S
        (coords R d cut P) y test p θ:=by
  let a(i:Fin 3):ℂ:=(((R.family.S.a (f+n)):ℂ)^d i)⁻¹
  have booked:votes R d (N:=N) (per:=per) file P.names P.turn=fun i=>a i • coords R d cut P i:=by
    funext i
    dsimp only [WilsonOriginalObservedRoseCorrectedWords.votes,WilsonMovingForkMixedSeed.units,WilsonMovingForkMixedSeed.doses,WilsonReceivedChronologicalHeldEntrance.coords,a]
    rw [←station,←axes]
  rw [booked,scaled,←mul_assoc,←prod_mul_distrib]
  congr 1
  apply prod_congr rfl
  intro i _
  exact (div_pow (r:ℂ) (R.family.S.a (f+n):ℂ) (d i)).symm

end YM.Integration.WilsonOlderFreshSoftSocketStationFigureScale
end
