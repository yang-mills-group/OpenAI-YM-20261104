import YM.Integration.WilsonPositionProgramTrialPublicCellIntegral
import YM.Integration.WilsonPositionProgramTrialPublicReflectedCells

/-! Bounds on the true thermal scalar under the continuum cell integral for the original and reissued Wilson inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicCellObserver
open Precision Function Finset Lattice Laurent Wilson RG Source Labels Marker Tree Exterior PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.StableStrip WilsonCoeffUV.Power
open RG.Supply Next.Foundations PhysicalNext.Repeat
open WilsonFiniteMarkedHistoryStep
open WilsonOriginalPublicNodalChildSites (digits here)
open WilsonPositionProgramTrialPublicPulse (choices frame sites survey)
open WilsonReceivedCanonicalSocketSeed (contact)
open WilsonPositionProgramTrialPublicGather (gather)
open WilsonPositionProgramTrialPublicOldReturn (portfolio)
open WilsonIndependentMatchedOpeningFiled (planted)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentRawPhysicalFaces (ordered entered)
open WilsonOriginalPhysicalFruitVerse (written)
open WilsonPositionProgramTrialHomeFaces (Filed)
open WilsonMarkedIndependentNormalizedElection (deck)
open PertExtension RegulatorIR RegulatorIR.Cluster XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
open WilsonIndependentMatchedPhysicalReturn (ordinary)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonPositionProgramTrialAccrued (home)

variable {G:Gauge}{a n:ℕ}
open MeasureTheory Extraction Table
open WilsonPositionProgramTrialPublicCensusReturn (logged)
open WilsonPositionProgramTrialPublicCellVisits (node)
open WilsonPositionProgramTrialPublicCellPhase (layout moved)
open WilsonMeasuredPublicEntranceCoverCells (cube)
open WilsonViewerAffineCells (pull)

open private pull_test from YM.Integration.WilsonPositionProgramTrialPublicCellIntegral

def grade (G:Gauge)(q:ℕ):Era G ℝ→ₗ[ℝ]ℂ where
  toFun A:=((A.2 q 0 Fin.elim0:ℝ):ℂ)
  map_add' a b:=by change (((a.2 q 0 Fin.elim0+b.2 q 0 Fin.elim0:ℝ)):ℂ)=_;rw [Complex.ofReal_add]
  map_smul' r a:=by change (((r*a.2 q 0 Fin.elim0:ℝ)):ℂ)=r • _;rw [Complex.real_smul,Complex.ofReal_mul]

theorem single {e u q:ℕ}{A B:Era G ℝ}{fee:ℝ}(live:q≤e)(earned:response e u (A-B) fee):
    ‖grade G q A-grade G q B‖≤fee:=by
  change ‖(A.2 q 0 Fin.elim0:ℂ)-(B.2 q 0 Fin.elim0:ℂ)‖≤fee
  rw [←Complex.ofReal_sub,Complex.norm_real]
  exact earned.2 q live Fin.elim0

def tile (n:ℕ):Set (Points n):=cube 1 1 (0:Fin n → Cover)

theorem finite (n:ℕ):volume (tile n)≠⊤:=by
  let fill:(Fin n→Point4)→Points n:=fun b=>WithLp.toLp 2 (fun i=>WithLp.toLp 2 (b i))
  have smooth:Continuous fill:=by unfold fill;fun_prop
  have compact:= (isCompact_closedBall (0:Fin n→Point4) 1).image smooth
  have crop:tile n⊆fill '' Metric.closedBall 0 1:=by
    intro ξ paid
    refine ⟨fun i e=>ξ i e,?_,rfl⟩
    change dist _ 0≤1
    rw [dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 (WilsonPositionProgramTrialPublicReflectedCells.bounded paid)
  exact ne_top_of_le_ne_top compact.measure_ne_top (measure_mono crop)

theorem integrated {A B:Points n→Era G ℝ}{e u q:ℕ}{fee E:ℝ}(nonneg:0≤E)(live:q≤e)
    (trueA:IntegrableOn (fun ξ=>E • grade G q (A ξ)) (tile n))
    (trueB:IntegrableOn (fun ξ=>E • grade G q (B ξ)) (tile n))
    (earned:∀ξ∈tile n,response e u (A ξ-B ξ) fee):
    ‖(∫ξ in tile n,E • grade G q (A ξ))-(∫ξ in tile n,E • grade G q (B ξ))‖≤
        volume.real (tile n)*(E*fee):=by
  have meas:MeasurableSet (tile n):=WilsonMeasuredPublicEntranceCoverCells.visible 1 1 one_pos _
  let μ:=volume.restrict (tile n)
  haveI : IsFiniteMeasure μ:=⟨by simpa only [μ,Measure.restrict_apply_univ] using (finite n).lt_top⟩
  rw [←integral_sub trueA trueB]
  have price:∀ᵐξ ∂μ,‖E • grade G q (A ξ)-E • grade G q (B ξ)‖≤E*fee:=by
    apply (ae_restrict_iff' meas).mpr
    exact ae_of_all _ (fun ξ x=>by
      rw [←smul_sub,norm_smul,Real.norm_of_nonneg nonneg]
      exact mul_le_mul_of_nonneg_left (single live (earned ξ x)) nonneg)
  calc
    _≤∫ξ,‖E • grade G q (A ξ)-E • grade G q (B ξ)‖ ∂μ:=norm_integral_le_integral_norm _
    _≤∫_ : Points n,E*fee ∂μ:=integral_mono_ae (trueA.sub trueB).norm (integrable_const _) price
    _=volume.real (tile n)*(E*fee):=by simp [μ,Measure.real]

end YM.Integration.WilsonPositionProgramTrialPublicCellObserver
end
