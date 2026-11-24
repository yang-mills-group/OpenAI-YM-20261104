import YM.Integration.WilsonQ198WithinPricePhaseMatrix
import YM.Integration.WilsonGraphUniformMixedShapeMass
import YM.Integration.WilsonPositionHomogeneousLeading
import YM.PhysMS.Frame.Phases
import YM.RG17.Aperture
import YM.Integration.WilsonGraphAppointedMeasurementLaws
import YangMills.WilsonProof.NativeSupport.IssuedBridge.WilsonQ198PostFrankValue
import YM.Integration.WilsonGraphAppointedStationaryPrices
import YM.Integration.WilsonQ198PhysicalPhaseWords

noncomputable section
namespace YM.Integration.WilsonQ198PublicPhaseProximity

open YM YM.Integration YM.FVA2.Dframe YM.FVA2.O.Score

open Function Filter Set Asymptotics PowerSeries
open Lattice RG MeasureTheory Wilson Extraction Climb Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Fleet PhysMS PhysMS.Frame Next.UVStress OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale FVA2.Scale.Level
open SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane
open SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Integration.Election Integration.Election.Frames
open Order Spin SignedWilsonExpansion.StageG XSpace.Cirrus Entree Future
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open Integration.GradedFar Integration.GradedFar.Tariff
open Integration.GradedFar.Tariff.Sunshine
open WilsonPositionHomogeneousComparison
open scoped Topology BigOperators Classical ContDiff

universe u
variable {g : YangMills.GaugeGroup} {H : g.core.Simple} {ε : ℝ} {e : Axis} {O : OrderS g.core}
variable {E : Construction.{u} H ε e O} {ξ : Extraction.Order}
variable (Z : WilsonPrescription g.core) (V : Vision E ξ) (Q : Perspective H Z true)
local notation "t" => V.T Z
local notation "X" => FVA2.Scale.Measure.outlook Z.scheme Z.criterion




open YM.FVA2 YM.FVA2.Register YM.FVA2.Scale YM.FVA2.Scale.Level


open YM.Integration.GradedFar.Tariff YM.FVA2.GradedFar YM.Trace.Pilot
open YM.Integration.WilsonGraphUniformMixedShapeMass
open YM.Answer.ContinuumLimit

theorem published (hg : g.IsSimple) (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) :
    YangMills.Matching.CorrelationOnly.PhaseProximity (ElectedMeasurement.publicMeasurement hg V Z Q) := by
  classical
  intro n j d K compact separated γ hγ h4
  have safe : K ⊆ conf n := separated
  let a : ℝ := (γ+4)/2
  have hga : γ < a := by dsimp [a]; linarith
  have ha : a < 4 := by dsimp [a]; linarith
  obtain ⟨C,hC,prices⟩ := YM.Integration.WilsonQ198WithinPricePhaseMatrix.original Z V Q
    d K compact safe a ha j
  have hexp : 0 < a-γ := sub_pos.mpr hga
  have continuous : ContinuousAt (fun r : ℝ => C*r^(a-γ)) 0 := by
    fun_prop (disch := positivity)
  have vanish : Tendsto (fun r : ℝ => C*r^(a-γ)) trail (𝓝 0) := by
    simpa only [Real.zero_rpow hexp.ne',mul_zero] using
      continuous.tendsto.mono_left (show trail ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have absorbed : ∀ᶠ r in trail, C*r^(a-γ) ≤ 1 :=
    (vanish.eventually (Iio_mem_nhds (show (0 : ℝ)<1 by norm_num))).mono
      (fun r h => le_of_lt h)
  filter_upwards [prices,absorbed,(show ∀ᶠr : ℝ in trail, 0<r from self_mem_nhdsWithin)]
    with r paid absorb hr p q o v x hx
  let Fp (ν : Viewers V.pupil.last) (y : Points n) :=
    TrueCompact V.pupil.last (V.Post Z) ν r o y v
  let M := ElectedMeasurement.publicMeasurement hg V Z Q
  have e : (fun y => YangMills.Matching.CorrelationOnly.phaseDifference M r o
        (fun i => ⟨d i,v i⟩) p q y) =ᶠ[𝓝 x] (fun y => Fp p y - Fp q y) := by
    filter_upwards [(conf_open n).mem_nhds (safe hx)] with y hy
    change (YangMills.hierarchy V.pupil.last V.pupil.P).correlation p
        (M.inputs r (fun i => ⟨d i, v i⟩))
          (WithLp.toLp 2 (fun i : Fin n => o+r•y i)) -
      (YangMills.hierarchy V.pupil.last V.pupil.P).correlation q
        (M.inputs r (fun i => ⟨d i, v i⟩))
          (WithLp.toLp 2 (fun i : Fin n => o+r•y i)) = _
    rw [show M.inputs r (fun i => ⟨d i, v i⟩) =
        ElectedMeasurement.inputs V Z r d v from ElectedMeasurement.publicInputs hg V Z Q r d v,
      ElectedMeasurement.scalar V Z p d v hr o y hy,
      ElectedMeasurement.scalar V Z q d v hr o y hy]
  have smooth (ν : Viewers V.pupil.last) : ContDiffAt ℝ j (Fp ν) x :=
    ((YM.Integration.WilsonQ198WithinPricePhaseMatrix.compactSmooth V.pupil.last
      (V.Post Z) ν d v o hr).contDiffAt ((conf_open n).mem_nhds (safe hx))).of_le (WithTop.coe_le_coe.mpr le_top)
  have subJet : iteratedFDeriv ℝ j (fun y => Fp p y - Fp q y) x =
      iteratedFDeriv ℝ j (Fp p) x - iteratedFDeriv ℝ j (Fp q) x := by
    exact iteratedFDeriv_sub_apply (smooth p) (smooth q)
  rw [(e.iteratedFDeriv ℝ j).eq_of_nhds,subJet]
  have hm : 0 ≤ inputMass g v := by
    exact Finset.prod_nonneg (fun i _ => YangMills.Matching.sectorMass_nonneg _)
  have split : r^a = r^(a-γ)*r^γ := by rw [← Real.rpow_add hr]; congr 1; ring
  calc
    _ ≤ C*r^a*inputMass g v := paid o x hx p q v
    _ = (C*r^(a-γ))*r^γ*inputMass g v := by rw [split]; ring
    _ ≤ 1*r^γ*inputMass g v :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right absorb (Real.rpow_nonneg hr.le _)) hm
    _ = _ := by simp [inputMass]

end YM.Integration.WilsonQ198PublicPhaseProximity

