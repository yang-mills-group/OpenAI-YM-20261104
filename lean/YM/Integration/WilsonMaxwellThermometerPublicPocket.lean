import YM.Integration.WilsonMaxwellThermometerNominatedCofactor
import YM.Integration.WilsonPositionGradedThermometerHearing
import YM.Integration.WilsonPositionOriginalCalibrationSensitivity

/-! The restored lower component of the coordinates cubic is read on its true
three-field cutoff. The cell weights retain both independent relative
positions and integrate the common center. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicPocket
open PhysicalNext.Repeat.Legato
open Function Filter MeasureTheory Lattice Wilson RG Maxwell Maxwell.Free RG17 XSpace XSpace.Normalize
open Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress PhysMS PhysMS.Frame
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedReading
open WilsonMaxwellThermometerNominatedCofactor WilsonPositionPrescribedFrame
open scoped Topology Classical BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S)
  (J:ℝ→PhysMS.tower S) (V:Store G) (K:Rose.Pick V) (A:ℝ→Group R.family 6)

def receipt (group:Group R.family 6) (r:ℝ) (z:ℕ×ℕ) (T:Test 3):
    C(Config G (R.family.side z.1 z.2),ℂ)→ₗ[ℂ]ℂ :=
  ∑o,WilsonThermometerAlignedCells.mass (R:=R) r z T o • reading R group z.1 z.2 o

def shoulder (group:Group R.family 6) (z:ℕ×ℕ) (e:RG17.Free R.family 4):
    C(Config G (R.family.side z.1 z.2),ℂ):=
  file R z.1 z.2 (group.station.wheel.atCut z (index group (⟨4,by decide⟩:Fin 7)) (group.change 4 e)) 0

def measured (r:ℝ) (z:ℕ×ℕ) (e:RG17.Free R.family 4):ℂ :=
  receipt R (WilsonPositionCorrectedCap.adjusted F J V A r) r z (Rose.test K) (shoulder R (A r) z e)

variable {I:Type} [Fintype I]
def coordinates (D:RG17.Free R.family 6 →L[ℂ] (I→ℂ)) (r:ℝ):I→ℂ :=
  let b:RG17.Free R.family 6:=(fields R.family.labels 6).symm (Rose.toll G)
  D (change F J V 6 r b-b)

theorem reading (D:RG17.Free R.family 6 →L[ℂ] (I→ℂ)) (e:I→RG17.Free R.family 4) (r:ℝ) (z:ℕ×ℕ):
    receipt R (WilsonPositionCorrectedCap.adjusted F J V A r) r z (Rose.test K)
      (∑i,coordinates R F J V D r i • shoulder R (A r) z (e i))=
    ∑i,coordinates R F J V D r i * measured R F J V K A r z (e i):=by
  rw [map_sum]
  simp only [map_smul,smul_eq_mul,measured]

theorem signed (lead:Leading F J) (D:RG17.Free R.family 6 →L[ℂ] (I→ℂ)):
    ∃c:ℝ,0≤c ∧ ∀ᶠr in trail,‖coordinates R F J V D r‖≤c*WilsonPositionOriginalCalibrationSensitivity.price F J V 6 r := by
  obtain ⟨c,hc,rate⟩:=WilsonPositionOriginalCalibrationSensitivity.field F J V lead 6 (Rose.toll G)
  refine ⟨‖D‖*c,mul_nonneg D.opNorm_nonneg hc,?_⟩
  filter_upwards [rate] with r hr
  exact (D.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hr D.opNorm_nonneg).trans_eq (mul_assoc ..).symm)

omit [Fintype I] in
theorem small (lead:Leading F J) (D:RG17.Free R.family 6 →L[ℂ] (I→ℂ)):
    Tendsto (fun r=>coordinates R F J V D r) trail (𝓝 0):=by
  let b:RG17.Free R.family 6:=(fields R.family.labels 6).symm (Rose.toll G)
  let h:=fun r=>WilsonPositionPrescribedLift.field F J V 6 r-ContinuousLinearMap.id ℂ (RG17.Free R.family 6)
  have near := WilsonPositionPrescribedLift.near F J V lead 6
  have hb:Tendsto (fun r=>h r b) trail (𝓝 0):=by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _=>norm_nonneg _) (fun r=>(h r).le_opNorm b) (by simpa using near.mul_const ‖b‖)
  have eqn (r:ℝ): (h r) b=change F J V 6 r b-b:=rfl
  simpa only [Function.comp_def,eqn,map_zero,coordinates,b] using (D.continuous.tendsto 0).comp hb

end YM.Integration.WilsonMaxwellThermometerPublicPocket
