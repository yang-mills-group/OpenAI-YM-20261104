import YM.Integration.WilsonOriginalPublicNodalBufferedCellFilm
import YM.Integration.WilsonPositionProgramTrialPublicReflectedCells

/-! On the physical displacement cube the reported fresh torus pupil at the very same compensated home is integrable. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalBufferedCellAppointment
open Lattice RG Source Labels Wilson Tree XSpace XSpace.Cirrus Finset PowerSeries MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open WilsonCoeffUV.Bank WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Wheel.Mark
open PhysicalNext.Repeat.Legato RegulatorIR.Profiles
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentSpoutNormalizedMaster (vector)
open WilsonPositionProgramTrialPublicCellPulse (placed)
open WilsonOriginalPublicNodalBufferedCellFilm (Disp)
open WilsonMeasuredPublicEntranceCoverCells (cube)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n:ℕ}{J:Type}(R:Run G)(W:Initialize G)(m j:J→ℕ)
  (d D:Fin (n+1)→ℕ)(cut:∀i,d i<D i)(home:J→ℕ)(T:J→(i:Fin (n+1))→Rarity (D i))
  (y:J→ℝ)(o:J→CellR)(σ:J→ℝ)(sp:∀z,0<σ z)(sample:J→Sample 2)
local notation "Q" => (deck (G:=G) d D cut)
local notation "L" => R.family.path.levels
local notation "x" => (fun z:J=>paceT (L).S (home z) (m z+j z))

def planted (ξ:Disp n)(z:J)(i:Fin (n+1)):Rarity (D i):=
  placed (T z i) (x z) (y z) (σ z) (sp z) (o z) (ξ i)
def opened (ξ:Disp n)(z:J)(b:Herit Q):PowerSeries ℂ:=
  WilsonOriginalPublicNodalBufferedOrbit.film R W m j d D cut home
    (planted R m j D home T y o σ sp ξ) y o sample z b

theorem seated (ξ:Disp n)(z:J)(b:Herit Q):
    opened R W m j d D cut home T y o σ sp sample ξ z b=
      WilsonOriginalPublicNodalBufferedCellFilm.paper R W (fun _=>false) d D cut (sample z) (T z)
        (fun _=>x z) (y z) (σ z) (sp z) (fun _=>o z) (vector R d D cut b (home z) (m z+j z)) ξ:=rfl

def native (ξ:Points (n+1)):Disp n:=fun i e=>ξ i e
def points (ξ:Disp n):Points (n+1):=WithLp.toLp 2 (fun i=>WithLp.toLp 2 (ξ i))

theorem reported (z:J)(b:Herit Q)(clock:Feeds)(pole q:ℕ):
    IntegrableOn (fun ξ:Points (n+1)=>coeff q (WilsonIndependentPublicReportComplex.apply clock pole
      (opened R W m j d D cut home T y o σ sp sample (native ξ) z b))) (cube 1 1 (0:Fin (n+1)→ Cover)):=by
  let cube₀:=Metric.closedBall (0:Disp n) 1
  let K:=points '' cube₀
  have pointsCont:Continuous (points (n:=n)):=by
    apply (PiLp.continuous_toLp ..).comp
    exact continuous_pi fun i=>(PiLp.continuous_toLp ..).comp (continuous_apply i)
  have nativeCont:Continuous (native (n:=n)):=by
    apply continuous_pi
    intro i
    exact (PiLp.continuous_ofLp 2 _).comp (PiLp.continuous_apply 2 _ i)
  have compact:IsCompact K:=(isCompact_closedBall (0:Disp n) 1).image pointsCont
  have inside (ξ:Disp n)(inbox:ξ∈cube₀)(i):‖ξ i‖ ≤ 1:=
    (norm_le_pi_norm ξ i).trans (mem_closedBall_zero_iff.mp inbox)
  have continuousFilm:=WilsonOriginalPublicNodalBufferedCellFilm.measured R W (fun _=>false) d D cut
    (sample z) (T z) (fun _=>x z) (y z) (σ z) (sp z) (fun _=>o z) cube₀ (fun _=>pace_pos ..) inside
    (vector R d D cut b (home z) (m z+j z)) clock pole q
  have realField:ContinuousOn (fun ξ:Points (n+1)=>coeff q (WilsonIndependentPublicReportComplex.apply clock pole
      (opened R W m j d D cut home T y o σ sp sample (native ξ) z b))) K:=by
    apply continuousFilm.comp nativeCont.continuousOn
    rintro _ ⟨t,ht,rfl⟩
    exact ht
  apply (realField.integrableOn_compact compact).mono_set
  intro ξ entered
  have fits:native ξ∈cube₀:=mem_closedBall_zero_iff.mpr <|
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr (WilsonPositionProgramTrialPublicReflectedCells.bounded entered)
  exact ⟨native ξ,fits,rfl⟩

theorem value (z:J)(b:Herit Q)(clock:Feeds)(pole Qmax:ℕ)(u:ℝ):
    let A:=fun l (ξ:Points (n+1))=>coeff (pole+l) (WilsonIndependentPublicReportComplex.apply clock pole
      (opened R W m j d D cut home T y o σ sp sample (native ξ) z b))
    let set:=cube 1 1 (0:Fin (n+1)→ Cover)
    IntegrableOn (fun ξ=>∑l∈range (Qmax+1),(u:ℂ)^l*A l ξ) set ∧
      (∫ξ in set,∑l∈range (Qmax+1),(u:ℂ)^l*A l ξ)=
        ∑l∈range (Qmax+1),(u:ℂ)^l*∫ξ in set,A l ξ:=by
  intro A set
  have row l:IntegrableOn (A l) set:=reported R W m j d D cut home T y o σ sp sample z b clock pole (pole+l)
  have term l:IntegrableOn (fun ξ=>(u:ℂ)^l*A l ξ) set:=(row l).const_mul _
  constructor
  · exact integrable_finsetSum _ (fun l _=>term l)
  · rw [integral_finsetSum _ (fun l _=>term l)]
    simp only [integral_const_mul]

end YM.Integration.WilsonOriginalPublicNodalBufferedCellAppointment
end
