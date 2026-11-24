import YM.Integration.WilsonOriginalPublicNodalFrequencyFilm
import YM.Integration.WilsonIndependentSpoutMasterEnrolledOrbit
import YM.Integration.WilsonOriginalPublicNodalBufferedCellAppointment

/-! The physical subcell integral of the truly submitted, reported torus film is measurable in the full Fourier frequency. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalFrequencyCash
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



open WilsonOriginalPublicNodalBufferedCellAppointment (opened native)
open WilsonOriginalPublicNodalBufferedCellFilm (paper full)
open WilsonPositionProgramTrialPublicJointRoom (normalized)
open WilsonPositionProgramTrialPublicCellHull (hull)
open WilsonIndependentSpoutMasterOrbitClock (measure)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped ContDiff
variable (c:Fin (n+1)→Bool)(z:J)(b:Herit (deck (G:=G) d D cut))(B:Cost)(q:ℕ)(g:ℝ)

def cashAt (ν ξ:Points (n+1)):ℂ:=cash q g (measure B
  (opened R W m j d D cut home (fun t=>normalized (T t) ν c) y o σ sp sample (native ξ) z b))

theorem original (real:∀i,ContDiff ℝ ∞ (T z i).ψ.val):
    let S:=cube 1 1 (0:Fin (n+1)→ Cover)
    let f:=cashAt R W m j d D cut home T y o σ sp sample c z b B q g
    ContinuousOn (fun p:Points (n+1) × Points (n+1)=>f p.1 p.2) (Set.univ ×ˢ S) ∧
      StronglyMeasurable (fun ν=>∫ξ in S,f ν ξ):=by
  intro S f
  let a:=paceT (R.family.path.levels).S (home z) (m z+j z)
  let w₀:=vector R d D cut b (home z) (m z+j z)
  let H:=fun i=>hull (T z i) a (y z) (σ z) (o z)
  let row:=fun p:Points (n+1) × Disp n=>cash q g (measure B (full R W (fun _=>false) d D cut
    (sample z) (normalized (T z) p.1 c) (fun _=>a) (y z) (σ z) (sp z) (fun _=>o z) H w₀ p.2))
  have ink:Continuous row:=by
    unfold row
    unfold cash
    apply continuous_finsetSum
    intro j' _
    apply continuous_const.mul
    simp only [WilsonIndependentSpoutMasterOrbitClock.shares]
    apply continuous_finsetSum
    intro e' _
    exact (WilsonOriginalPublicNodalFrequencyFilm.ledger R W (fun _=>false) d D cut (sample z)
      (T z) real c (fun _=>a) (y z) (σ z) (sp z) (fun _=>o z) w₀ H e').mul continuous_const
  let fixed:=fun p:Points (n+1) × Points (n+1)=>row (p.1,native p.2)
  have nativeCont:Continuous (native (n:=n)):=by
    apply continuous_pi
    intro i
    exact (PiLp.continuous_ofLp 2 _).comp (PiLp.continuous_apply 2 _ i)
  have smooth:Continuous fixed:=ink.comp (continuous_fst.prodMk (nativeCont.comp continuous_snd))
  have equality (ν ξ:Points (n+1))(fit:ξ∈S):f ν ξ=fixed (ν,ξ):=by
    exact congrArg (fun series:PowerSeries ℂ=>cash q g (measure B series))
      (WilsonOriginalPublicNodalBufferedCellFilm.original R W (fun _=>false) d D cut (sample z)
        (normalized (T z) ν c) (fun _=>a) (y z) (σ z) (sp z) (fun _=>o z) w₀
        (fun _=>pace_pos ..) (native ξ) (WilsonPositionProgramTrialPublicReflectedCells.bounded fit))
  constructor
  · apply smooth.continuousOn.congr
    exact fun p entered=>equality p.1 p.2 entered.2
  · have agree:(fun ν=>∫ξ in S,f ν ξ)=(fun ν:Points (n+1)=>∫ξ in S,fixed (ν,ξ)):=by
      funext ν
      exact setIntegral_congr_fun (WilsonMeasuredPublicEntranceCoverCells.visible 1 1 one_pos _)
        (equality ν)
    rw [agree]
    exact smooth.stronglyMeasurable.integral_prod_right'

end YM.Integration.WilsonOriginalPublicNodalFrequencyCash
end
