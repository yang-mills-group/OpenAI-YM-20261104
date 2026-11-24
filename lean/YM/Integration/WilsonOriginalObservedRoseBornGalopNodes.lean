import YM.Integration.WilsonOriginalObservedRoseBornSignal
import YM.Integration.WilsonOriginalObservedRoseBornAbsolute

/-! Ground of the preassigned position prescription on the occupied physical cells. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornGalopNodes
open Filter Function Set Finset PowerSeries Lattice RG Wilson Maxwell XSpace XSpace.Cirrus XSpace.Normalize
open XSpace.Rose XSpace.Structure1 PhysicalNext.Repeat.Legato Spec Extraction OPE Trace Trace.Pilot
open WilsonOriginalObservedRoseProgram (entry face)
open WilsonMaxwellThermometerPublicGalop (quotient)
open WilsonPositionThermometerConnected (value)
open FVA2 FVA2.Register MS MS.WilsonBridge.Coupling
open WilsonReceivedChronologicalFixedRoseVariation (cells)
open WilsonOriginalObservedRoseBornAbsolute (cell)
open WilsonMaxwellThermometerPublicStation (aperture granted)
open WilsonMaxwellThermometerSignedWallet (board)
open WilsonOriginalObservedRoseBornSlope (ground)
open scoped Classical BigOperators Topology

variable {G:Gauge}(R:Run G)(Z:WilsonPrescription G)

theorem position (x:Sample 3):
    entry Z.scheme (V:=Z.store) x (tag G)=together Z.scheme Z.store x:=by
  unfold WilsonOriginalObservedRoseProgram.entry together
  apply congrArg b3
  funext s
  apply PowerSeries.ext
  intro e
  rw [face,batchT,coeff_mk,coeff_mk]
  exact (Rose.detail Z.scheme Z.store x (tag G) e s).symm

theorem vanished (x:Sample 3)(ready:Z.store.Meets Z.scheme x.F 6):
    value (quotient Z.scheme (V:=Z.store) x (tag G) 0)=0:=by
  rw [←WilsonOriginalObservedRoseProgram.constant,position]
  have odd:=congrArg (coeff (R:=ℂ) 0) (parity₂ Z.scheme x ready)
  rw [inversion,coeff_rescale,pow_zero,one_mul,map_neg] at odd
  linear_combination odd/2

theorem grid (Φ:Test 3)(r:ℝ)(f per:ℕ)(ready:Z.store.Meets Z.scheme (board R f r per) 6):
    (∀y:cells R Φ r (f,per),value (quotient Z.scheme (V:=Z.store) (cell R Φ r f per y) (tag G) 0)=0) ∧
    ground Z (fun y:cells R Φ r (f,per)=>WilsonCenteredCompactBooking.mass R Φ r (f,per) y.val)
      (cell R Φ r f per)=0:=by
  have each (y:cells R Φ r (f,per)):=vanished Z (cell R Φ r f per y) ready
  exact ⟨each,by unfold ground; simp only [each,mul_zero,sum_const_zero]⟩

theorem original (Φ:Test 3)(o:Extraction.Order)(U:Filter (ℕ×ℕ))(prior:U≤o.fuse)
    (s:ℝ→ℕ)(small:Tendsto (aperture R s) trail (𝓝 0)):
    Tendsto (fun w:ℝ×(ℕ×ℕ)=>board R (s w.1) w.1 w.2.2) (trail.curry U) Front ∧
    ∀ᶠ w:ℝ×(ℕ×ℕ) in trail.curry U,
      Z.store.Meets Z.scheme (board R (s w.1) w.1 w.2.2) 6 ∧
      (∀y:cells R Φ w.1 (s w.1,w.2.2),value (quotient Z.scheme (V:=Z.store)
        (cell R Φ w.1 (s w.1) w.2.2 y) (tag G) 0)=0) ∧
      ground Z (fun y:cells R Φ w.1 (s w.1,w.2.2)=>
        WilsonCenteredCompactBooking.mass R Φ w.1 (s w.1,w.2.2) y.val)
        (cell R Φ w.1 (s w.1) w.2.2)=0:=by
  have geo:=WilsonSeparatedOriginalThermometerDetectorMesh.reporting R trail o U prior s
    (aperture R s) (granted R s) small
  have voted:∀ᶠ m in Front,Z.store.Meets Z.scheme m 6:=
    (Z.store.nested_solution Z.scheme 6 Cirrus.frontier).2.mono fun _ h=>h.1
  refine ⟨geo,?_⟩
  filter_upwards [geo.eventually voted] with w h
  exact ⟨h,grid R Z Φ w.1 (s w.1) w.2.2 h⟩

end YM.Integration.WilsonOriginalObservedRoseBornGalopNodes
