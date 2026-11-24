import YM.Integration.WilsonPhysicalChiralPairReading
import YM.Integration.WilsonPositionProgramReflectedPurse

/-! The uniformly invertible measured chiral matrix and its actual two
registered separated test functions, on the prescribed period and mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralPurse
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Maxwell Maxwell.Free
open XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Photo
open WilsonMaxwellThermometerReflectedIncidence Table.Pairing
open WilsonMaxwellThermometerPublicStation (aperture)
open WilsonMaxwellThermometerSignedWallet (board)
open WilsonPhysicalChiralPairReading (Paid)
open WilsonPositionProgramReflectedPurse (shape)
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open Trace Trace.Pilot FVA2 FVA2.Register Spec Extraction OPE PhysicalNext.Repeat.Legato MS MS.WilsonBridge.Coupling
open scoped Classical BigOperators Topology

variable {G:Gauge}(Z:WilsonPrescription G)(a:Axis)(x:E4){I:Type}[Fintype I](b:I→Sec G 6)

theorem original (R:Run G)(hx:0<x a)(o:Extraction.Order)(U:Filter (ℕ×ℕ))(prior:U≤o.fuse)
    (s:ℝ→ℕ)(small:Tendsto (aperture R s) trail (𝓝 0))(Q:Fin 2→SealR G)(y:ℝ):
    ∃B:Bulb (site x) a,∃C:ℝ,∃D:I→ℝ,∃φ:Wilt Q,∃fees:Fin 2→ℝ,
      0<C ∧ (∀i,0≤D i) ∧ (∀i,(φ i).ψ.val=shape a x B i) ∧
      (∀ᶠ space:ℝ in atTop,Bough Q φ y space fees) ∧
      ∀ᶠ w:ℝ×(ℕ×ℕ) in trail.curry U,
        let M:=board R (s w.1) w.1 w.2.2
        Z.store.Meets Z.scheme M 6 ∧ Paid Z a x b B C D M:=by
  obtain ⟨B,C,D,hC,hD,field⟩:=WilsonPhysicalChiralPairReading.hearing Z a x b R hx o U prior s small
  obtain ⟨φ,hears,fees,income⟩:=WilsonPositionProgramReflectedPurse.original Q a x B y
  exact ⟨B,C,D,φ,fees,hC,hD,hears,income,field⟩
end YM.Integration.WilsonOriginalObservedRoseBornChiralPurse
