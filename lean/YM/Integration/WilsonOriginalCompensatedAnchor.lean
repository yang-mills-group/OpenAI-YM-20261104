import YM.Integration.WilsonPositionHomogeneousLeading

/-! The zero-order comparison on the physical homogeneous tower, including its signed test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompensatedAnchor
open Filter Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame
open scoped Topology ContDiff Classical

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    (lead : PhysMS.Leading F J) {Y : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ, ∀ᶠ r in Trace.Pilot.trail, PhysMS.Frame.obedient F Y (J r) d)

theorem near (d : ℕ) :
    Tendsto (fun t => guide G d (WilsonPositionHomogeneousNear.field Z d t)) (𝓝 0) (𝓝 0) :=
  WilsonPositionHomogeneousNear.near Z d

include lead paid in
theorem measured (hG : G.Simple) (V : Store G) (K : Rose.Pick V) :
    Tendsto (WilsonPositionThermometerReading.reading F (WilsonPositionPrescribedFrame.positioned F J V) K)
      Trace.Pilot.trail (𝓝 0) :=
  WilsonPositionPrescribedZero.measured F J V lead paid hG K

include lead paid in
theorem field (hG : G.Simple) (d : ℕ) (v : RG17.Free R.family d) :
    Tendsto (fun r => WilsonPositionPrescribedLift.field F J Z.store d r (change F J Z d r v))
      Trace.Pilot.trail (𝓝 v) :=
  WilsonPositionHomogeneousLeading.field F J Z lead paid hG d v

include lead paid in
theorem jets (hG : G.Simple) {n : ℕ} (d : Caps n) (v : (i : Fin n) → RG17.Free R.family (d i)) (l : ℕ)
    {K : Set (Points n)} (hk : IsCompact K) (hs : K ⊆ conf n) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ r in Trace.Pilot.trail, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ l (fun y => S.classMoment S d (r • y) (fun i => homogeneous F J Z r (d i) (v i))) x -
        iteratedFDeriv ℝ l (fun y => (Bel R.family.book).classMoment (Bel R.family.book) d y v) x‖ ≤ ε :=
  WilsonPositionHomogeneousLeading.jets F J Z lead paid hG d v l hk hs he

end YM.Integration.WilsonOriginalCompensatedAnchor
end

