import YM.Integration.WilsonAddressedPublicCrown
import YM.Integration.WilsonThermometerWeakPublication

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonAddressedPublicOriginalFaces
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {N p k : ℕ} {I : Type} [Fintype I] [DecidableEq I]
local notation "C₀" => R.family

theorem original (d : I → ℕ) (x : (i : I) → (C₀).label (d i))
    (V : (i : I) → Sight C₀ (d i) p) (u : (i : I) → Emblems C₀ (d i))
    (est : ∀i, Opened C₀ (d i) k p) (hk : k ≤ N)
    (raw : ∀i, Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) k N p (d i)
      (digits R N p 0) (V i) (u i)) (ref : ∀i e, e ≤ d i → (C₀).ref e ≤ N)
    (c : I → Site ((C₀).side k p)) (names : Census I) (t : ℕ) :
    let y := fun i => offer R (x i) (est i) hk
    let b := fun i => WilsonThermometerReflectedTrajectory.anchorAt R (c i) N
    let data := fun i => reduce (y i)
    WilsonThermometerReflectedRoster.filed R d (fun _ => 0) (fun _ => (1,false)) c data V u names hk t →
    ∀ j (hj : j ≤ N) (s : names.Mode) U,
      (WilsonThermometerReflectedRoster.density R d (fun _ => 0) (fun _ => (1,false)) c data u names hk hj U).part s =
      ((C₀).path.rep N p j).eval U • actualTransport C₀ (N:=N)
        (fun W => ∏ i∈s.val, ((charge (y i):ℝ):ℂ)⁻¹ * (C₀).O N p (x i) (b i) W) hj U := by
  intro y b data filed j hj s U
  let f := WilsonThermometerReflectedRoster.source R d (fun _ => 0) (fun _ => (1,false)) c data u hk
  let bank := (C₀).path.rep N p
  have bill := (filed N hk (le_refl _)).1
  simp only [WilsonThermometerReflectedRoster.density,gust_base] at bill
  rw [WilsonThermometerReflectedRoster.density,actualTransport_unnormalize C₀ R.makes (le_refl N)]
  have face := congr_fun (pushpart hj (Accent.birth names (bank N) f) s bill) U
  rw [face]
  have exactField (W) : ((Accent.birth names (bank N) f) W).part s = (bank N).eval W •
      (∏ i∈s.val, ((charge (y i):ℝ):ℂ)⁻¹ * (C₀).O N p (x i) (b i) W) := by
    unfold Accent.birth Accent.Mach
    rw [Poly.part_smul,pass_fire,Complex.real_smul]
    congr 1
    exact prod_congr rfl fun i _ => congrFun (WilsonAddressedPublicCrown.arm R d x V u est hk raw ref c i) W
  simp_rw [exactField];rfl

end YM.Integration.WilsonAddressedPublicOriginalFaces
end
