import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedScreenedReparametrization
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedFieldSubstitution
noncomputable section
namespace IssuedBridge.PostedScreenedReports
open YangMills YangMills.Wilson
open YM YM.Integration YM.Spec YM.OPE YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free
open WilsonOneFrameMixedMaxwell WilsonPositionHomogeneousFrame
open Climb Lattice RG PhysMS Trace.Pilot Next.Extract PhysicalNext.Repeat.Legato RG17 XSpace XSpace.Normalize FVA2 FVA2.Register
open FixedFields
open Function Filter Set
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {R : Run g.core}
variable {simple : g.core.Simple} (Z : WilsonPrescription g.core)
open MS MS.Land MS.Fleet FVA2.Scale WilsonViewerReportingGrid WilsonThermometerWeakMeasuredSeries
open WilsonViewerGridPins WilsonViewerAlignedResidual WilsonViewerElectedHierarchy
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonLimitConstruction
open PostedMeasuredCompactCorrelation (leaves)
variable (raw : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core)))
variable {σ : Prescription (Press.portDeck g.core)} {dial : Bool} (matched : Main.Match Z simple raw σ dial)

open YM.FVA2.Scale YM.MS YM.MS.Fleet YM.MS.Land YangMills.Matching

open YangMills.MSbar
local notation "B" => maxwellReference g
local notation "W" => PostedPositionConversion.filed Z raw matched



open PostedScreenedReparametrization (screened)

theorem ground (μ : ℝ) (d : ℕ) : screened Z raw μ d 0 = LinearMap.id := by
  change PowerSeries.coeff 0 (Reg.State.chooseL μ Z.store raw d) = 1
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, Reg.State.baseL]

private theorem included (μ : ℝ) {d e : ℕ} (h : d ≤ e) (k : ℕ)
    (p : (maxwellReference g).sector d) (q : (maxwellReference g).sector e) (same : p.val = q.val) :
    (screened Z raw μ d k p).val = (screened Z raw μ e k q).val := by
  have placed : up h p = q := Subtype.ext same
  have he := Reg.State.chainL μ Z.store raw (k:=k) h p
  rw [placed] at he
  exact (congrArg (fun u : (maxwellReference g).sector e => u.val) he).symm

theorem nested (μ : ℝ) (d e k : ℕ) (p : (maxwellReference g).sector d) (q : (maxwellReference g).sector e)
    (same : p.val = q.val) :
    (screened Z raw μ d k p).val = (screened Z raw μ e k q).val := by
  rcases le_total d e with h | h
  · exact included Z raw μ h k p q same
  · exact (included Z raw μ h k q p same.symm).symm

theorem opened (μ : ℝ) (n d k : ℕ) (x : Stage n) (v : Fin n → (maxwellReference g).sector d) :
    Reg.State.wall μ Z.store raw d x.val k v =
      ∑ ν : Fin n → Fin (k+1),
        if (∑ i, (ν i).val) ≤ k then
          Equator.wave μ raw d n x (k-∑ i, (ν i).val)
            (fun i => screened Z raw μ d (ν i).val (v i)) else 0 := by
  exact PostedFieldSubstitution.original _ _ _ _

theorem normalized (μ : ℝ) (d k : ℕ) :
    (Z.store.measure d).D (Reg.State.author μ Z.store raw d k) =
      if k = 0 then (Z.store.measure d).D (Normalize.reference g.core d) else 0 := by
  exact (Reg.State.success (d:=d) μ Z.store raw).2.1 k


theorem original (μ : ℝ) :
    (∀ d, screened Z raw μ d 0 = LinearMap.id) ∧
    (∀ d e k (p : (maxwellReference g).sector d) (q : (maxwellReference g).sector e),
      p.val = q.val → (screened Z raw μ d k p).val = (screened Z raw μ e k q).val) ∧
    (∀ (n d k : ℕ) (x : Stage n) (v : Fin n → (maxwellReference g).sector d),
      Reg.State.wall μ Z.store raw d x.val k v = ∑ ν : Fin n → Fin (k+1),
        if (∑ i, (ν i).val) ≤ k then Equator.wave μ raw d n x (k-∑ i, (ν i).val)
          (fun i => screened Z raw μ d (ν i).val (v i)) else 0) ∧
    (∀ d k, (Z.store.measure d).D (Reg.State.author μ Z.store raw d k) =
      if k = 0 then (Z.store.measure d).D (Normalize.reference g.core d) else 0) :=
  ⟨ground Z raw μ, nested Z raw μ, opened Z raw μ, normalized Z raw μ⟩

end IssuedBridge.PostedScreenedReports
end

