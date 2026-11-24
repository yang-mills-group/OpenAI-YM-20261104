import YM.Integration.WilsonCapturedPhysicalMSDatum
import YM.FVA2.Main

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6RawDressing
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl.Near MS.Rake MS.Land
open FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
variable {G : Gauge} (Z : WilsonPrescription G) {simple : G.Simple}
    {σ : Prescription (Press.portDeck G)} {dial : Bool}
    (matched : Main.Match Z simple (WilsonCapturedPhysicalMSDatum.original G) σ dial)
    (μ : ℝ) (h : ℕ)

theorem point {n : ℕ} (a : Sample n) (j : ℕ) (p : Tags G h n) :
    Dframe.postedPoint μ Z.scheme σ h a j p =
      Dframe.status (Dframe.D μ σ a.F h) (Dframe.orderT μ Z.scheme σ a h) j p := rfl

theorem smeared (m : XSpace.Mesh) (j n : ℕ) (test : Test n) (p : Tags G h n) :
    Reg.Pivot.posted μ Z.scheme σ h m j n test p =
      realm (Dframe.D μ σ m h)
        (Program.substitute (Dframe.reset μ σ m) (batch Z.scheme m h)) j n test p := rfl

include matched in
theorem physical (m : XSpace.Mesh) (even : Even m.p.side.val) {W : Type} [LinearOrder W]
    (s : Finset W) (d : W → Cover) (x : Cover) (η : ℝ) (u : W → Label (Press.portDeck G)) :
    PhysicalSum G σ.team η m.p.side true s d x
      (ApplyMF (Press.wickInput Z.scheme) (Stripped σ.team) σ u)
      (Change.convertSources (Change.Dictionary.paid u σ η) s.toList fun l =>
        Program.substitute (Program.shift σ.team η)
          (Slice.record (Birth.words Z.scheme m.p.side (l.map (Top.declares u x d))))) :=
  matched.exactAtCutoff m.p.side even s d x η u

def Paid (m : XSpace.Mesh) : Prop :=
  Reg.Pivot.Ready μ Z.scheme Z.store σ h m ∧
    Program.substitute (Dframe.reset μ σ m) (Z.store.opens Z.scheme m h) =
      realm (deck (Reg.Pivot.chalk μ Z.scheme Z.store σ h m)) (Reg.Pivot.posted μ Z.scheme σ h m) ∧
    PowerSeries.constantCoeff (Dframe.D μ σ m h) = 1 ∧
    (∀ (n j : ℕ) (test : Test n) (p : Tags G h n), type_of% (smeared Z (σ := σ) μ h m j n test p)) ∧
    ∀ (W : Type) [LinearOrder W] (even : Even m.p.side.val) (s : Finset W) (d : W → Cover)
      (x : Cover) (η : ℝ) (u : W → Label (Press.portDeck G)),
      type_of% (physical Z matched m even s d x η u)

include matched in
theorem original :
    (∀ {n : ℕ} (a : Sample n) (j : ℕ) (p : Tags G h n), type_of% (point Z (σ := σ) μ h a j p)) ∧
    type_of% (matched.positionCoupling μ) ∧ type_of% (matched.frame μ h) ∧
    type_of% (matched.eqconv μ h) ∧ type_of% (matched.transformedTest μ h) ∧
    (∀ᶠ m in Front, Paid Z (σ := σ) μ h m) ∧
    (∀ᶠ i in atTop, Paid Z (σ := σ) μ h (Z.run.step i)) := by
  have paid : ∀ᶠ m in Front, Paid Z (σ := σ) μ h m := by
    filter_upwards [matched.cancelsBare μ h] with m wages
    exact ⟨wages.1, wages.2, matched.D_initial μ h m, fun n j => smeared Z (σ := σ) μ h m j n,
      fun W _ even s d x η u => physical Z matched m even s d x η u⟩
  exact ⟨fun {_} => point Z (σ := σ) μ h, matched.positionCoupling μ, matched.frame μ h,
    matched.eqconv μ h, matched.transformedTest μ h, paid, matched.onSchedule.eventually paid⟩
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6RawDressing
end
