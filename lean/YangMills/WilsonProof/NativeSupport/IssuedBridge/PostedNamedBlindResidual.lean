import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNamedRawMoments
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedLastDegreeExclusion
noncomputable section
namespace IssuedBridge.PostedNamedBlindResidual
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




open MeasureTheory


local notation "GC" => _root_.IssuedMaxwell.GraphCoefficients.issued g
local notation "M₀" => WilsonCapturedPhysicalMSDatum.original g.core
local notation "μ₀" => Teller.logNu 1
open PostedScreenedReparametrization (screened)


def shortened (d k : ℕ) : Normalize.Guard g.core d :=
  Normalize.deck (Normalize.Screen.blind (Reg.State.root μ₀ Z.store M₀ d) (k+1))

theorem earlier (d k : ℕ) (j : Fin (k+1)) :
    PowerSeries.coeff j.val (shortened Z d k) = screened Z M₀ μ₀ d j.val := by
  change PowerSeries.coeff j.val (Normalize.deck _) = PowerSeries.coeff j.val (Normalize.deck _)
  simp only [Normalize.decked, Normalize.pulling, Normalize.Screen.blind_low _ _ _ j.isLt]

theorem missing (d k : ℕ) : PowerSeries.coeff (k+1) (shortened Z d k) = 0 := by
  rw [shortened, Normalize.pos_decked _ (Nat.succ_ne_zero k), Normalize.Screen.blind_at]
  rfl

theorem readings (n d k : ℕ) (v : Fin n → (maxwellReference g).sector d) (x : Stage n) :
    Dframe.status (shortened Z d k) (Equator.wave μ₀ M₀ d n x) (k+1) v =
    YangMills.MSbar.Position.momentThrough GC d (k+1) k (fun j => screened Z M₀ μ₀ d j.val) n v x.val := by
  rw [PostedFieldSubstitution.original]
  let F (ν : Fin n → Fin (k+2)) : ℂ := if (∑ i, (ν i).val) ≤ k+1 then
    Equator.wave μ₀ M₀ d n x ((k+1)-∑ i, (ν i).val)
      (fun i => (PowerSeries.coeff (ν i).val (shortened Z d k)) (v i)) else 0
  have gone (ν : Fin n → Fin (k+2)) (htop : ∃ i, (ν i).val = k+1) : F ν = 0 := by
    obtain ⟨i, hi⟩ := htop
    dsimp only [F]
    split_ifs
    · apply MultilinearMap.map_coord_zero (i:=i)
      simp only [hi, missing, LinearMap.zero_apply]
    · rfl
  change (∑ ν, F ν) = _
  rw [PostedLastDegreeExclusion.original F gone]
  unfold YangMills.MSbar.Position.momentThrough
  apply Finset.sum_congr rfl
  intro τ _
  simp only [F, Fin.val_castSucc, earlier, PostedNamedRawMoments.cofiled]
  rfl

theorem correction (d k : ℕ) :
    screened Z M₀ μ₀ d (k+1) = -(((Z.store.measure d).D
      (Normalize.realm (shortened Z d k) (Reg.State.kernel μ₀ M₀ d) (k+1))).val) := by
  have recurs := Normalize.Screen.bare_price (Z.store.measure d) (Reg.State.kernel μ₀ M₀ d)
    (Reg.State.root μ₀ Z.store M₀ d) (Nat.succ_ne_zero k)
    (Reg.State.success (d:=d) μ₀ Z.store M₀).2.1
  rw [Reg.State.baseK, Reg.State.freeT, Normalize.regular _ (Z.store.prepared d)] at recurs
  exact (Normalize.pos_decked _ (Nat.succ_ne_zero k)).trans (congrArg Subtype.val recurs)

theorem original (d k n : ℕ) (φ : YangMills.SeparatedTest n) (v : Fin n → (maxwellReference g).sector d) :
    YangMills.MSbar.Position.residualReport GC d k (fun j => screened Z M₀ μ₀ d j.val) n φ v =
    Normalize.realm (shortened Z d k) (Reg.State.kernel μ₀ M₀ d) (k+1) n φ v := by
  rw [← Reg.State.in_mem μ₀ M₀ φ v]
  apply YM.Test.apply_eq
  intro x hx
  exact (readings Z n d k v ⟨x,hx⟩).symm

end IssuedBridge.PostedNamedBlindResidual
end
