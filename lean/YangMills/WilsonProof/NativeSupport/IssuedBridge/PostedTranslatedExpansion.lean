import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedCompactCorrelationReceipt
import YM.Integration.WilsonOriginalTranslatedCorrelation
import YM.Integration.WilsonOriginalGlobalViewerShape

/-! The appointed correlation on the released joint tests. -/
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedTranslatedExpansion
open YM YM.Integration
open Filter Function Set Metric Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace Trace.Pilot PhysMS Climb GapsContact
open OPE.Orbits (Reader)
open OPE OPE.Orbits.Reader Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot WilsonViewerElectedHierarchy
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J : ℝ → PhysMS.tower S} {L : EveryPhase.Almanac F} {Y : (Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family} {ℓ : Ultrafilter (ℕ×ℕ)}
    {simple : G.Simple} {cohort : Ultrafilter (ℕ×ℕ) → Prop}
    (run : Selected.{u} F L Q J Y arch ℓ simple cohort) (Z : WilsonPrescription G)



open UnitAddTorus AddCircle
open WilsonOriginalFourierBoxIntegral (localize)
open WilsonOriginalFourierLattice (height)
open WilsonOriginalPhysicalBoxSlices (positions)

open scoped ContDiff
open MeasureTheory
open WilsonOriginalTestedFourierBank (Prices)
open WilsonOriginalIntegerModeCut (size size_pow)
open WilsonOriginalFourierBoxIntegral (test)

local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "pub" => homogeneous F J Z


open WilsonOriginalCompactPoseCover (Box)

theorem onConf {n m : ℕ} {meter : ℝ → ℝ} {old new : ℝ → YM.Points n → ℂ}
    {pred : ℕ → YM.Points n → ℂ} (paid : YangMills.Matching.HasExpansion m meter old pred)
    (filed : ∀ r, 0 < r → ∀ x ∈ conf n, old r x = new r x) :
    YangMills.Matching.HasExpansion m meter new pred := by
  refine ⟨paid.1,?_⟩
  intro K hk hc p ε he
  have pos : ∀ᶠ r : ℝ in trail, 0 < r := self_mem_nhdsWithin
  filter_upwards [paid.2 K hk hc p ε he,pos] with r bill hr φ hK norm
  have eq : (fun x => φ x * old r x) = fun x => φ x * new r x := by
    funext x
    by_cases h : φ x = 0
    · simp [h]
    · rw [filed r hr x (hc (hK (subset_tsupport _ h)))]
  exact eq ▸ bill φ hK norm
include run in
theorem original {n m : ℕ} (d : Fin n → ℕ) (v : MaxwellSlots R.family d)
    (clock : Coupling G θ) (coordinates : (Fin (m+1) → ℝ) ≃L[ℝ] YM.Points n)
    (coeff : ℕ → YM.Points n → ℂ) (smooth : ∀ k, ContDiffOn ℝ ∞ (coeff k) (conf n))
    (Dtest : Box n (m+1) → ℕ)
    (earned : WilsonOriginalGlobalViewerShape.Tested (F:=F) (J:=J) Z d v coeff Dtest)
    (who : Viewers F) (o : E4) :
    YangMills.Matching.HasExpansion 0 θ (fun r x => S.classMoment (spectator F who) d (points fun i => o + r • x i) (fun i => pub r (d i) (v i))) coeff :=
  onConf (PostedCompactCorrelationReceipt.original run Z d v clock coordinates coeff smooth Dtest earned who)
    fun r hr _ hx => (WilsonOriginalTranslatedCorrelation.original F who (pub r) d v r hr o hx).symm
end IssuedBridge.PostedTranslatedExpansion
