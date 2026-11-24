import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedObservedCompactExpansion
import YM.Integration.WilsonOriginalGlobalViewerShape

/-! The appointed correlation on the released joint tests. -/
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedCompactCorrelationReceipt
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

include run in
theorem original {n m : ℕ} (d : Fin n → ℕ) (v : MaxwellSlots R.family d)
    (clock : Coupling G θ) (coordinates : (Fin (m+1) → ℝ) ≃L[ℝ] YM.Points n)
    (coeff : ℕ → YM.Points n → ℂ) (smooth : ∀ k, ContDiffOn ℝ ∞ (coeff k) (conf n))
    (Dtest : Box n (m+1) → ℕ)
    (earned : WilsonOriginalGlobalViewerShape.Tested (F:=F) (J:=J) Z d v coeff Dtest)
    (who : Viewers F) :
    YangMills.Matching.HasExpansion 0 θ (fun r => measured F who (pub r) v r) coeff := by
  apply PostedObservedCompactExpansion.original
  · exact fun k => (smooth k).continuousOn
  · have pos : ∀ᶠ r : ℝ in trail, 0 < r := self_mem_nhdsWithin
    filter_upwards [pos] with r hr
    intro y hy
    have inc := (S.class_smooth _ (spectate F who).smooth (fun i=>⟨d i,pub r (d i) (v i)⟩)).continuousOn
    exact ((inc.continuousAt ((conf_open n).mem_nhds (Work.A05.smul_conf hr hy))).comp
      (continuousAt_id.const_smul r)).continuousWithinAt
  · intro K hk hc p ε eps
    have full := WilsonOriginalGlobalViewerShape.original run Z d v clock coordinates coeff smooth Dtest earned K hk hc p 0 eps
    filter_upwards [full,clock.positive] with r bill warm x hx
    simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,← map_sub,LinearIsometryEquiv.norm_map,abs_of_pos warm] using bill x hx who
end IssuedBridge.PostedCompactCorrelationReceipt
