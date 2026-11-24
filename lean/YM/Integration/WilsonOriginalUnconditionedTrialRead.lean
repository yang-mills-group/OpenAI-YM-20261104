import YM.Integration.WilsonOriginalFittedLaplacianSupport
import YM.Integration.WilsonOriginalPublicTrialPhasePair

/-! The unrestricted ordinary fitted word on the inherited K law. Its
Bochner integrability and size are uniform on the entire fine position grid. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalUnconditionedTrialRead
open Finset Set Function MeasureTheory Lattice RG Wilson PhysicalNext.Repeat.Legato
open OPE.Therm
open WilsonOriginalMicroscopicGuardedTrial (unary raw)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceCellWords (submitted)
open WilsonOriginalMicroscopicGuardedWallet (loss)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3 → ℕ){N per f K requested power t:ℕ}{B:ℝ}{fk:f≤K}{cut:K≤N}
variable (A:Panel R d N per f K fk cut requested power t B)(file:Filed R d K)
variable (station:A.slot=file.station)(axes:A.axis=file.A N per)
variable (s:(Stock.census (Fin 3)).Mode)(sites:Fin 3 → Site (R.family.side K per))

def reading (z:Fin 3 → Site (R.family.side K per)):ℂ:=
  ∫U,submitted R d (N:=N) file (le_refl K) A.names A.turn z s U ∂scene R.family.path N per K

include station axes in
theorem original :
    Integrable (submitted R d (N:=N) file (le_refl K) A.names A.turn sites s) (scene R.family.path N per K) ∧
    ‖reading R d A file s sites‖≤∏i∈s.val,loss R (d i) K*(B*(R.family.path.levels.clock.hatBeta K)^power):=by
  letI : IsProbabilityMeasure (scene R.family.path N per K):= probability R.makes.wilson cut
  let w:=votes R d (N:=N) (per:=per) file A.names A.turn
  let z:=fun i:Fin 3=>(R.family.S.toDepth (le_refl K) per).embed (sites i)
  have m:Measurable (submitted R d (N:=N) file (le_refl K) A.names A.turn sites s):=by
    change Measurable (fun U=>∏i∈s.val,raw R d N per K z w i U)
    exact Finset.measurable_prod _ fun i _=>(unary R d N per K z w i).2.1
  have h:=WilsonCapturedPrimaryMasterGridGross.original R d A file station axes s sites
  exact ⟨Integrable.of_bound m.aestronglyMeasurable _ (Filter.Eventually.of_forall h),
    by simpa [reading] using norm_integral_le_of_norm_le_const (μ:=scene R.family.path N per K) (Filter.Eventually.of_forall h)⟩
end YM.Integration.WilsonOriginalUnconditionedTrialRead
