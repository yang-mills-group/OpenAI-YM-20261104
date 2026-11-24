import YM.Integration.WilsonIndependentConditionedLocatedPairPayment
import YM.Integration.WilsonReceivedChronologicalFixedRoseFittedBank

/-! A pair of the actual positioned columns before real placement and
before the Wilson fine cutoff. Bounded phases share the original purse;
the raw two-slot debt is one fixed power before the thermal order. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedLocatedPanelPurse
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonThermometerUnitFilingCoarse
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonThermometerReflectedTrajectory (anchorAt)
open WilsonReflectedPublicOrientedFaces (displayed)
open WilsonMovingForkMixedSeed WilsonAddressedFiniteGuardTrial WilsonPositionProgramReportedField
open WilsonMeasuredPublicEntrancePanel (Panel Reading charged)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonPositionProgramBlockedTrialAddBack (uncut)
open WilsonMeasuredPublicEntranceMasterUpper (ReadAt)
open WilsonMeasuredPublicEntranceScreen (Ground)
open PertExtension PertExtension.LatticePT
open MergeProof.Accent Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Carp
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReceivedCanonicalVersePosterior (word)
open WilsonThermometerDeclaredSeeds OriginalMarkedSourceComet
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(d:Fin 2→ℕ){N per f K u:ℕ}
local notation "C" => R.family
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "J" => Stock.census (Fin 2)
variable {requested power t:ℕ}{B:ℝ}{fk:f≤K}{cut:K≤N}

open Extraction WilsonAddressedPhysicalCells


open Motion WilsonOriginalObservedRoseCorrectedWords
open WilsonReceivedCanonicalVersePortfolio (wallet)
variable (A:Panel R d N per f K fk cut requested power t B)(file:Filed R d K)
  (station:A.slot=file.station)(axes:A.axis=file.A N per)
local notation "w" => votes R d (N:=N) (per:=per) file A.names A.turn


open WilsonIndependentConditionedLocatedPairPayment (ballot)
variable (phase:Fin 2→ℂ)
local notation "actual" => ballot R d K N per file.station (file.A N per) A.names
    (fun i=>(A.turn i).1) (fun i=>(A.turn i).2) phase

theorem fitted (i:Fin 2):actual i=phase i • w i:=by
  unfold ballot votes units doses
  rw [smul_smul]

include station axes in
theorem column (bounded:∀i,‖phase i‖≤1)(i:Fin 2):
    (R.family.labels.level (d i)).coeffSize (actual i)≤B*(H K)^power:=by
  have cap:=WilsonOriginalObservedRoseFittedPurse.column R d A file station axes i
  rw [fitted R d A file phase i]
  have scaled:((C).labels.level (d i)).coeffSize (phase i • w i)=
      ‖phase i‖*((C).labels.level (d i)).coeffSize (w i):=by
    simp only [Labels.Frame.coeffSize,Pi.smul_apply,norm_smul,Finset.mul_sum]
  rw [scaled]
  have pos:0≤((C).labels.level (d i)).coeffSize (w i):=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  exact (mul_le_mul_of_nonneg_right (bounded i) pos).trans (by simpa using cap)

theorem salaries (b:ℝ):∃M:ℝ,1≤M ∧ ∀{H':ℝ},1≤H' → ∀p:ℕ,∀S:Finset (Fin 2),
    wallet R d (fun _=>b*H'^p) S ≤ M*H'^(2*p):=by
  classical
  let M:=max 1 (∑S:Finset (Fin 2), |wallet R d (fun _=>b) S|)
  have one:1≤M:=le_max_left ..
  refine ⟨M,one,?_⟩
  intro H' large p S
  rw [WilsonReceivedChronologicalFixedRoseFittedBank.factor]
  have fee:wallet R d (fun _=>b) S≤M:=by
    calc
      _≤|wallet R d (fun _=>b) S|:=le_abs_self _
      _≤∑S:Finset (Fin 2),|wallet R d (fun _=>b) S|:=
        Finset.single_le_sum (f:=fun T:Finset (Fin 2)=>|wallet R d (fun _=>b) T|) (fun _ _=>abs_nonneg _) (Finset.mem_univ S)
      _≤M:=le_max_right ..
  have small:S.card≤2:=by simpa using Finset.card_le_card (Finset.subset_univ S)
  exact mul_le_mul fee (pow_le_pow_right₀ large (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left p small))
    (pow_nonneg (zero_le_one.trans large) _) (zero_le_one.trans one)

end YM.Integration.WilsonIndependentConditionedLocatedPanelPurse
end
